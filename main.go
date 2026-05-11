package main

// ---------------------------------------------------------------------------
// Key derivation — PBKDF2-SHA512 (stdlib only, no external deps)
// ---------------------------------------------------------------------------
// We implement PBKDF2 inline because golang.org/x/crypto is unavailable
// in this environment. This is the exact RFC 2898 / NIST SP 800-132 algorithm.

import (
	"bufio"
	"crypto/aes"
	"crypto/cipher"
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha512"
	"encoding/hex"
	"fmt"
	"io"
	"log/slog"
	"math"
	"os"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
	"unicode/utf8"
	"unsafe"
)

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

type Column struct {
	Name         string
	Type         string
	AutoIter     bool   // AUTOITER     — auto-incrementing integer (INT)
	AutoUUID     bool   // AUTOUUID     — auto-generated UUID v4 (UUID type)
	AutoTS       bool   // AUTOTS       — set to NOW() on INSERT, immutable (TIMESTAMP/DATE)
	AutoTSUpdate bool   // AUTOTS UPDATE — also refreshed on UPDATE
	Secure       bool   // SECURE       — AES-256-GCM encrypted at rest
	NotNull      bool   // NOT NULL     — rejects NULL / empty values
	Unique       bool   // UNIQUE       — enforces uniqueness across rows
	Default      string // DEFAULT <value>  (NOW() supported for DATE/TIMESTAMP)
}

type Table struct {
	mu           sync.RWMutex // protects Columns, Rows, AutoCounters
	Columns      []Column
	Rows         [][]string
	AutoCounters map[string]int
}

// dbMu protects the database map itself (adding/removing tables).
// For row-level operations, each Table.mu is used directly.
var dbMu sync.RWMutex

// lockFD is the file descriptor held open for flock() on the db file.
// -1 means no lock is held.
var lockFD = -1

// logger is the structured slog logger. Writes to stderr at WARN+ by default;
// use \loglevel debug|info|warn|error inside the REPL to change.
var logger *slog.Logger
var logLevel = new(slog.LevelVar) // default WARN

// slowQueryThresholdMs: queries slower than this are logged at WARN.
var slowQueryThresholdMs = 100

// deep-copy a Table for transaction snapshots (mutex is not copied)
func cloneTable(t *Table) *Table {
	t.mu.RLock()
	defer t.mu.RUnlock()
	cols := make([]Column, len(t.Columns))
	copy(cols, t.Columns)
	rows := make([][]string, len(t.Rows))
	for i, r := range t.Rows {
		rc := make([]string, len(r))
		copy(rc, r)
		rows[i] = rc
	}
	counters := make(map[string]int, len(t.AutoCounters))
	for k, v := range t.AutoCounters {
		counters[k] = v
	}
	return &Table{Columns: cols, Rows: rows, AutoCounters: counters}
}

var database = map[string]*Table{}

// transaction state: non-nil when inside BEGIN … COMMIT/ROLLBACK
var txSnapshot map[string]*Table

// dbFile / keyFile are set by parseArgs() or \connect before anything loads.
// Empty string means "no database selected yet" — nothing is auto-loaded.
var dbFile = ""
var keyFile = ""

const nullSentinel = "NULL"
const version = "1.5.0"

var validTypes = map[string]bool{
	"INT": true, "BIGINT": true, "FLOAT": true, "DOUBLE": true,
	"TEXT": true, "VARCHAR": true, "CHAR": true, "BOOL": true,
	"DATE": true, "TIMESTAMP": true, "BLOB": true, "UUID": true,
}

// ---------------------------------------------------------------------------
// Password prompt (no echo, pure syscall)
// ---------------------------------------------------------------------------

// stdinReader is the shared buffered reader for all stdin consumption.
// It must be used everywhere we read from stdin so bytes aren't lost.
var stdinReader = bufio.NewReader(os.Stdin)

func readPassword(prompt string) (string, error) {
	fmt.Print(prompt)
	// Try to disable echo via termios
	var oldState syscall.Termios
	fd := uintptr(syscall.Stdin)
	_, _, errno := syscall.Syscall6(syscall.SYS_IOCTL, fd,
		syscall.TCGETS, uintptr(unsafe.Pointer(&oldState)), 0, 0, 0)
	isTTY := errno == 0
	if isTTY {
		newState := oldState
		newState.Lflag &^= syscall.ECHO
		syscall.Syscall6(syscall.SYS_IOCTL, fd,
			syscall.TCSETS, uintptr(unsafe.Pointer(&newState)), 0, 0, 0)
		defer syscall.Syscall6(syscall.SYS_IOCTL, fd,
			syscall.TCSETS, uintptr(unsafe.Pointer(&oldState)), 0, 0, 0)
	}
	line, _ := stdinReader.ReadString('\n')
	if isTTY {
		fmt.Println() // echo the newline that was suppressed
	}
	return strings.TrimRight(line, "\r\n"), nil
}

// ---------------------------------------------------------------------------
// Key derivation — PBKDF2-SHA512 (inline, no external deps)
// RFC 2898 §5.2 with HMAC-SHA512, 200 000 iterations → 32-byte key
// ---------------------------------------------------------------------------

const pbkdf2Iters = 200_000

func pbkdf2Key(password, salt []byte, iter, keyLen int) []byte {
	prf := func(data []byte) []byte {
		h := hmac.New(sha512.New, password)
		h.Write(data)
		return h.Sum(nil)
	}
	hLen := sha512.Size
	blocks := (keyLen + hLen - 1) / hLen
	out := make([]byte, 0, blocks*hLen)

	buf := make([]byte, len(salt)+4)
	copy(buf, salt)

	for block := 1; block <= blocks; block++ {
		buf[len(salt)] = byte(block >> 24)
		buf[len(salt)+1] = byte(block >> 16)
		buf[len(salt)+2] = byte(block >> 8)
		buf[len(salt)+3] = byte(block)

		u := prf(buf)
		xored := make([]byte, len(u))
		copy(xored, u)
		for i := 1; i < iter; i++ {
			u = prf(u)
			for j := range xored {
				xored[j] ^= u[j]
			}
		}
		out = append(out, xored...)
	}
	return out[:keyLen]
}

// ---------------------------------------------------------------------------
// Encryption — AES-256-GCM  (key derived per-session from master password)
// ---------------------------------------------------------------------------

var encKey []byte // 32-byte session key, derived from master password

const keyFileMagic = "MINISQL-KDF-V1"

// loadOrCreateKey prompts for the master password and derives encKey.
// Key file stores: magic | salt(32B hex) | verifier HMAC(32B hex)
// The raw password is never stored anywhere.
func loadOrCreateKey() {
	data, err := os.ReadFile(keyFile)
	if err == nil {
		lines := strings.Split(strings.TrimSpace(string(data)), "\n")
		if len(lines) >= 3 && lines[0] == keyFileMagic {
			salt, e1 := hex.DecodeString(lines[1])
			storedVerifier, e2 := hex.DecodeString(lines[2])
			if e1 == nil && e2 == nil && len(salt) == 32 {
				for attempts := 0; attempts < 3; attempts++ {
					pw, _ := readPassword(fmt.Sprintf("Password for %s: ", dbFile))
					derived := pbkdf2Key([]byte(pw), salt, pbkdf2Iters, 32)
					verifier := computeVerifier(derived)
					if hmac.Equal(verifier, storedVerifier) {
						encKey = derived
						return
					}
					fmt.Println("Wrong password.")
				}
				fatalf("too many wrong password attempts")
			}
		}
		fmt.Println("Warning: key file corrupted, creating new database key.")
	}

	fmt.Printf("New database: %s\n", dbFile)
	fmt.Println("Set a master password. It will be required every time this database is opened.")
	for {
		pw, _ := readPassword("New password: ")
		if len(pw) < 4 {
			fmt.Println("Password must be at least 4 characters.")
			continue
		}
		pw2, _ := readPassword("Confirm password: ")
		if pw != pw2 {
			fmt.Println("Passwords do not match.")
			continue
		}

		salt := make([]byte, 32)
		if _, err := io.ReadFull(rand.Reader, salt); err != nil {
			fatalf("cannot generate salt: %v", err)
		}
		encKey = pbkdf2Key([]byte(pw), salt, pbkdf2Iters, 32)
		verifier := computeVerifier(encKey)

		content := keyFileMagic + "\n" +
			hex.EncodeToString(salt) + "\n" +
			hex.EncodeToString(verifier) + "\n"
		if err := os.WriteFile(keyFile, []byte(content), 0600); err != nil {
			fatalf("cannot write key file: %v", err)
		}
		fmt.Printf("Password set. Key file: %s\n", keyFile)
		fmt.Println("(The key file holds the KDF salt — back it up alongside your database.)")
		return
	}
}

// computeVerifier returns HMAC-SHA512(key, "minisql-verify")[:32]
// Used to check password correctness without storing the password.
func computeVerifier(key []byte) []byte { return computeVerifierFrom(key) }
func computeVerifierFrom(key []byte) []byte {
	h := hmac.New(sha512.New, key)
	h.Write([]byte("minisql-verify-v1"))
	return h.Sum(nil)[:32]
}

func encryptValue(plaintext string) (string, error) {
	return aesGCMEncrypt([]byte(plaintext))
}

func decryptValue(hexct string) (string, error) {
	pt, err := aesGCMDecrypt(hexct)
	return string(pt), err
}

// aesGCMEncrypt encrypts plaintext with AES-256-GCM and returns hex ciphertext.
func aesGCMEncrypt(plaintext []byte) (string, error) {
	block, err := aes.NewCipher(encKey)
	if err != nil {
		return "", err
	}
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return "", err
	}
	nonce := make([]byte, gcm.NonceSize())
	if _, err := io.ReadFull(rand.Reader, nonce); err != nil {
		return "", err
	}
	ct := gcm.Seal(nonce, nonce, plaintext, nil)
	return hex.EncodeToString(ct), nil
}

// aesGCMDecrypt decrypts a hex AES-256-GCM ciphertext.
func aesGCMDecrypt(hexct string) ([]byte, error) {
	ct, err := hex.DecodeString(hexct)
	if err != nil {
		return nil, err
	}
	block, err := aes.NewCipher(encKey)
	if err != nil {
		return nil, err
	}
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return nil, err
	}
	ns := gcm.NonceSize()
	if len(ct) < ns {
		return nil, fmt.Errorf("ciphertext too short")
	}
	return gcm.Open(nil, ct[:ns], ct[ns:], nil)
}

// ---------------------------------------------------------------------------
// HMAC-SHA512 file integrity
// ---------------------------------------------------------------------------

const hmacMarker = "HMAC:"

// signContent returns HMAC-SHA512(encKey, content) as a hex string.
func signContent(content []byte) string {
	h := hmac.New(sha512.New, encKey)
	h.Write(content)
	return hex.EncodeToString(h.Sum(nil))
}

// verifyAndStrip checks the HMAC trailer on a db file and returns the body.
func verifyAndStrip(data []byte) ([]byte, error) {
	s := string(data)
	lastNL := strings.LastIndex(strings.TrimRight(s, "\n"), "\n")
	if lastNL == -1 {
		return nil, fmt.Errorf("missing HMAC trailer")
	}
	lastLine := strings.TrimSpace(s[lastNL+1:])
	if !strings.HasPrefix(lastLine, hmacMarker) {
		return nil, fmt.Errorf("missing HMAC trailer (file may be tampered)")
	}
	storedMAC, err := hex.DecodeString(lastLine[len(hmacMarker):])
	if err != nil {
		return nil, fmt.Errorf("invalid HMAC trailer")
	}
	body := data[:lastNL+1]
	h := hmac.New(sha512.New, encKey)
	h.Write(body)
	if !hmac.Equal(h.Sum(nil), storedMAC) {
		return nil, fmt.Errorf("HMAC mismatch — file tampered or wrong password")
	}
	return body, nil
}

// ---------------------------------------------------------------------------
// Type validation
// ---------------------------------------------------------------------------

var dateRE = regexp.MustCompile(`^\d{4}-\d{2}-\d{2}$`)
var tsRE = regexp.MustCompile(`^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}$`)
var hexRE = regexp.MustCompile(`^[0-9a-fA-F]*$`)

func validateType(col Column, val string) error {
	switch col.Type {
	case "INT", "BIGINT":
		if _, err := strconv.ParseInt(val, 10, 64); err != nil {
			return fmt.Errorf("column '%s' expects %s, got '%s'", col.Name, col.Type, val)
		}
	case "FLOAT":
		if _, err := strconv.ParseFloat(val, 32); err != nil {
			return fmt.Errorf("column '%s' expects FLOAT, got '%s'", col.Name, val)
		}
	case "DOUBLE":
		if _, err := strconv.ParseFloat(val, 64); err != nil {
			return fmt.Errorf("column '%s' expects DOUBLE, got '%s'", col.Name, val)
		}
	case "CHAR":
		if utf8.RuneCountInString(val) != 1 {
			return fmt.Errorf("column '%s' expects exactly 1 character, got '%s'", col.Name, val)
		}
	case "BOOL":
		switch strings.ToLower(val) {
		case "true", "false", "1", "0", "yes", "no":
		default:
			return fmt.Errorf("column '%s' expects BOOL (true/false/1/0/yes/no), got '%s'", col.Name, val)
		}
	case "DATE":
		if !dateRE.MatchString(val) {
			return fmt.Errorf("column '%s' expects DATE (YYYY-MM-DD), got '%s'", col.Name, val)
		}
		if _, err := time.Parse("2006-01-02", val); err != nil {
			return fmt.Errorf("column '%s' invalid date '%s'", col.Name, val)
		}
	case "TIMESTAMP":
		if !tsRE.MatchString(val) {
			return fmt.Errorf("column '%s' expects TIMESTAMP (YYYY-MM-DD HH:MM:SS), got '%s'", col.Name, val)
		}
		if _, err := time.Parse("2006-01-02 15:04:05", val); err != nil {
			return fmt.Errorf("column '%s' invalid timestamp '%s'", col.Name, val)
		}
	case "BLOB":
		if !hexRE.MatchString(val) || len(val)%2 != 0 {
			return fmt.Errorf("column '%s' expects BLOB as even-length hex string, got '%s'", col.Name, val)
		}
	case "UUID":
		if !uuidRE.MatchString(val) {
			return fmt.Errorf("column '%s' expects UUID (xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx), got '%s'", col.Name, val)
		}
	}
	return nil
}

// ---------------------------------------------------------------------------
// UUID v4 generation — crypto/rand, no external deps
// ---------------------------------------------------------------------------

func generateUUID() string {
	var b [16]byte
	if _, err := io.ReadFull(rand.Reader, b[:]); err != nil {
		fatalf("cannot generate UUID: %v", err)
	}
	// Set version 4 and variant bits (RFC 4122)
	b[6] = (b[6] & 0x0f) | 0x40
	b[8] = (b[8] & 0x3f) | 0x80
	return fmt.Sprintf("%08x-%04x-%04x-%04x-%012x",
		b[0:4], b[4:6], b[6:8], b[8:10], b[10:16])
}

// uuidRE validates UUID v4 format.
var uuidRE = regexp.MustCompile(`(?i)^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$`)

// nowForCol returns the current time formatted for the column's type.
func nowForCol(col Column) string {
	now := time.Now()
	if col.Type == "DATE" {
		return now.Format("2006-01-02")
	}
	return now.Format("2006-01-02 15:04:05")
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

func fatalf(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "Fatal: "+format+"\n", args...)
	os.Exit(1)
}

// ---------------------------------------------------------------------------
// Structured logging (log/slog)
// ---------------------------------------------------------------------------

func initLogger() {
	logLevel.Set(slog.LevelWarn) // default: only warn+error
	h := slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: logLevel})
	logger = slog.New(h)
}

func logQuery(op, detail string, dur time.Duration, rowsAffected int) {
	ms := dur.Milliseconds()
	attrs := []any{
		slog.String("op", op),
		slog.String("db", dbFile),
		slog.Int64("ms", ms),
		slog.Int("rows", rowsAffected),
	}
	if detail != "" {
		attrs = append(attrs, slog.String("detail", detail))
	}
	if ms >= int64(slowQueryThresholdMs) {
		logger.Warn("slow query", attrs...)
	} else {
		logger.Info("query", attrs...)
	}
}

// ---------------------------------------------------------------------------
// OS file locking (flock) — prevents two processes opening the same db
// ---------------------------------------------------------------------------

func acquireFileLock(path string) {
	f, err := os.OpenFile(path+".lock", os.O_CREATE|os.O_RDWR, 0600)
	if err != nil {
		// Non-fatal: lock file couldn't be created (read-only fs, etc.)
		logger.Warn("cannot create lock file", slog.String("path", path+".lock"), slog.Any("err", err))
		return
	}
	// LOCK_EX | LOCK_NB: exclusive, non-blocking
	err = syscall.Flock(int(f.Fd()), syscall.LOCK_EX|syscall.LOCK_NB)
	if err != nil {
		f.Close()
		fatalf("database '%s' is already open by another process.\nIf this is wrong, delete %s.lock", path, path)
	}
	lockFD = int(f.Fd())
}

func releaseFileLock() {
	if lockFD != -1 {
		syscall.Flock(lockFD, syscall.LOCK_UN)
		syscall.Close(lockFD)
		lockFD = -1
	}
}

// ---------------------------------------------------------------------------
// Key rotation — ALTER DATABASE SET PASSWORD
// ---------------------------------------------------------------------------

// rotateKey re-derives the encryption key from a new password and re-encrypts
// all SECURE column values and all row blobs. Uses atomic save at the end.
func rotateKey() {
	if dbFile == "" || encKey == nil {
		fmt.Println("No database open.")
		return
	}
	fmt.Println("Key rotation: all row data will be re-encrypted with the new password.")
	pw, _ := readPassword("New password: ")
	if len(pw) < 4 {
		fmt.Println("Password too short (min 4 chars). Aborted.")
		return
	}
	pw2, _ := readPassword("Confirm new password: ")
	if pw != pw2 {
		fmt.Println("Passwords do not match. Aborted.")
		return
	}

	// Decrypt all SECURE column values with the old key first
	dbMu.Lock()
	defer dbMu.Unlock()
	type cellAddr struct{ table, row, col int }
	type cellVal struct {
		addr cellAddr
		plain string
	}
	var plains []cellVal
	for _, t := range database {
		t.mu.Lock()
		for ri, row := range t.Rows {
			for ci, col := range t.Columns {
				if col.Secure && row[ci] != nullSentinel {
					plain, err := decryptValue(row[ci])
					if err != nil {
						t.mu.Unlock()
						fmt.Printf("Error decrypting during rotation: %v\n", err)
						return
					}
					_ = plain // we'll re-encrypt below after key swap
					plains = append(plains, cellVal{cellAddr{0, ri, ci}, plain})
				}
			}
		}
		t.mu.Unlock()
	}

	// Derive new key
	salt := make([]byte, 32)
	if _, err := io.ReadFull(rand.Reader, salt); err != nil {
		fmt.Println("Error generating salt:", err)
		return
	}
	newKey := pbkdf2Key([]byte(pw), salt, pbkdf2Iters, 32)

	// Write new key file
	verifier := computeVerifierFrom(newKey)
	content := keyFileMagic + "\n" +
		hex.EncodeToString(salt) + "\n" +
		hex.EncodeToString(verifier) + "\n"
	if err := os.WriteFile(keyFile, []byte(content), 0600); err != nil {
		fmt.Println("Error writing key file:", err)
		return
	}

	// Swap key in memory
	oldKey := encKey
	encKey = newKey

	// Re-encrypt all SECURE cells with new key
	tableList := make([]*Table, 0, len(database))
	for _, t := range database {
		tableList = append(tableList, t)
	}
	for i, t := range tableList {
		t.mu.Lock()
		for ri, row := range t.Rows {
			for ci, col := range t.Columns {
				if col.Secure && row[ci] != nullSentinel {
					// Decrypt with old key
					encKey = oldKey
					plain, err := decryptValue(row[ci])
					if err != nil {
						encKey = newKey
						t.mu.Unlock()
						fmt.Printf("Error during re-encryption (table %d row %d col %d): %v\n", i, ri, ci, err)
						return
					}
					// Re-encrypt with new key
					encKey = newKey
					ct, err := encryptValue(plain)
					if err != nil {
						t.mu.Unlock()
						fmt.Println("Error re-encrypting:", err)
						return
					}
					row[ci] = ct
				}
			}
		}
		t.mu.Unlock()
	}

	saveDB(dbFile)
	fmt.Println("Key rotation complete. All data re-encrypted with new password.")
}

func printBanner() {
	fmt.Printf("MiniSQL v%s  —  type HELP for commands, EXIT to quit\n", version)
	fmt.Println(strings.Repeat("─", 60))
}

func printHelp() {
	fmt.Println(`
Commands
────────────────────────────────────────────────────────────
DDL
  CREATE TABLE [IF NOT EXISTS] <name> (col TYPE [mods...], ...)
  ALTER TABLE <name> ADD COLUMN <col> <TYPE> [mods...]
  ALTER TABLE <name> DROP COLUMN <col>
  ALTER TABLE <name> RENAME COLUMN <old> TO <new>
  ALTER TABLE <name> RENAME TO <newname>
  DROP TABLE [IF EXISTS] <name>
  TRUNCATE TABLE <name>

DML
  INSERT INTO <table> [(col,...)] VALUES (v1, v2, ...)
  SELECT [*|col,...|AGG(col)] FROM <table>
         [WHERE cond [AND cond ...]]
         [ORDER BY col [ASC|DESC]] [LIMIT n]
  UPDATE <table> SET col=val [, ...] [WHERE ...]
  DELETE FROM <table> WHERE cond [AND cond ...]

Transactions
  BEGIN
  COMMIT
  ROLLBACK

Meta
  SHOW TABLES
  DESCRIBE <table>             (alias: \d <table>)
  \dt                          list tables (short)
  \i  <file>                   load & execute an .msql script
  \connect <file.msql>         save current db, open another (\c also works)
  \status                      show current database file and stats
  HELP                         this message
  EXIT

  \loglevel debug|info|warn|error  set log verbosity (default: warn)
  EXPLAIN SELECT ...               show query plan without executing
  ALTER DATABASE SET PASSWORD      re-encrypt database with new master password
  -db <file.msql>              database file to open (default: db.msql)
                               each db gets its own password + key file
  -exec "SQL"                  run one statement non-interactively then exit
  script.msql                  positional arg: execute script then exit

Types:     INT  BIGINT  FLOAT  DOUBLE  TEXT  VARCHAR  CHAR
           BOOL  DATE  TIMESTAMP  UUID  BLOB

Modifiers: AUTOITER            auto-increment integer (INT)
           AUTOUUID            auto-generate UUID v4 (UUID)
           AUTOTS              set to current timestamp on INSERT (immutable)
           AUTOTS UPDATE       set on INSERT, refresh on UPDATE
           SECURE              AES-256-GCM encrypted at rest
           NOT NULL            reject NULL / empty
           UNIQUE              enforce uniqueness
           DEFAULT <val>       fallback value (NOW(), UUID() also accepted)

Aggregates (SELECT): COUNT(*)  SUM(col)  AVG(col)  MIN(col)  MAX(col)

WHERE: =  !=  <  >  <=  >=  LIKE (% wildcard)  AND
Timestamps must be quoted: '2024-01-15 12:30:00'
────────────────────────────────────────────────────────────`)
}

// ---------------------------------------------------------------------------
// Arg parsing
// ---------------------------------------------------------------------------

// parseArgs handles:
//   minisql                           → interactive, no db pre-loaded
//   minisql -db <path>                → interactive, open <path>
//   minisql -db <path> <script.sql>   → execute script against <path>, exit
//   minisql -db <path> -exec "SQL"    → execute one statement, exit

func parseArgs() (scriptFile, execStmt string) {
	args := os.Args[1:]
	for i := 0; i < len(args); i++ {
		switch args[i] {
		case "-db", "--db":
			if i+1 >= len(args) {
				fatalf("-db requires a file path\nUsage: minisql [-db <file.msql>] [script.sql]")
			}
			i++
			setDB(args[i])
		case "-exec", "--exec":
			if i+1 >= len(args) {
				fatalf("-exec requires a SQL string")
			}
			i++
			execStmt = args[i]
		case "-help", "--help", "-h":
			fmt.Fprintln(os.Stderr, "Usage: minisql [-db <file.msql>] [script.sql]")
			fmt.Fprintln(os.Stderr, "")
			fmt.Fprintln(os.Stderr, "  -db <file>   database to open (each db has its own password + key file)")
			fmt.Fprintln(os.Stderr, "  script.sql   SQL script to execute then exit (requires -db)")
			fmt.Fprintln(os.Stderr, "  -exec \"SQL\"  run one statement then exit (requires -db)")
			fmt.Fprintln(os.Stderr, "")
			fmt.Fprintln(os.Stderr, "Without -db, starts with no database loaded.")
			fmt.Fprintln(os.Stderr, "Use \\connect <file.msql> inside the REPL to open or create one.")
			os.Exit(0)
		default:
			if strings.HasPrefix(args[i], "-") {
				fatalf("unknown flag %q\nUsage: minisql [-db <file.msql>] [script.sql]", args[i])
			}
			scriptFile = args[i]
		}
	}
	return
}

// setDB updates dbFile and derives keyFile from it.
func setDB(path string) {
	dbFile = path
	keyFile = path + ".key"
}

// ---------------------------------------------------------------------------
// \connect — open a database file (also used internally)
// ---------------------------------------------------------------------------

func connectDB(path string) {
	if dbFile != "" && len(database) > 0 {
		saveDB(dbFile)
	}
	releaseFileLock() // release old lock before acquiring new one

	for k := range database {
		delete(database, k)
	}
	txSnapshot = nil

	setDB(path)
	acquireFileLock(dbFile)
	loadOrCreateKey()
	loadDB(dbFile)
	fmt.Printf("Connected to %s\n", dbFile)
}

// ---------------------------------------------------------------------------
// EXIT save — prompt for path when no db file was chosen
// ---------------------------------------------------------------------------

func exitSave(scanner *bufio.Scanner) {
	if len(database) == 0 {
		// Nothing to save
		return
	}
	if dbFile != "" {
		saveDB(dbFile)
		return
	}
	// No file selected — ask the user
	fmt.Print("No database file set. Save to file? (leave blank to discard): ")
	if !scanner.Scan() {
		return
	}
	path := strings.TrimSuffix(strings.TrimSpace(scanner.Text()), ";")
	if path == "" {
		fmt.Println("Changes discarded.")
		return
	}
	setDB(path)
	// Need a key to encrypt — derive one now
	loadOrCreateKey()
	saveDB(dbFile)
}

func main() {
	initLogger()
	scriptFile, execStmt := parseArgs()

	if (scriptFile != "" || execStmt != "") && dbFile == "" {
		fatalf("non-interactive modes require -db <file>\nExample: minisql -db mydata.msql script.sql")
	}

	if dbFile != "" {
		acquireFileLock(dbFile)
		defer releaseFileLock()
		loadOrCreateKey()
		loadDB(dbFile)
	}

	if execStmt != "" {
		execute(strings.TrimSuffix(strings.TrimSpace(execStmt), ";"))
		saveDB(dbFile)
		return
	}
	if scriptFile != "" {
		runFile(scriptFile)
		saveDB(dbFile)
		return
	}

	// Interactive REPL
	printBanner()
	if dbFile == "" {
		fmt.Println("No database loaded. Use \\connect <file.msql> to open or create one.")
		fmt.Println("Type HELP for all commands.")
	}

	scanner := bufio.NewScanner(stdinReader)
	var buf strings.Builder

	for {
		if buf.Len() == 0 {
			if dbFile == "" {
				fmt.Print("sql(no db)> ")
			} else if txSnapshot != nil {
				fmt.Printf("sql(%s)(txn)> ", dbFile)
			} else {
				fmt.Printf("sql(%s)> ", dbFile)
			}
		} else {
			fmt.Print("  -> ")
		}
		if !scanner.Scan() {
			break
		}
		line := strings.TrimSpace(scanner.Text())

		if line == "" || strings.HasPrefix(line, "--") {
			continue
		}

		if strings.HasPrefix(line, `\`) {
			handleMeta(line)
			continue
		}

		if buf.Len() > 0 {
			buf.WriteByte(' ')
		}
		buf.WriteString(line)

		full := strings.TrimSpace(buf.String())
		upper := strings.ToUpper(full)
		singleWord := !strings.Contains(full, " ")

		if strings.HasSuffix(full, ";") || singleWord ||
			upper == "EXIT" || upper == "HELP" || upper == "SHOW TABLES" ||
			upper == "BEGIN" || upper == "COMMIT" || upper == "ROLLBACK" {
			buf.Reset()
			stmt := strings.TrimSuffix(full, ";")
			stmt = strings.TrimSpace(stmt)
			if strings.ToUpper(stmt) == "EXIT" {
				exitSave(scanner)
				fmt.Println("Bye.")
				break
			}
			execute(stmt)
		}
	}
}

// ---------------------------------------------------------------------------
// Meta-commands (\i, \d, \dt)
// ---------------------------------------------------------------------------

func handleMeta(line string) {
	line = strings.TrimSuffix(strings.TrimSpace(line), ";")
	parts := strings.Fields(line)
	if len(parts) == 0 {
		return
	}
	cmd := strings.ToLower(parts[0])
	switch cmd {
	case `\i`:
		if len(parts) < 2 {
			fmt.Println(`Syntax: \i <script.sql>   (executes a plain-text SQL script, not a .msql database file)`)
			return
		}
		fname := parts[1]
		// Guard: warn if the file looks like an encrypted .msql database
		if isEncryptedDB(fname) {
			fmt.Printf("Error: '%s' is an encrypted MiniSQL database file, not a SQL script.\n", fname)
			fmt.Printf("To switch databases use: \\connect %s\n", fname)
			return
		}
		runFile(fname)
	case `\d`:
		if len(parts) < 2 {
			fmt.Println(`Syntax: \d <table>   or use \dt to list tables`)
			return
		}
		describeTable("DESCRIBE " + parts[1])
	case `\dt`:
		showTables()
	case `\connect`, `\c`:
		if len(parts) < 2 {
			fmt.Printf("Current database: %s\nSyntax: \\connect <file.msql>\n", dbFile)
			return
		}
		connectDB(parts[1])
	case `\loglevel`:
		if len(parts) < 2 {
			fmt.Printf("Log level: %s\nSyntax: \\loglevel debug|info|warn|error\n", logLevel.Level())
			return
		}
		switch strings.ToLower(parts[1]) {
		case "debug":
			logLevel.Set(slog.LevelDebug)
		case "info":
			logLevel.Set(slog.LevelInfo)
		case "warn":
			logLevel.Set(slog.LevelWarn)
		case "error":
			logLevel.Set(slog.LevelError)
		default:
			fmt.Println("Unknown level. Use: debug, info, warn, error")
			return
		}
		fmt.Printf("Log level set to %s\n", logLevel.Level())
		if dbFile == "" {
			fmt.Println("No database loaded. Use \\connect <file.msql> to open one.")
		} else {
			fmt.Printf("Database : %s\n", dbFile)
			fmt.Printf("Key file : %s\n", keyFile)
			fmt.Printf("Tables   : %d\n", len(database))
			total := 0
			for _, t := range database {
				total += len(t.Rows)
			}
			fmt.Printf("Rows     : %d\n", total)
		}
	default:
		fmt.Printf("Unknown meta-command: %s\n", parts[0])
		// Suggest close matches
		known := []string{`\i`, `\d`, `\dt`, `\connect`, `\c`, `\status`}
		for _, k := range known {
			if strings.HasPrefix(k, parts[0][:min(len(parts[0]), len(k))]) ||
				levenshtein(cmd, k) <= 2 {
				fmt.Printf("  Did you mean: %s ?\n", k)
				break
			}
		}
	}
}

// isEncryptedDB peeks at the first line of a file to detect the v3 format header.
func isEncryptedDB(fname string) bool {
	f, err := os.Open(fname)
	if err != nil {
		return false
	}
	defer f.Close()
	buf := make([]byte, 80)
	n, _ := f.Read(buf)
	return strings.Contains(string(buf[:n]), "format v3")
}

// levenshtein computes edit distance between two short strings.
func levenshtein(a, b string) int {
	if a == b {
		return 0
	}
	if len(a) == 0 {
		return len(b)
	}
	if len(b) == 0 {
		return len(a)
	}
	row := make([]int, len(b)+1)
	for j := range row {
		row[j] = j
	}
	for i, ca := range a {
		prev := i + 1
		for j, cb := range b {
			next := row[j]
			if ca != cb {
				next = 1 + min(min(next, prev), row[j+1])
			}
			row[j] = prev
			prev = next
		}
		row[len(b)] = prev
	}
	return row[len(b)]
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

// ---------------------------------------------------------------------------
// Lexer — tokenises SQL into a flat token stream
// ---------------------------------------------------------------------------

type TokKind int

const (
	tokEOF TokKind = iota
	tokIdent                // unquoted identifier or keyword
	tokString               // 'single-quoted string'
	tokNumber               // 123, 3.14
	tokStar                 // *
	tokComma                // ,
	tokLParen               // (
	tokRParen               // )
	tokDot                  // .
	tokEq                   // =
	tokNeq                  // !=  or  <>
	tokLt                   // <
	tokLe                   // <=
	tokGt                   // >
	tokGe                   // >=
	tokSemicolon            // ;
)

type Token struct {
	Kind TokKind
	Val  string // raw text (lower-cased for keywords, original for strings/numbers)
}

func lex(input string) []Token {
	var tokens []Token
	i := 0
	for i < len(input) {
		ch := input[i]
		// Skip whitespace
		if ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n' {
			i++
			continue
		}
		// Single-line comment
		if ch == '-' && i+1 < len(input) && input[i+1] == '-' {
			for i < len(input) && input[i] != '\n' {
				i++
			}
			continue
		}
		// Single-quoted string
		if ch == '\'' {
			j := i + 1
			for j < len(input) && !(input[j] == '\'' && (j+1 >= len(input) || input[j+1] != '\'')) {
				if input[j] == '\'' { // escaped ''
					j += 2
				} else {
					j++
				}
			}
			val := input[i+1 : j]
			val = strings.ReplaceAll(val, "''", "'")
			tokens = append(tokens, Token{tokString, val})
			i = j + 1
			continue
		}
		// Numbers
		if (ch >= '0' && ch <= '9') || (ch == '-' && i+1 < len(input) && input[i+1] >= '0' && input[i+1] <= '9') {
			j := i
			if input[j] == '-' {
				j++
			}
			for j < len(input) && (input[j] >= '0' && input[j] <= '9' || input[j] == '.') {
				j++
			}
			tokens = append(tokens, Token{tokNumber, input[i:j]})
			i = j
			continue
		}
		// Identifiers and keywords
		if isIdentStart(ch) {
			j := i
			for j < len(input) && isIdentCont(input[j]) {
				j++
			}
			tokens = append(tokens, Token{tokIdent, input[i:j]})
			i = j
			continue
		}
		// Operators and punctuation
		switch ch {
		case '*':
			tokens = append(tokens, Token{tokStar, "*"})
			i++
		case ',':
			tokens = append(tokens, Token{tokComma, ","})
			i++
		case '(':
			tokens = append(tokens, Token{tokLParen, "("})
			i++
		case ')':
			tokens = append(tokens, Token{tokRParen, ")"})
			i++
		case '.':
			tokens = append(tokens, Token{tokDot, "."})
			i++
		case ';':
			tokens = append(tokens, Token{tokSemicolon, ";"})
			i++
		case '=':
			tokens = append(tokens, Token{tokEq, "="})
			i++
		case '!':
			if i+1 < len(input) && input[i+1] == '=' {
				tokens = append(tokens, Token{tokNeq, "!="})
				i += 2
			} else {
				i++ // skip unknown char
			}
		case '<':
			if i+1 < len(input) && input[i+1] == '=' {
				tokens = append(tokens, Token{tokLe, "<="})
				i += 2
			} else if i+1 < len(input) && input[i+1] == '>' {
				tokens = append(tokens, Token{tokNeq, "!="})
				i += 2
			} else {
				tokens = append(tokens, Token{tokLt, "<"})
				i++
			}
		case '>':
			if i+1 < len(input) && input[i+1] == '=' {
				tokens = append(tokens, Token{tokGe, ">="})
				i += 2
			} else {
				tokens = append(tokens, Token{tokGt, ">"})
				i++
			}
		default:
			i++ // skip unknown
		}
	}
	tokens = append(tokens, Token{tokEOF, ""})
	return tokens
}

func isIdentStart(c byte) bool {
	return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
}
func isIdentCont(c byte) bool {
	return isIdentStart(c) || (c >= '0' && c <= '9')
}

// ---------------------------------------------------------------------------
// Token stream — peek / consume helpers
// ---------------------------------------------------------------------------

type tokenStream struct {
	tokens []Token
	pos    int
}

func newStream(tokens []Token) *tokenStream { return &tokenStream{tokens, 0} }

func (ts *tokenStream) peek() Token {
	if ts.pos >= len(ts.tokens) {
		return Token{tokEOF, ""}
	}
	return ts.tokens[ts.pos]
}

func (ts *tokenStream) peekUp() string { return strings.ToUpper(ts.peek().Val) }

func (ts *tokenStream) next() Token {
	t := ts.peek()
	if ts.pos < len(ts.tokens) {
		ts.pos++
	}
	return t
}

// expect consumes the next token and returns it; prints error and returns zero if mismatch.
func (ts *tokenStream) expect(kind TokKind, val string) (Token, bool) {
	t := ts.next()
	if t.Kind != kind || (val != "" && !strings.EqualFold(t.Val, val)) {
		fmt.Printf("Syntax error: expected %q, got %q\n", val, t.Val)
		return Token{}, false
	}
	return t, true
}

// keyword returns true and consumes the token if the next token is a keyword matching s.
func (ts *tokenStream) keyword(s string) bool {
	if ts.peek().Kind == tokIdent && strings.EqualFold(ts.peek().Val, s) {
		ts.next()
		return true
	}
	return false
}

// ---------------------------------------------------------------------------
// Condition / WHERE clause — shared between SELECT, UPDATE, DELETE
// ---------------------------------------------------------------------------

type condition struct {
	col   string  // may be "table.col" for joins
	op    string  // = != < > <= >= LIKE IS_NULL IS_NOT_NULL
	val   string
}

// parseWhere parses: col op value [AND|OR col op value ...]
// Returns slice of conditions (all ANDed together for now; OR is also supported
// by wrapping in an orGroup — kept simple since we have no query planner).
func parseWhere(ts *tokenStream) []condition {
	var conds []condition
	for {
		col := ts.parseColRef()
		if col == "" {
			break
		}
		// IS NULL / IS NOT NULL
		if strings.EqualFold(ts.peekUp(), "IS") {
			ts.next()
			not := ts.keyword("NOT")
			if !ts.keyword("NULL") {
				fmt.Println("Syntax error: expected NULL after IS [NOT]")
				break
			}
			op := "IS_NULL"
			if not {
				op = "IS_NOT_NULL"
			}
			conds = append(conds, condition{col, op, ""})
		} else {
			op := ts.parseOp()
			if op == "" {
				fmt.Println("Syntax error: expected operator in WHERE clause")
				break
			}
			val := ts.parseValue()
			conds = append(conds, condition{col, op, val})
		}
		// AND / OR — OR is treated as AND for now (noted in EXPLAIN output)
		t := ts.peek()
		if t.Kind == tokIdent && (strings.EqualFold(t.Val, "AND") || strings.EqualFold(t.Val, "OR")) {
			ts.next()
			continue
		}
		break
	}
	return conds
}

func (ts *tokenStream) parseColRef() string {
	t := ts.peek()
	if t.Kind != tokIdent {
		return ""
	}
	ts.next()
	col := t.Val
	// table.col reference
	if ts.peek().Kind == tokDot {
		ts.next()
		if ts.peek().Kind == tokIdent {
			col = col + "." + ts.next().Val
		}
	}
	return col
}

func (ts *tokenStream) parseOp() string {
	t := ts.next()
	switch t.Kind {
	case tokEq:
		return "="
	case tokNeq:
		return "!="
	case tokLt:
		return "<"
	case tokLe:
		return "<="
	case tokGt:
		return ">"
	case tokGe:
		return ">="
	case tokIdent:
		if strings.EqualFold(t.Val, "LIKE") {
			return "LIKE"
		}
		if strings.EqualFold(t.Val, "NOT") && ts.keyword("LIKE") {
			return "NOT_LIKE"
		}
	}
	fmt.Printf("Syntax error: unknown operator %q\n", t.Val)
	return ""
}

func (ts *tokenStream) parseValue() string {
	t := ts.next()
	switch t.Kind {
	case tokString:
		return t.Val
	case tokNumber:
		return t.Val
	case tokIdent:
		if strings.EqualFold(t.Val, "NULL") {
			return nullSentinel
		}
		if strings.EqualFold(t.Val, "TRUE") {
			return "true"
		}
		if strings.EqualFold(t.Val, "FALSE") {
			return "false"
		}
		return t.Val // bare identifier used as value
	case tokStar:
		return "*"
	}
	return ""
}

// ---------------------------------------------------------------------------
// SELECT parser — handles JOIN, subquery-free
// ---------------------------------------------------------------------------

type joinClause struct {
	kind      string // INNER, LEFT
	table     string
	leftCol   string // qualified: table.col
	rightCol  string
}

type selectStmt struct {
	cols      []string    // raw column expressions (may be *, table.*, agg(...))
	fromTable string
	joins     []joinClause
	where     []condition
	orderBy   string
	orderDesc bool
	limit     int
	explain   bool
}

func parseSelect(input string) (*selectStmt, error) {
	tokens := lex(input)
	ts := newStream(tokens)

	stmt := &selectStmt{limit: -1}

	// EXPLAIN SELECT ...
	if strings.EqualFold(ts.peek().Val, "EXPLAIN") {
		ts.next()
		stmt.explain = true
	}

	if !ts.keyword("SELECT") {
		return nil, fmt.Errorf("expected SELECT")
	}

	// Column list
	stmt.cols = parseColList(ts)

	if !ts.keyword("FROM") {
		return nil, fmt.Errorf("expected FROM")
	}
	stmt.fromTable = ts.next().Val

	// JOINs
	for {
		kind := ""
		if ts.keyword("INNER") {
			kind = "INNER"
		} else if ts.keyword("LEFT") {
			kind = "LEFT"
		} else if ts.keyword("CROSS") {
			kind = "CROSS"
		} else {
			break
		}
		ts.keyword("JOIN") // consume optional JOIN keyword
		joinTable := ts.next().Val
		if !ts.keyword("ON") {
			return nil, fmt.Errorf("expected ON after JOIN table name")
		}
		leftRef := ts.parseColRef()
		if _, ok := ts.expect(tokEq, "="); !ok {
			return nil, fmt.Errorf("expected = in JOIN ON clause")
		}
		rightRef := ts.parseColRef()
		stmt.joins = append(stmt.joins, joinClause{kind, joinTable, leftRef, rightRef})
	}

	// WHERE
	if ts.keyword("WHERE") {
		stmt.where = parseWhere(ts)
	}

	// ORDER BY
	if ts.keyword("ORDER") {
		ts.keyword("BY")
		stmt.orderBy = ts.parseColRef()
		if ts.keyword("DESC") {
			stmt.orderDesc = true
		} else {
			ts.keyword("ASC")
		}
	}

	// LIMIT
	if ts.keyword("LIMIT") {
		n, err := strconv.Atoi(ts.next().Val)
		if err != nil {
			return nil, fmt.Errorf("LIMIT expects integer")
		}
		stmt.limit = n
	}

	return stmt, nil
}

func parseColList(ts *tokenStream) []string {
	var cols []string
	for {
		// Aggregate: FUNC(col)
		if ts.peek().Kind == tokIdent {
			next := ts.peek().Val
			upper := strings.ToUpper(next)
			if upper == "COUNT" || upper == "SUM" || upper == "AVG" || upper == "MIN" || upper == "MAX" {
				fn := ts.next().Val
				if ts.peek().Kind == tokLParen {
					ts.next()
					inner := ts.next().Val
					if ts.peek().Kind == tokStar {
						inner = "*"
						ts.next()
					}
					ts.next() // )
					cols = append(cols, strings.ToUpper(fn)+"("+inner+")")
					if ts.peek().Kind != tokComma {
						break
					}
					ts.next()
					continue
				}
			}
		}
		// * or table.*
		if ts.peek().Kind == tokStar {
			ts.next()
			cols = append(cols, "*")
		} else {
			ref := ts.parseColRef()
			if ref == "" {
				break
			}
			cols = append(cols, ref)
		}
		if ts.peek().Kind != tokComma {
			break
		}
		ts.next() // consume comma
	}
	return cols
}

// ---------------------------------------------------------------------------
// Dispatcher
// ---------------------------------------------------------------------------

func execute(query string) {
	query = strings.TrimSpace(query)
	upper := strings.ToUpper(query)

	if upper == "HELP" {
		printHelp()
		return
	}
	if upper == "SHOW TABLES" {
		showTables()
		return
	}

	if dbFile == "" || encKey == nil {
		fmt.Println("No database open. Use \\connect <file.msql> to open or create one.")
		return
	}

	start := time.Now()

	switch {
	case upper == "BEGIN":
		txBegin()
	case upper == "COMMIT":
		txCommit()
	case upper == "ROLLBACK":
		txRollback()
	case strings.HasPrefix(upper, "EXPLAIN ") || upper == "EXPLAIN":
		// Route EXPLAIN SELECT through new parser
		inner := strings.TrimSpace(query[7:])
		if strings.HasPrefix(strings.ToUpper(inner), "SELECT") {
			selectFrom("EXPLAIN " + inner)
		} else {
			fmt.Println("EXPLAIN only supports SELECT currently.")
		}
	case strings.HasPrefix(upper, "ALTER DATABASE"):
		if strings.Contains(upper, "SET PASSWORD") || strings.Contains(upper, "ROTATE KEY") {
			rotateKey()
		} else {
			fmt.Println("Syntax: ALTER DATABASE SET PASSWORD")
		}
	case strings.HasPrefix(upper, "DESCRIBE "):
		describeTable(query)
	case strings.HasPrefix(upper, "CREATE TABLE"):
		createTable(query)
	case strings.HasPrefix(upper, "ALTER TABLE"):
		alterTable(query)
	case strings.HasPrefix(upper, "DROP TABLE"):
		dropTable(query)
	case strings.HasPrefix(upper, "TRUNCATE TABLE"):
		truncateTable(query)
	case strings.HasPrefix(upper, "INSERT INTO"):
		insertInto(query)
	case strings.HasPrefix(upper, "SELECT"), strings.HasPrefix(upper, "EXPLAIN SELECT"):
		selectFrom(query)
	case strings.HasPrefix(upper, "UPDATE"):
		updateTable(query)
	case strings.HasPrefix(upper, "DELETE FROM"):
		deleteFrom(query)
	case query == "":
		// nothing
	default:
		fmt.Println("Unknown command. Type HELP for a list of commands.")
	}

	logQuery(strings.Fields(upper)[0], "", time.Since(start), 0)
}

// ---------------------------------------------------------------------------
// SHOW TABLES
// ---------------------------------------------------------------------------

func showTables() {
	dbMu.RLock()
	defer dbMu.RUnlock()
	if len(database) == 0 {
		fmt.Println("No tables.")
		return
	}
	names := make([]string, 0, len(database))
	for n := range database {
		names = append(names, n)
	}
	sort.Strings(names)
	fmt.Println("Tables:")
	for _, n := range names {
		t := database[n]
		fmt.Printf("  %-24s  %d col(s), %d row(s)\n", n, len(t.Columns), len(t.Rows))
	}
}

// ---------------------------------------------------------------------------
// DESCRIBE
// ---------------------------------------------------------------------------

func describeTable(query string) {
	parts := strings.Fields(query)
	if len(parts) < 2 {
		fmt.Println("Syntax error: DESCRIBE <table>")
		return
	}
	name := parts[1]
	t, ok := database[name]
	if !ok {
		fmt.Println("Table not found:", name)
		return
	}
	fmt.Printf("Table: %s  (%d row(s))  [%s]\n", name, len(t.Rows), dbFile)
	rows := [][]string{{"Column", "Type", "Modifiers", "Default"}}
	for _, c := range t.Columns {
		var mods []string
		if c.AutoIter {
			mods = append(mods, "AUTOITER")
		}
		if c.AutoUUID {
			mods = append(mods, "AUTOUUID")
		}
		if c.AutoTS {
			if c.AutoTSUpdate {
				mods = append(mods, "AUTOTS UPDATE")
			} else {
				mods = append(mods, "AUTOTS")
			}
		}
		if c.Secure {
			mods = append(mods, "SECURE")
		}
		if c.NotNull {
			mods = append(mods, "NOT NULL")
		}
		if c.Unique {
			mods = append(mods, "UNIQUE")
		}
		def := c.Default
		if def == "" {
			def = "-"
		}
		rows = append(rows, []string{c.Name, c.Type, strings.Join(mods, " "), def})
	}
	printTable(rows)
}

// ---------------------------------------------------------------------------
// Transactions — BEGIN / COMMIT / ROLLBACK
// ---------------------------------------------------------------------------

func txBegin() {
	if txSnapshot != nil {
		fmt.Println("Warning: already inside a transaction. Implicit COMMIT of previous transaction.")
		txCommit()
	}
	dbMu.RLock()
	snap := make(map[string]*Table, len(database))
	for k, t := range database {
		snap[k] = cloneTable(t)
	}
	dbMu.RUnlock()
	txSnapshot = snap
	fmt.Println("BEGIN")
}

func txCommit() {
	if txSnapshot == nil {
		fmt.Println("Error: no active transaction.")
		return
	}
	txSnapshot = nil
	saveDB(dbFile)
	fmt.Println("COMMIT")
}

func txRollback() {
	if txSnapshot == nil {
		fmt.Println("Error: no active transaction.")
		return
	}
	dbMu.Lock()
	for k := range database {
		delete(database, k)
	}
	for k, t := range txSnapshot {
		database[k] = t
	}
	dbMu.Unlock()
	txSnapshot = nil
	fmt.Println("ROLLBACK")
}

// ---------------------------------------------------------------------------
// CREATE TABLE
// ---------------------------------------------------------------------------

func createTable(query string) {
	upper := strings.ToUpper(query)
	ifNotExists := strings.Contains(upper, "IF NOT EXISTS")

	// Normalise: strip "IF NOT EXISTS" so the rest parses the same way
	normalized := query
	if ifNotExists {
		re := regexp.MustCompile(`(?i)IF\s+NOT\s+EXISTS\s+`)
		normalized = re.ReplaceAllString(normalized, "")
		normalized = strings.TrimSpace(normalized)
	}

	parts := strings.SplitN(normalized, "(", 2)
	if len(parts) < 2 {
		fmt.Println("Syntax error: expected '(' in CREATE TABLE")
		return
	}
	header := strings.Fields(parts[0])
	if len(header) < 3 {
		fmt.Println("Syntax error: missing table name")
		return
	}
	tableName := header[2]
	if _, exists := database[tableName]; exists {
		if ifNotExists {
			fmt.Printf("Table '%s' already exists — skipped.\n", tableName)
			return
		}
		fmt.Println("Error: table already exists:", tableName)
		return
	}

	columnPart := strings.TrimSuffix(strings.TrimSpace(parts[1]), ")")
	columns := splitColumns(columnPart)
	if columns == nil {
		return
	}

	t := &Table{
		Columns:      columns,
		Rows:         [][]string{},
		AutoCounters: map[string]int{},
	}
	for _, c := range columns {
		if c.AutoIter {
			t.AutoCounters[c.Name] = 1
		}
	}
	dbMu.Lock()
	database[tableName] = t
	dbMu.Unlock()
	fmt.Printf("Table '%s' created (%d column(s)).\n", tableName, len(columns))
}

// tokenizeQuoteAware splits on whitespace but treats single-quoted
// strings (which may contain spaces, e.g. '2026-01-15 12:00:00') as
// a single token.
func tokenizeQuoteAware(s string) []string {
	var tokens []string
	var cur strings.Builder
	inQuote := false
	for i := 0; i < len(s); i++ {
		ch := s[i]
		if ch == '\'' {
			inQuote = !inQuote
			cur.WriteByte(ch)
		} else if (ch == ' ' || ch == '\t') && !inQuote {
			if cur.Len() > 0 {
				tokens = append(tokens, cur.String())
				cur.Reset()
			}
		} else {
			cur.WriteByte(ch)
		}
	}
	if cur.Len() > 0 {
		tokens = append(tokens, cur.String())
	}
	return tokens
}

func splitColumns(input string) []Column {
	rawParts := smartSplit(input, ',')
	var cols []Column
	seen := map[string]bool{}
	for _, raw := range rawParts {
		raw = strings.TrimSpace(raw)
		if raw == "" {
			continue
		}
		// Quote-aware tokenisation (fixes TIMESTAMP/DATE defaults with spaces)
		origTokens := tokenizeQuoteAware(raw)
		if len(origTokens) == 0 {
			continue
		}
		col := Column{Name: origTokens[0]}
		if seen[col.Name] {
			fmt.Printf("Error: duplicate column name '%s'\n", col.Name)
			return nil
		}
		seen[col.Name] = true

		for i := 1; i < len(origTokens); i++ {
			tok := origTokens[i]
			up := strings.ToUpper(tok)
			switch {
			case validTypes[up]:
				if col.Type == "" {
					col.Type = up
				}
			case up == "AUTOITER":
				col.AutoIter = true
				if col.Type == "" {
					col.Type = "INT"
				}
			case up == "AUTOUUID":
				col.AutoUUID = true
				if col.Type == "" {
					col.Type = "UUID"
				}
			case up == "AUTOTS":
				// AUTOTS [UPDATE] — check if next token is UPDATE
				col.AutoTS = true
				if col.Type == "" {
					col.Type = "TIMESTAMP"
				}
				if i+1 < len(origTokens) && strings.ToUpper(origTokens[i+1]) == "UPDATE" {
					col.AutoTSUpdate = true
					i++
				}
			case up == "SECURE":
				col.Secure = true
			case up == "UNIQUE":
				col.Unique = true
			case up == "NOT" && i+1 < len(origTokens) && strings.ToUpper(origTokens[i+1]) == "NULL":
				col.NotNull = true
				i++ // consume "NULL"
			case up == "DEFAULT":
				if i+1 < len(origTokens) {
					i++
					val := origTokens[i]
					// Strip surrounding single quotes from the stored default
					if len(val) >= 2 && val[0] == '\'' && val[len(val)-1] == '\'' {
						val = val[1 : len(val)-1]
					}
					col.Default = val
				}
			}
		}
		cols = append(cols, col)
	}
	return cols
}

// ---------------------------------------------------------------------------
// DROP TABLE [IF EXISTS]
// ---------------------------------------------------------------------------

func dropTable(query string) {
	upper := strings.ToUpper(query)
	ifExists := strings.Contains(upper, "IF EXISTS")

	fields := strings.Fields(query)
	// DROP TABLE [IF EXISTS] name  → name is last token
	name := fields[len(fields)-1]
	if _, ok := database[name]; !ok {
		if ifExists {
			fmt.Printf("Table '%s' does not exist — skipped.\n", name)
			return
		}
		fmt.Println("Table not found:", name)
		return
	}
	dbMu.Lock()
	delete(database, name)
	dbMu.Unlock()
	fmt.Printf("Table '%s' dropped.\n", name)
}

// ---------------------------------------------------------------------------
// TRUNCATE TABLE
// ---------------------------------------------------------------------------

func truncateTable(query string) {
	fields := strings.Fields(query)
	if len(fields) < 3 {
		fmt.Println("Syntax error: TRUNCATE TABLE <name>")
		return
	}
	name := fields[2]
	t, ok := database[name]
	if !ok {
		fmt.Println("Table not found:", name)
		return
	}
	n := len(t.Rows)
	t.Rows = [][]string{}
	// Reset auto-counters
	for k := range t.AutoCounters {
		t.AutoCounters[k] = 1
	}
	fmt.Printf("Table '%s' truncated (%d row(s) removed).\n", name, n)
}

// ---------------------------------------------------------------------------
// ALTER TABLE
// ---------------------------------------------------------------------------

func alterTable(query string) {
	// ALTER TABLE <name> <action> ...
	fields := strings.Fields(query)
	if len(fields) < 4 {
		fmt.Println("Syntax error: ALTER TABLE <name> ADD|DROP|RENAME ...")
		return
	}
	tableName := fields[2]
	table, ok := database[tableName]
	if !ok {
		fmt.Println("Table not found:", tableName)
		return
	}

	action := strings.ToUpper(fields[3])
	switch action {
	case "ADD":
		// ALTER TABLE t ADD COLUMN col TYPE [mods...]
		// "COLUMN" keyword is optional (PostgreSQL allows omitting it)
		rest := strings.TrimSpace(query)
		// strip up to and including ADD (or ADD COLUMN)
		addIdx := strings.Index(strings.ToUpper(rest), " ADD ")
		rest = strings.TrimSpace(rest[addIdx+5:])
		if strings.HasPrefix(strings.ToUpper(rest), "COLUMN ") {
			rest = strings.TrimSpace(rest[7:])
		}
		cols := splitColumns(rest)
		if cols == nil || len(cols) == 0 {
			return
		}
		for _, c := range cols {
			if colIndex(table, c.Name) != -1 {
				fmt.Printf("Error: column '%s' already exists.\n", c.Name)
				return
			}
			table.Columns = append(table.Columns, c)
			if c.AutoIter {
				table.AutoCounters[c.Name] = 1
			}
			// Backfill existing rows with NULL or DEFAULT
			defVal := nullSentinel
			if c.Default != "" {
				defVal = resolveDefault(c)
			}
			for i := range table.Rows {
				table.Rows[i] = append(table.Rows[i], defVal)
			}
			fmt.Printf("Column '%s' added to '%s'.\n", c.Name, tableName)
		}

	case "DROP":
		// ALTER TABLE t DROP COLUMN col
		if len(fields) < 5 {
			fmt.Println("Syntax error: ALTER TABLE <t> DROP COLUMN <col>")
			return
		}
		colName := fields[len(fields)-1]
		if strings.ToUpper(fields[4]) == "COLUMN" && len(fields) >= 6 {
			colName = fields[5]
		}
		idx := colIndex(table, colName)
		if idx == -1 {
			fmt.Println("Column not found:", colName)
			return
		}
		if len(table.Columns) == 1 {
			fmt.Println("Error: cannot drop the only column in a table.")
			return
		}
		table.Columns = append(table.Columns[:idx], table.Columns[idx+1:]...)
		for i, row := range table.Rows {
			table.Rows[i] = append(row[:idx], row[idx+1:]...)
		}
		fmt.Printf("Column '%s' dropped from '%s'.\n", colName, tableName)

	case "RENAME":
		if len(fields) < 6 {
			fmt.Println("Syntax error: ALTER TABLE <t> RENAME COLUMN <old> TO <new>  |  RENAME TO <new>")
			return
		}
		sub := strings.ToUpper(fields[4])
		if sub == "TO" {
			// ALTER TABLE t RENAME TO newname
			newName := fields[5]
			if _, exists := database[newName]; exists {
				fmt.Println("Error: table already exists:", newName)
				return
			}
			database[newName] = table
			delete(database, tableName)
			fmt.Printf("Table '%s' renamed to '%s'.\n", tableName, newName)
		} else if sub == "COLUMN" {
			// ALTER TABLE t RENAME COLUMN old TO new
			if len(fields) < 7 {
				fmt.Println("Syntax error: ALTER TABLE <t> RENAME COLUMN <old> TO <new>")
				return
			}
			oldCol := fields[5]
			newCol := fields[7]
			idx := colIndex(table, oldCol)
			if idx == -1 {
				fmt.Println("Column not found:", oldCol)
				return
			}
			if colIndex(table, newCol) != -1 {
				fmt.Printf("Error: column '%s' already exists.\n", newCol)
				return
			}
			table.Columns[idx].Name = newCol
			// Update AutoCounters key if needed
			if n, ok2 := table.AutoCounters[oldCol]; ok2 {
				table.AutoCounters[newCol] = n
				delete(table.AutoCounters, oldCol)
			}
			fmt.Printf("Column '%s' renamed to '%s'.\n", oldCol, newCol)
		} else {
			fmt.Println("Syntax error: expected COLUMN or TO after RENAME")
		}

	default:
		fmt.Println("Syntax error: unknown ALTER TABLE action:", action)
	}
}

// ---------------------------------------------------------------------------
// INSERT INTO — supports named column list and NOW() defaults
// ---------------------------------------------------------------------------

// resolveDefault expands NOW() into the current timestamp/date string.
func resolveDefault(col Column) string {
	up := strings.ToUpper(col.Default)
	if up == "NOW()" {
		return nowForCol(col)
	}
	if up == "UUID()" || up == "GEN_RANDOM_UUID()" {
		return generateUUID()
	}
	return col.Default
}

func insertInto(query string) {
	upper := strings.ToUpper(query)
	vi := strings.Index(upper, "VALUES")
	if vi == -1 {
		fmt.Println("Syntax error: missing VALUES")
		return
	}

	left := strings.TrimSpace(query[:vi])
	// Detect named column list: INSERT INTO t (col1, col2) VALUES ...
	var namedCols []string
	parenOpen := strings.Index(left, "(")
	if parenOpen != -1 {
		parenClose := strings.LastIndex(left, ")")
		if parenClose == -1 {
			fmt.Println("Syntax error: unmatched '(' in column list")
			return
		}
		colList := left[parenOpen+1 : parenClose]
		for _, c := range splitCSV(colList) {
			namedCols = append(namedCols, strings.TrimSpace(c))
		}
		left = left[:parenOpen]
	}

	leftFields := strings.Fields(left)
	if len(leftFields) < 3 {
		fmt.Println("Syntax error: missing table name")
		return
	}
	tableName := leftFields[2]

	table, exists := database[tableName]
	if !exists {
		fmt.Println("Table not found:", tableName)
		return
	}

	valuePart := strings.TrimSpace(query[vi+6:])
	valuePart = strings.TrimPrefix(valuePart, "(")
	valuePart = strings.TrimSuffix(valuePart, ")")
	values := parseValues(valuePart)

	// Build a workRow aligned to table.Columns
	workRow := make([]string, len(table.Columns))
	for i := range workRow {
		workRow[i] = nullSentinel // default everything to NULL
	}

	if len(namedCols) > 0 {
		// Named-column insert
		if len(namedCols) != len(values) {
			fmt.Printf("Column count mismatch: %d column(s) named, %d value(s) given\n",
				len(namedCols), len(values))
			return
		}
		for j, cname := range namedCols {
			idx := colIndex(table, cname)
			if idx == -1 {
				fmt.Println("Column not found:", cname)
				return
			}
			workRow[idx] = values[j]
		}
	} else {
		// Positional insert — auto-columns (AUTOITER, AUTOUUID, AUTOTS) are skipped
		autoCount := 0
		for _, c := range table.Columns {
			if c.AutoIter || c.AutoUUID || c.AutoTS {
				autoCount++
			}
		}
		nonAutoCount := len(table.Columns) - autoCount
		switch len(values) {
		case nonAutoCount:
			vi2 := 0
			for i, col := range table.Columns {
				if col.AutoIter || col.AutoUUID || col.AutoTS {
					// leave as nullSentinel — auto-filled below
				} else {
					workRow[i] = values[vi2]
					vi2++
				}
			}
		case len(table.Columns):
			copy(workRow, values)
		default:
			fmt.Printf("Column count mismatch: got %d, expected %d (or %d omitting auto columns)\n",
				len(values), len(table.Columns), nonAutoCount)
			return
		}
	}

	// Validate, apply auto-values, defaults, constraints, encrypt
	finalRow := make([]string, len(table.Columns))
	for i, col := range table.Columns {
		val := workRow[i]
		isNull := strings.ToUpper(val) == nullSentinel || val == ""

		// AUTOTS — always overwrite with current time; user cannot supply a value
		if col.AutoTS {
			finalRow[i] = nowForCol(col)
			continue
		}

		// AUTOITER
		if col.AutoIter && isNull {
			n := table.AutoCounters[col.Name]
			val = strconv.Itoa(n)
			table.AutoCounters[col.Name] = n + 1
			isNull = false
		}

		// AUTOUUID
		if col.AutoUUID && isNull {
			val = generateUUID()
			isNull = false
		}

		// Apply DEFAULT (including NOW() / UUID())
		if isNull && col.Default != "" {
			val = resolveDefault(col)
			isNull = false
		}

		if col.NotNull && isNull {
			fmt.Printf("Error: column '%s' is NOT NULL\n", col.Name)
			return
		}
		if isNull {
			finalRow[i] = nullSentinel
			continue
		}

		if col.Type != "" && col.Type != "TEXT" && col.Type != "VARCHAR" {
			if err := validateType(col, val); err != nil {
				fmt.Println("Error:", err)
				return
			}
		}

		// UNIQUE check
		if col.Unique {
			for _, row := range table.Rows {
				existing := row[i]
				if col.Secure {
					if p, err := decryptValue(existing); err == nil {
						existing = p
					}
				}
				if existing == val {
					fmt.Printf("Error: duplicate value '%s' violates UNIQUE constraint on '%s'\n", val, col.Name)
					return
				}
			}
		}

		if col.Secure {
			enc, err := encryptValue(val)
			if err != nil {
				fmt.Printf("Error encrypting '%s': %v\n", col.Name, err)
				return
			}
			finalRow[i] = enc
		} else {
			finalRow[i] = val
		}
	}

	table.mu.Lock()
	table.Rows = append(table.Rows, finalRow)
	table.mu.Unlock()
	fmt.Println("1 row inserted.")
}

func parseValues(input string) []string {
	var result []string
	var cur strings.Builder
	inQuote := false
	for i := 0; i < len(input); i++ {
		ch := input[i]
		switch {
		case ch == '\'' && !inQuote:
			inQuote = true
		case ch == '\'' && inQuote:
			inQuote = false
		case ch == ',' && !inQuote:
			result = append(result, strings.TrimSpace(cur.String()))
			cur.Reset()
		default:
			cur.WriteByte(ch)
		}
	}
	result = append(result, strings.TrimSpace(cur.String()))
	return result
}

// ---------------------------------------------------------------------------
// UPDATE
// ---------------------------------------------------------------------------

func updateTable(query string) {
	fields := strings.Fields(query)
	if len(fields) < 4 {
		fmt.Println("Syntax error: UPDATE <table> SET col=val [WHERE ...]")
		return
	}
	tableName := fields[1]
	table, ok := database[tableName]
	if !ok {
		fmt.Println("Table not found:", tableName)
		return
	}

	upper := strings.ToUpper(query)
	setIdx := strings.Index(upper, " SET ")
	if setIdx == -1 {
		fmt.Println("Syntax error: missing SET")
		return
	}
	rest := strings.TrimSpace(query[setIdx+5:])

	whereIdx := strings.Index(strings.ToUpper(rest), " WHERE ")
	var setStr, whereClause string
	if whereIdx == -1 {
		setStr = rest
	} else {
		setStr = strings.TrimSpace(rest[:whereIdx])
		whereClause = strings.TrimSpace(rest[whereIdx+7:])
	}

	// Parse assignments: col1=val1, col2=val2
	assignments := parseAssignments(setStr)
	if assignments == nil {
		return
	}

	// Resolve column indices for each assignment
	type assign struct {
		colIdx int
		val    string
	}
	var ops []assign
	for col, val := range assignments {
		idx := colIndex(table, col)
		if idx == -1 {
			fmt.Println("Column not found:", col)
			return
		}
		c := table.Columns[idx]
		// Block writes to immutable auto-columns
		if c.AutoIter {
			fmt.Printf("Error: column '%s' is AUTOITER and cannot be updated\n", col)
			return
		}
		if c.AutoUUID {
			fmt.Printf("Error: column '%s' is AUTOUUID and cannot be updated\n", col)
			return
		}
		if c.AutoTS && !c.AutoTSUpdate {
			fmt.Printf("Error: column '%s' is AUTOTS (immutable); use AUTOTS UPDATE to allow refresh\n", col)
			return
		}
		isNull := strings.ToUpper(val) == nullSentinel || val == ""
		if c.NotNull && isNull {
			fmt.Printf("Error: column '%s' is NOT NULL\n", col)
			return
		}
		if !isNull && c.Type != "" && c.Type != "TEXT" && c.Type != "VARCHAR" {
			if err := validateType(c, val); err != nil {
				fmt.Println("Error:", err)
				return
			}
		}
		if !isNull && c.Secure {
			enc, err := encryptValue(val)
			if err != nil {
				fmt.Printf("Error encrypting '%s': %v\n", col, err)
				return
			}
			val = enc
		}
		if isNull {
			val = nullSentinel
		}
		ops = append(ops, assign{idx, val})
	}

	// Collect AutoTSUpdate column indices to refresh on every matched row
	var autoTSUpdateCols []int
	for i, c := range table.Columns {
		if c.AutoTSUpdate {
			autoTSUpdateCols = append(autoTSUpdateCols, i)
		}
	}

	conditions := splitConditions(whereClause)
	updated := 0
	table.mu.Lock()
	for _, row := range table.Rows {
		if whereClause == "" || matchesAll(table, row, conditions) {
			for _, op := range ops {
				row[op.colIdx] = op.val
			}
			for _, ci := range autoTSUpdateCols {
				row[ci] = nowForCol(table.Columns[ci])
			}
			updated++
		}
	}
	table.mu.Unlock()
	fmt.Printf("%d row(s) updated.\n", updated)
}

func parseAssignments(s string) map[string]string {
	out := map[string]string{}
	parts := smartSplit(s, ',')
	for _, p := range parts {
		p = strings.TrimSpace(p)
		eq := strings.IndexByte(p, '=')
		if eq == -1 {
			fmt.Println("Syntax error in SET clause:", p)
			return nil
		}
		col := strings.TrimSpace(p[:eq])
		val := strings.TrimSpace(p[eq+1:])
		// Strip surrounding quotes
		if len(val) >= 2 && val[0] == '\'' && val[len(val)-1] == '\'' {
			val = val[1 : len(val)-1]
		}
		out[col] = val
	}
	return out
}

var aggRE = regexp.MustCompile(`(?i)^(COUNT|SUM|AVG|MIN|MAX)\s*\(\s*(\*|[A-Za-z_][A-Za-z0-9_.]*)\s*\)$`)

// virtualCol represents a column in a joined virtual table, tracking which
// source table it came from for qualified name resolution.
type virtualCol struct {
	tableAlias string
	colIdx     int
	col        Column
}

// ---------------------------------------------------------------------------
// SELECT — parser-backed, supports INNER/LEFT JOIN and EXPLAIN
// ---------------------------------------------------------------------------

func selectFrom(query string) {
	stmt, err := parseSelect(query)
	if err != nil {
		fmt.Println("Parse error:", err)
		return
	}

	// ---- EXPLAIN mode ----
	if stmt.explain {
		explainSelect(stmt)
		return
	}

	dbMu.RLock()
	tbl, ok := database[stmt.fromTable]
	dbMu.RUnlock()
	if !ok {
		fmt.Println("Table not found:", stmt.fromTable)
		return
	}

	var virtCols []virtualCol
	var virtRows [][]string

	tbl.mu.RLock()
	for i, c := range tbl.Columns {
		virtCols = append(virtCols, virtualCol{stmt.fromTable, i, c})
	}
	baseRows := make([][]string, len(tbl.Rows))
	copy(baseRows, tbl.Rows)
	tbl.mu.RUnlock()

	virtRows = baseRows

	for _, j := range stmt.joins {
		dbMu.RLock()
		joinTbl, ok2 := database[j.table]
		dbMu.RUnlock()
		if !ok2 {
			fmt.Println("Table not found:", j.table)
			return
		}

		joinTbl.mu.RLock()
		var joinVirtCols []virtualCol
		for i, c := range joinTbl.Columns {
			joinVirtCols = append(joinVirtCols, virtualCol{j.table, i, c})
		}
		joinRows := make([][]string, len(joinTbl.Rows))
		copy(joinRows, joinTbl.Rows)
		joinTbl.mu.RUnlock()

		// Resolve ON columns
		leftIdx := resolveVirtCol(virtCols, j.leftCol, stmt.fromTable)
		rightBaseIdx := -1
		for i, vc := range joinVirtCols {
			if strings.EqualFold(vc.col.Name, unqualify(j.rightCol)) ||
				strings.EqualFold(vc.tableAlias+"."+vc.col.Name, j.rightCol) {
				rightBaseIdx = i
				break
			}
		}
		if leftIdx == -1 || rightBaseIdx == -1 {
			fmt.Printf("JOIN: cannot resolve ON columns %q = %q\n", j.leftCol, j.rightCol)
			return
		}

		// Nested-loop join
		newVirtCols := append(virtCols, joinVirtCols...)
		var newRows [][]string
		nullPad := make([]string, len(joinVirtCols))
		for i := range nullPad {
			nullPad[i] = nullSentinel
		}
		for _, leftRow := range virtRows {
			matched := false
			for _, rightRow := range joinRows {
				lv := decryptIfNeeded(virtCols[leftIdx].col, leftRow[leftIdx])
				rv := decryptIfNeeded(joinVirtCols[rightBaseIdx].col, rightRow[rightBaseIdx])
				if lv == rv {
					combined := append(append([]string{}, leftRow...), rightRow...)
					newRows = append(newRows, combined)
					matched = true
				}
			}
			if !matched && j.kind == "LEFT" {
				combined := append(append([]string{}, leftRow...), nullPad...)
				newRows = append(newRows, combined)
			}
		}
		virtCols = newVirtCols
		virtRows = newRows
	}

	// ---- WHERE filter ----
	virtTable := &Table{Columns: make([]Column, len(virtCols))}
	for i, vc := range virtCols {
		virtTable.Columns[i] = vc.col
		// Qualify ambiguous names with table prefix
		if countColName(virtCols, vc.col.Name) > 1 {
			virtTable.Columns[i].Name = vc.tableAlias + "." + vc.col.Name
		}
	}

	var resultRows [][]string
	for _, row := range virtRows {
		if len(stmt.where) == 0 || matchesAll(virtTable, row, stmt.where) {
			resultRows = append(resultRows, row)
		}
	}

	// ---- Aggregates ----
	colExprs := stmt.cols
	var aggs []aggExpr
	for _, expr := range colExprs {
		m := aggRE.FindStringSubmatch(expr)
		if m == nil {
			aggs = nil
			break
		}
		aggs = append(aggs, aggExpr{strings.ToUpper(m[1]), m[2], strings.ToUpper(expr)})
	}

	if aggs != nil {
		row := make([]string, len(aggs))
		headers := make([]string, len(aggs))
		for i, ag := range aggs {
			headers[i] = ag.label
			if ag.fn == "COUNT" {
				row[i] = strconv.Itoa(len(resultRows))
				continue
			}
			idx := colIndexVirt(virtCols, ag.col)
			if idx == -1 {
				fmt.Println("Column not found:", ag.col)
				return
			}
			var nums []float64
			for _, r := range resultRows {
				v := decryptIfNeeded(virtCols[idx].col, r[idx])
				if v == nullSentinel {
					continue
				}
				if f, err2 := strconv.ParseFloat(v, 64); err2 == nil {
					nums = append(nums, f)
				}
			}
			row[i] = computeAgg(ag.fn, nums)
		}
		printTable([][]string{headers, row})
		fmt.Printf("(1 row(s))\n")
		return
	}

	// ---- Column projection ----
	var outIdxs []int
	var headers []string

	if len(colExprs) == 1 && colExprs[0] == "*" {
		for i, vc := range virtCols {
			outIdxs = append(outIdxs, i)
			headers = append(headers, virtTable.Columns[i].Name)
			_ = vc
		}
	} else {
		for _, expr := range colExprs {
			idx := colIndexVirt(virtCols, expr)
			if idx == -1 {
				fmt.Println("Column not found:", expr)
				return
			}
			outIdxs = append(outIdxs, idx)
			headers = append(headers, virtTable.Columns[idx].Name)
		}
	}

	// ---- ORDER BY ----
	if stmt.orderBy != "" {
		obIdx := colIndexVirt(virtCols, stmt.orderBy)
		if obIdx == -1 {
			fmt.Println("ORDER BY column not found:", stmt.orderBy)
			return
		}
		colType := virtCols[obIdx].col.Type
		sort.SliceStable(resultRows, func(i, j int) bool {
			a, b := resultRows[i][obIdx], resultRows[j][obIdx]
			if colType == "INT" || colType == "BIGINT" {
				ai, _ := strconv.ParseInt(a, 10, 64)
				bi, _ := strconv.ParseInt(b, 10, 64)
				if stmt.orderDesc {
					return ai > bi
				}
				return ai < bi
			}
			if colType == "FLOAT" || colType == "DOUBLE" {
				af, _ := strconv.ParseFloat(a, 64)
				bf, _ := strconv.ParseFloat(b, 64)
				if stmt.orderDesc {
					return af > bf
				}
				return af < bf
			}
			if stmt.orderDesc {
				return a > b
			}
			return a < b
		})
	}

	if stmt.limit >= 0 && stmt.limit < len(resultRows) {
		resultRows = resultRows[:stmt.limit]
	}

	outRows := [][]string{headers}
	for _, row := range resultRows {
		var out []string
		for _, idx := range outIdxs {
			v := decryptIfNeeded(virtCols[idx].col, row[idx])
			if v == nullSentinel {
				out = append(out, "NULL")
			} else {
				out = append(out, v)
			}
		}
		outRows = append(outRows, out)
	}
	printTable(outRows)
	fmt.Printf("(%d row(s))\n", len(resultRows))
}

// explainSelect prints the query plan without executing.
func explainSelect(stmt *selectStmt) {
	fmt.Println("Query Plan")
	fmt.Println("──────────────────────────────────────────")
	fmt.Printf("  Seq Scan on %q\n", stmt.fromTable)
	for _, j := range stmt.joins {
		fmt.Printf("  %s JOIN %q ON %s = %s  [nested-loop, O(N·M)]\n",
			j.kind, j.table, j.leftCol, j.rightCol)
	}
	if len(stmt.where) > 0 {
		fmt.Printf("  Filter: ")
		for i, c := range stmt.where {
			if i > 0 {
				fmt.Print(" AND ")
			}
			fmt.Printf("%s %s %s", c.col, c.op, c.val)
		}
		fmt.Println()
		fmt.Println("  Note: no indexes — full scan applies filter row-by-row")
	} else {
		fmt.Println("  No WHERE filter — all rows returned")
	}
	if stmt.orderBy != "" {
		dir := "ASC"
		if stmt.orderDesc {
			dir = "DESC"
		}
		fmt.Printf("  Sort: %s %s  [in-memory sort, O(N log N)]\n", stmt.orderBy, dir)
	}
	if stmt.limit >= 0 {
		fmt.Printf("  Limit: %d\n", stmt.limit)
	}
	fmt.Println("──────────────────────────────────────────")
	fmt.Println("Hint: Add indexes (not yet implemented) to avoid full scans on large tables.")
}

// helpers for virtual (joined) column tables
func resolveVirtCol(vcs []virtualCol, ref, defaultTable string) int {
	for i, vc := range vcs {
		fq := vc.tableAlias + "." + vc.col.Name
		if strings.EqualFold(fq, ref) || strings.EqualFold(vc.col.Name, unqualify(ref)) {
			return i
		}
	}
	return -1
}

func colIndexVirt(vcs []virtualCol, ref string) int {
	// Try qualified first
	for i, vc := range vcs {
		if strings.EqualFold(vc.tableAlias+"."+vc.col.Name, ref) {
			return i
		}
	}
	// Then unqualified
	uq := unqualify(ref)
	for i, vc := range vcs {
		if strings.EqualFold(vc.col.Name, uq) {
			return i
		}
	}
	return -1
}

func unqualify(ref string) string {
	if dot := strings.LastIndex(ref, "."); dot != -1 {
		return ref[dot+1:]
	}
	return ref
}

func countColName(vcs []virtualCol, name string) int {
	n := 0
	for _, vc := range vcs {
		if strings.EqualFold(vc.col.Name, name) {
			n++
		}
	}
	return n
}

func decryptIfNeeded(col Column, val string) string {
	if !col.Secure || val == nullSentinel {
		return val
	}
	plain, err := decryptValue(val)
	if err != nil {
		return "[decrypt error]"
	}
	return plain
}

type aggExpr struct {
	fn    string
	col   string
	label string
}

func computeAgg(fn string, nums []float64) string {
	if len(nums) == 0 {
		if fn == "COUNT" {
			return "0"
		}
		return "NULL"
	}
	switch fn {
	case "SUM":
		s := 0.0
		for _, v := range nums {
			s += v
		}
		return formatFloat(s)
	case "AVG":
		s := 0.0
		for _, v := range nums {
			s += v
		}
		return formatFloat(s / float64(len(nums)))
	case "MIN":
		m := nums[0]
		for _, v := range nums[1:] {
			if v < m {
				m = v
			}
		}
		return formatFloat(m)
	case "MAX":
		m := nums[0]
		for _, v := range nums[1:] {
			if v > m {
				m = v
			}
		}
		return formatFloat(m)
	}
	return "NULL"
}

func formatFloat(f float64) string {
	if f == math.Trunc(f) && math.Abs(f) < 1e15 {
		return strconv.FormatInt(int64(f), 10)
	}
	return strconv.FormatFloat(f, 'f', -1, 64)
}

// ---------------------------------------------------------------------------
// DELETE FROM
// ---------------------------------------------------------------------------

func deleteFrom(query string) {
	fields := strings.Fields(query)
	if len(fields) < 3 {
		fmt.Println("Syntax error: DELETE FROM <table> WHERE ...")
		return
	}
	tableName := fields[2]
	table, exists := database[tableName]
	if !exists {
		fmt.Println("Table not found:", tableName)
		return
	}

	whereIndex := strings.Index(strings.ToUpper(query), " WHERE ")
	if whereIndex == -1 {
		fmt.Println("Safety: WHERE clause is required for DELETE. Use DELETE FROM <table> WHERE 1=1 to delete all rows.")
		return
	}
	clause := strings.TrimSpace(query[whereIndex+7:])
	conditions := splitConditions(clause)

	var newRows [][]string
	deleted := 0
	table.mu.Lock()
	for _, row := range table.Rows {
		if matchesAll(table, row, conditions) {
			deleted++
		} else {
			newRows = append(newRows, row)
		}
	}
	table.Rows = newRows
	table.mu.Unlock()
	fmt.Printf("%d row(s) deleted.\n", deleted)
}

// ---------------------------------------------------------------------------
// WHERE — splitConditions kept for UPDATE/DELETE which still use string parsing
// (SELECT uses the new parser-based parseWhere)
// ---------------------------------------------------------------------------

func splitConditions(clause string) []condition {
	if clause == "" {
		return nil
	}
	// Split on AND (case-insensitive)
	re := regexp.MustCompile(`(?i)\bAND\b`)
	parts := re.Split(clause, -1)
	ops := []string{"!=", "<=", ">=", "=", "<", ">", " LIKE "}
	var conds []condition
	for _, p := range parts {
		p = strings.TrimSpace(p)
		matched := false
		for _, op := range ops {
			idx := strings.Index(strings.ToUpper(p), strings.ToUpper(op))
			if idx == -1 {
				continue
			}
			col := strings.TrimSpace(p[:idx])
			val := strings.TrimSpace(p[idx+len(op):])
			// Strip single quotes
			if len(val) >= 2 && val[0] == '\'' && val[len(val)-1] == '\'' {
				val = val[1 : len(val)-1]
			}
			conds = append(conds, condition{col, strings.TrimSpace(op), val})
			matched = true
			break
		}
		if !matched && p != "" {
			fmt.Println("Warning: unrecognized condition:", p)
		}
	}
	return conds
}

func matchesAll(table *Table, row []string, conds []condition) bool {
	for _, c := range conds {
		if !matchesCond(table, row, c) {
			return false
		}
	}
	return true
}

func matchesCond(table *Table, row []string, c condition) bool {
	// Resolve column — handle qualified names (table.col)
	colName := unqualify(c.col)
	idx := colIndex(table, colName)
	if idx == -1 {
		// Also try fully qualified
		idx = colIndex(table, c.col)
	}
	if idx == -1 {
		// 1=1 shorthand
		if c.col == "1" && c.val == "1" && c.op == "=" {
			return true
		}
		return false
	}
	col := table.Columns[idx]
	stored := row[idx]

	// IS NULL / IS NOT NULL
	if c.op == "IS_NULL" {
		return stored == nullSentinel
	}
	if c.op == "IS_NOT_NULL" {
		return stored != nullSentinel
	}

	if col.Secure && stored != nullSentinel {
		plain, err := decryptValue(stored)
		if err != nil {
			return false
		}
		stored = plain
	}

	if c.op == "LIKE" {
		return likeMatch(stored, c.val)
	}
	if c.op == "NOT_LIKE" {
		return !likeMatch(stored, c.val)
	}

	// Numeric compare when both sides look like numbers
	if an, ae := strconv.ParseFloat(stored, 64); ae == nil {
		if bn, be := strconv.ParseFloat(c.val, 64); be == nil {
			switch c.op {
			case "=":
				return an == bn
			case "!=":
				return an != bn
			case "<":
				return an < bn
			case ">":
				return an > bn
			case "<=":
				return an <= bn
			case ">=":
				return an >= bn
			}
		}
	}
	// String compare
	switch c.op {
	case "=":
		return stored == c.val
	case "!=":
		return stored != c.val
	case "<":
		return stored < c.val
	case ">":
		return stored > c.val
	case "<=":
		return stored <= c.val
	case ">=":
		return stored >= c.val
	}
	return false
}

// likeMatch supports % wildcard.
func likeMatch(s, pattern string) bool {
	if pattern == "%" {
		return true
	}
	if !strings.Contains(pattern, "%") {
		return s == pattern
	}
	parts := strings.Split(pattern, "%")
	pos := 0
	for i, part := range parts {
		if part == "" {
			continue
		}
		idx := strings.Index(s[pos:], part)
		if idx == -1 {
			return false
		}
		if i == 0 && idx != 0 {
			return false // pattern doesn't start with %
		}
		pos += idx + len(part)
	}
	// If pattern ends without %, s must be fully consumed
	if !strings.HasSuffix(pattern, "%") {
		return pos == len(s)
	}
	return true
}

// ---------------------------------------------------------------------------
// Pretty-print table
// ---------------------------------------------------------------------------

func printTable(rows [][]string) {
	if len(rows) == 0 {
		return
	}
	cols := len(rows[0])
	widths := make([]int, cols)
	for _, row := range rows {
		for i, cell := range row {
			if i < cols && utf8.RuneCountInString(cell) > widths[i] {
				widths[i] = utf8.RuneCountInString(cell)
			}
		}
	}

	sep := "+"
	for _, w := range widths {
		sep += strings.Repeat("-", w+2) + "+"
	}
	fmt.Println(sep)

	for ri, row := range rows {
		line := "|"
		for i := 0; i < cols; i++ {
			cell := ""
			if i < len(row) {
				cell = row[i]
			}
			pad := widths[i] - utf8.RuneCountInString(cell)
			line += " " + cell + strings.Repeat(" ", pad) + " |"
		}
		fmt.Println(line)
		if ri == 0 {
			fmt.Println(sep)
		}
	}
	fmt.Println(sep)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

func colIndex(table *Table, name string) int {
	for i, c := range table.Columns {
		if strings.EqualFold(c.Name, name) {
			return i
		}
	}
	return -1
}

func splitCSV(input string) []string {
	parts := strings.Split(input, ",")
	var result []string
	for _, p := range parts {
		result = append(result, strings.TrimSpace(p))
	}
	return result
}

func smartSplit(s string, sep rune) []string {
	var parts []string
	depth, start := 0, 0
	inQuote := false
	for i, ch := range s {
		switch {
		case ch == '\'' && !inQuote:
			inQuote = true
		case ch == '\'' && inQuote:
			inQuote = false
		case ch == '(' && !inQuote:
			depth++
		case ch == ')' && !inQuote:
			depth--
		default:
			if ch == sep && depth == 0 && !inQuote {
				parts = append(parts, s[start:i])
				start = i + 1
			}
		}
	}
	return append(parts, s[start:])
}

func runFile(fname string) {
	fname = strings.TrimSuffix(strings.TrimSpace(fname), ";")
	file, err := os.Open(fname)
	if err != nil {
		fmt.Println("Error opening file:", err)
		return
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	var buf strings.Builder
	lineNum := 0
	for scanner.Scan() {
		lineNum++
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "--") || strings.HasPrefix(line, "#") {
			continue
		}
		// Backslash meta-commands are valid inside script files too
		if strings.HasPrefix(line, `\`) {
			if buf.Len() > 0 {
				execute(strings.TrimSuffix(strings.TrimSpace(buf.String()), ";"))
				buf.Reset()
			}
			handleMeta(line)
			continue
		}
		// Skip lines that look like encrypted blobs (ROW/HMAC lines from .msql db files)
		if strings.HasPrefix(line, "ROW ") || strings.HasPrefix(line, "HMAC:") ||
			strings.HasPrefix(line, "TABLE ") || strings.HasPrefix(line, "COL ") ||
			strings.HasPrefix(line, "COUNTER ") || line == "END" {
			fmt.Printf("Error: '%s' is an encrypted MiniSQL database file, not a SQL script.\nTo switch databases use: \\connect %s\n", fname, fname)
			return
		}
		if buf.Len() > 0 {
			buf.WriteByte(' ')
		}
		buf.WriteString(line)
		if strings.HasSuffix(line, ";") {
			stmt := strings.TrimSuffix(strings.TrimSpace(buf.String()), ";")
			fmt.Printf("[%s:%d] %s\n", fname, lineNum, stmt)
			execute(stmt)
			buf.Reset()
		}
	}
	if buf.Len() > 0 {
		execute(strings.TrimSuffix(strings.TrimSpace(buf.String()), ";"))
	}
	if err := scanner.Err(); err != nil {
		fmt.Println("Read Error:", err)
	}
}

// ---------------------------------------------------------------------------
// Persistence — .msql format v2
// ---------------------------------------------------------------------------

func saveDB(fname string) {
	var sb strings.Builder
	sb.WriteString("# MiniSQL database — .msql format v3 (AES-256-GCM rows + HMAC-SHA512)\n")

	names := make([]string, 0, len(database))
	for n := range database {
		names = append(names, n)
	}
	sort.Strings(names)

	for _, tableName := range names {
		table := database[tableName]
		sb.WriteString("TABLE " + tableName + "\n")

		for _, col := range table.Columns {
			line := "COL " + col.Name
			if col.Type != "" {
				line += " " + col.Type
			}
			if col.AutoIter {
				line += " AUTOITER"
			}
			if col.AutoUUID {
				line += " AUTOUUID"
			}
			if col.AutoTS {
				if col.AutoTSUpdate {
					line += " AUTOTS_UPDATE"
				} else {
					line += " AUTOTS"
				}
			}
			if col.Secure {
				line += " SECURE"
			}
			if col.NotNull {
				line += " NOTNULL"
			}
			if col.Unique {
				line += " UNIQUE"
			}
			if col.Default != "" {
				line += " DEFAULT " + col.Default
			}
			sb.WriteString(line + "\n")
		}

		for colName, n := range table.AutoCounters {
			sb.WriteString(fmt.Sprintf("COUNTER %s %d\n", colName, n))
		}

		for _, row := range table.Rows {
			esc := make([]string, len(row))
			for i, v := range row {
				esc[i] = strings.ReplaceAll(v, "|", "\\|")
			}
			plainRow := strings.Join(esc, "|")
			enc, err := aesGCMEncrypt([]byte(plainRow))
			if err != nil {
				fmt.Println("Error encrypting row:", err)
				return
			}
			sb.WriteString("ROW " + enc + "\n")
		}

		sb.WriteString("END\n\n")
	}

	body := sb.String()
	sig := signContent([]byte(body))
	full := body + hmacMarker + sig + "\n"

	// Atomic write: write to temp file, fsync, rename
	tmp := fname + ".tmp"
	f, err := os.OpenFile(tmp, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0600)
	if err != nil {
		fmt.Println("Write Error:", err)
		return
	}
	if _, err := f.WriteString(full); err != nil {
		f.Close()
		os.Remove(tmp)
		fmt.Println("Write Error:", err)
		return
	}
	if err := f.Sync(); err != nil { // fsync before rename
		f.Close()
		os.Remove(tmp)
		fmt.Println("Sync Error:", err)
		return
	}
	f.Close()
	if err := os.Rename(tmp, fname); err != nil {
		fmt.Println("Rename Error:", err)
		return
	}
	fmt.Printf("DB saved → %s\n", fname)
}

func loadDB(fname string) {
	raw, err := os.ReadFile(fname)
	if err != nil {
		if os.IsNotExist(err) {
			return
		}
		fmt.Println("Load Error:", err)
		return
	}

	// Detect format version
	firstLine := ""
	if nl := strings.Index(string(raw), "\n"); nl != -1 {
		firstLine = strings.TrimSpace(string(raw[:nl]))
	}
	isV3 := strings.Contains(firstLine, "format v3")
	isV2 := strings.Contains(firstLine, "format v2")

	var body []byte
	if isV3 {
		// Verify HMAC before trusting any content
		body, err = verifyAndStrip(raw)
		if err != nil {
			fatalf("database integrity check failed: %v\nThe file may have been tampered with.", err)
		}
	} else if isV2 {
		// Legacy plaintext format — load as-is (rows are stored unencrypted)
		body = raw
		fmt.Println("Note: legacy plaintext format detected. Re-save to upgrade to v3.")
	} else {
		body = raw
	}

	var cur *Table
	var curName string

	for lineNum, line := range strings.Split(string(body), "\n") {
		line = strings.TrimSpace(line)
		if line == "" || strings.HasPrefix(line, "#") || strings.HasPrefix(line, hmacMarker) {
			continue
		}

		switch {
		case strings.HasPrefix(line, "TABLE "):
			if cur != nil && curName != "" {
				database[curName] = cur
			}
			curName = strings.TrimSpace(strings.TrimPrefix(line, "TABLE "))
			cur = &Table{Rows: [][]string{}, AutoCounters: map[string]int{}}

		case strings.HasPrefix(line, "COL "):
			if cur == nil {
				fmt.Printf("Warning: COL outside TABLE at line %d\n", lineNum+1)
				continue
			}
			tokens := tokenizeQuoteAware(strings.TrimPrefix(line, "COL "))
			if len(tokens) == 0 {
				continue
			}
			col := Column{Name: tokens[0]}
			for i := 1; i < len(tokens); i++ {
				up := strings.ToUpper(tokens[i])
				switch {
				case validTypes[up]:
					if col.Type == "" {
						col.Type = up
					}
				case up == "AUTOITER":
					col.AutoIter = true
				case up == "AUTOUUID":
					col.AutoUUID = true
				case up == "AUTOTS":
					col.AutoTS = true
				case up == "AUTOTS_UPDATE":
					col.AutoTS = true
					col.AutoTSUpdate = true
				case up == "SECURE":
					col.Secure = true
				case up == "NOTNULL":
					col.NotNull = true
				case up == "UNIQUE":
					col.Unique = true
				case up == "DEFAULT":
					if i+1 < len(tokens) {
						i++
						val := tokens[i]
						if len(val) >= 2 && val[0] == '\'' && val[len(val)-1] == '\'' {
							val = val[1 : len(val)-1]
						}
						col.Default = val
					}
				}
			}
			cur.Columns = append(cur.Columns, col)

		case strings.HasPrefix(line, "COUNTER "):
			if cur == nil {
				continue
			}
			parts := strings.Fields(strings.TrimPrefix(line, "COUNTER "))
			if len(parts) == 2 {
				if n, err2 := strconv.Atoi(parts[1]); err2 == nil {
					cur.AutoCounters[parts[0]] = n
				}
			}

		case strings.HasPrefix(line, "ROW "):
			if cur == nil {
				continue
			}
			payload := strings.TrimPrefix(line, "ROW ")

			var plainRow string
			if isV3 {
				// Decrypt the row blob
				pt, derr := aesGCMDecrypt(payload)
				if derr != nil {
					fmt.Printf("Error decrypting row at line %d: %v\n", lineNum+1, derr)
					continue
				}
				plainRow = string(pt)
			} else {
				// v2 / legacy: payload is already plaintext pipe-separated
				plainRow = payload
			}

			rawCells := splitPipe(plainRow)
			row := make([]string, len(rawCells))
			for i, cell := range rawCells {
				row[i] = strings.ReplaceAll(cell, "\\|", "|")
			}
			cur.Rows = append(cur.Rows, row)

		case line == "END":
			if cur != nil && curName != "" {
				database[curName] = cur
			}
			cur = nil
			curName = ""
		}
	}

	if cur != nil && curName != "" {
		database[curName] = cur
	}

	fmt.Printf("DB loaded from %s (%d table(s))\n", fname, len(database))
}

func splitPipe(input string) []string {
	var parts []string
	var cur strings.Builder
	for i := 0; i < len(input); i++ {
		if input[i] == '|' && (i == 0 || input[i-1] != '\\') {
			parts = append(parts, cur.String())
			cur.Reset()
		} else {
			cur.WriteByte(input[i])
		}
	}
	return append(parts, cur.String())
}