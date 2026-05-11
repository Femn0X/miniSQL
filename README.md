# MiniSQL

A lightweight, embeddable SQL-like database engine written in pure Go. Stores data in a single `.msql` file with optional AES-256-GCM column-level encryption.

## Features

- **No dependencies** — pure Go standard library only
- **Persistent storage** — all data saved to `db.msql` automatically on exit
- **Encrypted columns** — mark any column `SECURE` for transparent AES-256-GCM encryption
- **Type system** — `INT`, `BIGINT`, `FLOAT`, `DOUBLE`, `TEXT`, `VARCHAR`, `CHAR`, `BOOL`, `DATE`, `TIMESTAMP`, `BLOB`
- **Column modifiers** — `AUTOITER`, `SECURE`, `NOT NULL`, `DEFAULT <value>`
- **Rich WHERE** — supports `=`, `!=`, `<`, `>`, `<=`, `>=`, `LIKE` (with `%`), and `AND`
- **`ORDER BY`** — numeric-aware ascending/descending sort
- **`LIMIT`** — cap result set size
- **`UPDATE`** — modify existing rows with multi-column SET
- **`DROP TABLE`** — remove a table
- **`SHOW TABLES`** — list all tables with row/column counts
- **`DESCRIBE`** — inspect table schema
- **Multi-line input** — statements can span multiple lines in the REPL; terminated by `;`
- **Script mode** — pass a `.sql` file as argument to execute in batch
- **Pretty output** — box-drawing ASCII table renderer

## Installation

```bash
git clone https://github.com/Femn0X/miniSQL
cd minisql
go build -o minisql .
```

Requires Go 1.21 or later.

## Usage

### Interactive REPL

```
./minisql
```

```
MiniSQL v1.2.0  —  type HELP for commands, EXIT to quit
────────────────────────────────────────────────────────────
sql>
```

### Script mode

```bash
./minisql seed.sql
```

Lines beginning with `--` are treated as comments. Statements must end with `;`.

## SQL Reference

### CREATE TABLE

```sql
CREATE TABLE users (
    id        INT       NOT NULL AUTOITER,
    username  VARCHAR   NOT NULL,
    password  TEXT      SECURE NOT NULL,
    score     DOUBLE    DEFAULT 0.0,
    active    BOOL      DEFAULT true,
    joined    DATE,
    updated   TIMESTAMP,
    data      BLOB
);
```

### INSERT INTO

```sql
-- AUTOITER columns can be omitted or passed as NULL
INSERT INTO users VALUES (alice, s3cr3t, 9.5, true, 2024-01-15, NULL, NULL);

-- Timestamps must be single-quoted (contain a space)
INSERT INTO users VALUES (bob, pass123, 7.0, false, 2024-03-01, '2024-03-01 09:00:00', NULL);
```

### SELECT

```sql
SELECT * FROM users;
SELECT id, username, score FROM users WHERE active = true;
SELECT * FROM users WHERE score >= 7.5 AND active = true ORDER BY score DESC LIMIT 10;
SELECT * FROM users WHERE username LIKE al%;
```

### UPDATE

```sql
UPDATE users SET score = 10.0, active = true WHERE id = 1;
```

### DELETE

```sql
DELETE FROM users WHERE id = 3;
-- Delete all rows (explicit intent required):
DELETE FROM users WHERE 1=1;
```

### DROP TABLE

```sql
DROP TABLE users;
```

### SHOW TABLES

```sql
SHOW TABLES
```

### DESCRIBE

```sql
DESCRIBE users
```

## Column Types

| Type        | Description                              |
|-------------|------------------------------------------|
| `INT`       | 64-bit signed integer                    |
| `BIGINT`    | Alias for INT                            |
| `FLOAT`     | 32-bit floating point                    |
| `DOUBLE`    | 64-bit floating point                    |
| `TEXT`      | Unlimited UTF-8 string                   |
| `VARCHAR`   | Alias for TEXT (SQL compatibility)       |
| `CHAR`      | Single Unicode character                 |
| `BOOL`      | `true`/`false`/`1`/`0`/`yes`/`no`       |
| `DATE`      | `YYYY-MM-DD`                             |
| `TIMESTAMP` | `YYYY-MM-DD HH:MM:SS` (quote in VALUES) |
| `BLOB`      | Even-length hex string                   |

## Column Modifiers

| Modifier         | Effect                                                    |
|------------------|-----------------------------------------------------------|
| `AUTOITER`       | Auto-incrementing integer; can be omitted in INSERT       |
| `SECURE`         | Value encrypted with AES-256-GCM before storage           |
| `NOT NULL`       | Rejects `NULL` and empty values                           |
| `DEFAULT <val>`  | Used when the value is `NULL` or omitted                  |

## Encryption

MiniSQL generates a 256-bit key on first run and stores it in `db.msql.key` (mode `0600`). Keep this file alongside your database — without it, `SECURE` columns cannot be decrypted.

> **Warning:** `db.msql.key` is plain hex on disk. Protect it with filesystem permissions or external secrets management in production.

## WHERE Operators

| Operator | Meaning        |
|----------|----------------|
| `=`      | Equal          |
| `!=`     | Not equal      |
| `<`      | Less than      |
| `>`      | Greater than   |
| `<=`     | Less or equal  |
| `>=`     | Greater/equal  |
| `LIKE`   | Pattern match (`%` wildcard) |

Multiple conditions are joined with `AND`.

## File Format

Data is stored in a compact `.msql` format (`db.msql`) and is not intended for manual editing:

```
# MiniSQL database — .msql format v2
TABLE users
COL id INT AUTOITER NOTNULL
COL username VARCHAR NOTNULL
COL password TEXT SECURE NOTNULL
COUNTER id 3
ROW 1|alice|<hex-ciphertext>
ROW 2|bob|<hex-ciphertext>
END
```

Pipe characters inside values are escaped as `\|`.

## License

ISC — see [LICENSE](LICENSE).
