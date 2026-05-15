CREATE TABLE users IF NOT EXISTS (
 id INT AUTOITER, 
 username UNIQUE TEXT NOT NULL
);
INSERT INTO users VALUES ('user1');
INSERT INTO users VALUES ('Admin');
SELECT * from users;
