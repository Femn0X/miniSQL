CREATE TABLE users (
 id INT AUTOITER, 
 username UNIQUE TEXT NOT NULL
);
INSERT users VALUES ('user1');
INSERT INTO users VALUES ('Admin');
SELECT * from users;
