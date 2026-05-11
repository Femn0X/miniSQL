CREATE TABLE prices (
 id INT AUTOITER, 
 username UNIQUE TEXT NOT NULL,
 pass SECURE TEXT NOT NULL,
 login_time AUTO TIMESTAMP
);
INSERT INTO prices VALUES ('Luca','2112','2007-12-21 00:00:00');   
INSERT INTO prices VALUES ('Admin','admin','9999-12-31 23:59:59');
SELECT * from prices;
