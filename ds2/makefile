.PHONY: compile test cln client server
compile: cln
	javac *.java

test:
	java Server 8000
	java Client 127.0.0.1 8000

cln:
	-rm *.class

server: compile
	java Server

client: compile
	java Client < input
