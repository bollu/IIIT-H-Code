.PHONY: compile test clean client server
compile: clean
	javac *.java

test:
	java Server 8000
	java Client 127.0.0.1 8000

clean:
	-rm *.class

server: compile
	java Server

client: compile
	java Client < input
