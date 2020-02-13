.PHONY: compile test cln client server
compile: cln
	javac *.java

cln:
	-rm *.class

server: compile
	java Server 1900

client: compile
	java Client 127.0.0.1 1900 < input
