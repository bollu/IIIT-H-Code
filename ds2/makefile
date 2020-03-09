.PHONY: compile test cln client server zip
compile: cln
	javac *.java

cln:
	-rm *.class

server: compile
	java Server 1900

client: compile
	java Client 127.0.0.1 1900 < input

zip: 
	-rm -r 20161105/
	mkdir -p 20161105
	cp *.java 20161105
	zip -r 20161105.zip 20161105
