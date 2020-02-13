.PHONY: compile test clean
compile: clean
	javac *.java

test:
	java Server 8000
	java Client 127.0.0.1 8000

clean:
	-rm *.class
