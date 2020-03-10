.PHONY: zip
main: main.cpp makefile
	g++ -std=c++11 main.cpp -o main -fsanitize=undefined -fsanitize=address -g -O0 -DDEBUG

zip: main.cpp README.md makefile
	zip 20161105_Assignment3.zip main.cpp README.md 
