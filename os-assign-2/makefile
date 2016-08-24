CC=clang -Wall -Werror

all: build run

build:
	@mkdir -p bin/
	$(CC) shell.c -o bin/shell

run: build
	@echo "--"
	@./bin/shell

zip:
	zip -r 20161105_assign_2.zip *
