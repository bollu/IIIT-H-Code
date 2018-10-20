CC=clang
CC_SAFE=$(CC) -Wall -Werror


build:
	@mkdir -p bin/
	$(CC_SAFE) shell.c context.c parser.c linenoise.c -o bin/shell
	$(CC) crash.c -o bin/crash

run: build
	@echo "--"
	@./bin/shell

zip:
	zip  20161105_assign_3.zip  shell.c crash.c makefile  context.c context.h parser.c parser.h common.h README.md

all: build run
