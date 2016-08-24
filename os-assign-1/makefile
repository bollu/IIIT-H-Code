CC=gcc -Wall -Werror

all: q1 q2

q1: q1.c
	@mkdir -p bin
	$(CC) q1.c -o bin/q1
	rm -rf Assignment/

q2: q2.c
	@mkdir -p bin
	$(CC) q2.c -o bin/q2
	rm -rf Assignment/

zip:
	tar -czvf 20161105_os_assign_1.tar.gz q1.c q2.c  README.md makefile testfile 
