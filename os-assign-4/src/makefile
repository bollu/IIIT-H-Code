all: q1 q2

q1: mkbin q1.c
	gcc -Wall -Werror q1.c -o bin/q1

q2: mkbin q2.c
	gcc -Wall -Werror q2.c -o bin/q2

mkbin:
	@mkdir -p bin

zip:
	zip q1.c -out 20161105_assignment4.zip
