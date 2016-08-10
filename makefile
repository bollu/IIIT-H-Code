CC=clang -Wall -Werror
osAssign1Build: os-assign-1.c
	$(CC) os-assign-1.c -o bin/os-assign-1

osAssign1Run: osAssign1Build
	@echo "*** Running ***"
	@./bin/os-assign-1
