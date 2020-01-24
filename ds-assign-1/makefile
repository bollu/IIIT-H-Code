EXECS=mpi_hello_world
MPICXX?=mpicxx

20161105_1: 20161105_1.cpp
	${MPICXX} -std=c++17 -O0 -o 20161105_1 20161105_1.cpp -fsanitize=address -fsanitize=undefined -g

20161105_2: 20161105_2.cpp
	# ${MPICXX} -std=c++17 -O0 -o 20161105_2 20161105_2.cpp -fsanitize=address -fsanitize=undefined -g
	${MPICXX} -std=c++17 -o 20161105_2 20161105_2.cpp -g

avg: avg.c
	${MPICXX} -std=c++17 -o avg avg.c -fsanitize=address -fsanitize=undefined -g

zip:
	mkdir 20161105
	cp 20161105_1.cpp 20161105_2.cpp README.md makefile 20161105/
	zip -r 20161105.zip 20161105
