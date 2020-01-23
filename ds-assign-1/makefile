EXECS=mpi_hello_world
MPICXX?=mpicxx

20161105_1: 20161105_1.cpp
	${MPICXX} -std=c++17 -O0 -o 20161105_1 20161105_1.cpp -fsanitize=address -fsanitize=undefined -g


20161105_2: 20161105_2.cpp

avg: avg.c
	${MPICXX} -std=c++17 -o avg avg.c -fsanitize=address -fsanitize=undefined -g


