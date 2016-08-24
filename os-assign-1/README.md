files `q1.c` and `q2.c` contain the C files corresponding to the code

run both `q1` and `q2` by passing input file name as parameter.

For example

```
$ q1 testfile.txt
$ q2 testfile.txt
```

`q1` creates the output fie as `output_<input filename>` inside the `Assignment`
directory which it creates

`q2` reads the file from the `Assignment/` folder

Makefile
========

The makefile is bundled along with the code. To build, run
```
$ make build
```

To run, use

```
$ ./bin/q1 testfile
$ ./bin/q2 testfile
```
