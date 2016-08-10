#!/usr/bin/env python
import sys

if len(sys.argv) != 3:
    print("usage: %s [inputfile] [outputfile]" % sys.argv[0])
f1 = open(sys.argv[1]).read()
f2 = open(sys.argv[2]).read()

print ("Success" if f1[::-1] == f2 else "Failure")
