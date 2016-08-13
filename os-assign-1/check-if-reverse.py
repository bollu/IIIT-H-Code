#!/usr/bin/env python
import sys

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("usage: %s [inputfile] [outputfile]" % sys.argv[0])
    else:
        f1 = open(sys.argv[1], "rb").read()
        f2 = open(sys.argv[2], "rb").read()

        print ("Success" if f1[::-1] == f2 else "Failure")
