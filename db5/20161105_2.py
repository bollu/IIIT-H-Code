import sys
with open(sys.argv[1], "r") as f:
    lines = f.readlines()
    words0 = [w.strip() for w in lines[0].strip().split()]
    START = []
    for i in range(0, len(words0), 2):
        START.append((words0[i], int(words0[i+1])))

print(START)

