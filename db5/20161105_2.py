import sys
import copy
# http://www.mathcs.emory.edu/~cheung/Courses/554/Syllabus/6-logging/undo2.html

class StartTxn:
    def __init__(self, txn): self.txn = txn
    def get_tnxs(self): return [self.txn]
    def __repr__(self): return "<START %s>" %(self.txn, )
    def __str__(self): return self.__repr__()

class Txn:
    def __init__(self, txn, var, val):
        self.txn = txn; self.var = var; self.val = val;
    def get_tnxs(self): return [self.txn]
    def __repr__(self): return "<%s, %s, %s>"%(self.txn, self.var, self.val)
    def __str__(self): return self.__repr__()

class StartCkpt:
    def __init__(self, txns): self.txns = txns
    def get_tnxs(self): return self.txns
    def __repr__(self): return "<START CKPT (%s)>"%(", ".join([str(t) for t in self.txns]), )
    def __str__(self): return self.__repr__()

class CommitTxn: 
    def __init__(self, txn): self.txn = txn
    def get_tnxs(self): return [self.txn]
    def __repr__(self): return "<COMMIT %s>" % (self.txn, )
    def __str__(self): return self.__repr__()

class EndCkpt:
    def __init__(self): pass
    def get_tnxs(self): return []
    def __repr__(self): return "<END CKPT>"
    def __str__(self): return self.__repr__()

with open(sys.argv[1], "r") as f:
    lines = f.readlines()
    words0 = [w.strip() for w in lines[0].strip().split()]
    START = []
    for i in range(0, len(words0), 2):
        START.append((words0[i], int(words0[i+1])))

    commands = []
    for l in lines[2:]:
        l = l[1:-2] # remove <>
        # <START CKPT (T1, T3)>
        if l.find("START CKPT") != -1: 
            txns = [t.strip() for t in l.split("(")[1].split(")")[0].split(",")]
            commands.append(StartCkpt(txns))
        # <START T1>
        elif l.find("START") != -1: 
            commands.append(StartTxn(l.split()[1].strip()))
        # <COMMIT T3>
        elif l.split()[0] == "COMMIT": commands.append(CommitTxn(l.split()[1].strip()))
        # <END CKPT>
        elif l.find("END CKPT") != -1: commands.append(EndCkpt())
        else: # <T2, B, 10>
            [txn, var, val] = l.split(",")
            commands.append(Txn(txn, var, val))

# print(START)
# print(commands)

ALLTXNS = []
for c in commands: ALLTXNS.extend(c.get_tnxs())
ALLTXNS = set(ALLTXNS)
# print(ALLTXNS)

UNCOMMITEDTXNS = copy.deepcopy(ALLTXNS)
for c in commands: 
    if isinstance(c, CommitTxn): UNCOMMITEDTXNS.remove(c.txn)

for i in range(len(commands)-1, -1, -1): 
    c = commands[i]
    if not isinstance(c, Txn): continue
    if c in UNCOMMITEDTXNS: ALLTXNS[c.var] = c.val

print(" ".join([" ".join([var, str(val)]) for (var, val) in START]))
