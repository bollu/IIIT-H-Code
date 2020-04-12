import sys

class Action:
    def __init__(self, name, params):
        self.name = name
        self.params = params

    def __repr__(self):
        return "%s(%s)" % (self.name, ", ".join(self.params))

    def __str__(self): return self.__repr__()

class Operation:
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return "%s := %s" % (self.lhs, self.rhs)

    def __str__(self): return self.__repr__()

class Transaction:
    def __init__(self, name):
        self.name = name
        self.instrs = []

    def add_instr(self, instr):
        self.instrs.append(instr)

    def __repr__(self):
        s = ""
        s += "%s %s\n" % (self.name, len(self.instrs))
        s += "\n".join([str(a) for a in self.instrs])
        return s

    def __str__(self): return self.__repr__()

class Input:
    def __init__(self, elems):
        self.elems = elems
        self.transactions = []
    def add_transaction(self, t):
        self.transactions.append(t)


    def __repr__(self):
        s = ""
        s += " ".join(["%s %s" % (name, self.elems[name]) for name in self.elems])
        s += "\n\n"
        s += "\n\n".join([str(t) for t in self.transactions])
        return s

    def __str__(self): return self.__repr__()



def parse():
    with open(sys.argv[1], "r") as f:
        lines = f.readlines()

    raw_elems = lines[0].strip().split(" ")
    elems = {}
    i = 0
    while i < len(raw_elems):
        elems[raw_elems[i]] = raw_elems[i+1]; i += 2
    inp = Input(elems)

    i = 1
    while i < len(lines):
        assert lines[i].strip() == ""
        i += 1
        (tname, numts) = lines[i].strip().split()
        numts = int(numts)
        t = Transaction(tname)
        i += 1
        for j in range(numts):
            if lines[i].find(":=") != -1:
                lhs = lines[i].split(":=")[0].strip()
                rhs = lines[i].split(":=")[1].strip()
                t.add_instr(Operation(lhs, rhs))
            else:
                actname = lines[i].split("(")[0]
                actps = lines[i].split("(")[1].split(")")[0].split(",")
                t.add_instr(Action(actname, actps))
            i += 1
        inp.add_transaction(t)
    return inp


N = int(sys.argv[2])
inp = parse()

print(inp)
