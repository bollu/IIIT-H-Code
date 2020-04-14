import sys

class Action:
    def __init__(self, name, params):
        self.name = name
        self.params = params

    def __repr__(self):
        return "%s(%s)" % (self.name, ", ".join(self.params))

    def __str__(self): return self.__repr__()

class Operation:
    def __init__(self, lhs, rhs1, op, rhs2):
        self.lhs = lhs
        self.rhs1 = rhs1
        self.op = op
        self.rhs2 = rhs2

    def __repr__(self):
        return "%s := %s %s %s" % (self.lhs, self.rhs1, self.op, self.rhs2)

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

                rhs1 = None
                rhs2 = None
                op = None
                if rhs.find("+") != -1:
                    rhs1 = rhs[:rhs.find("+")].strip()
                    rhs2 = rhs[rhs.find("+")+1:].strip()
                    op = "+"
                elif rhs.find("-") != -1:
                    rhs1 = rhs[:rhs.find("-")].strip()
                    rhs2 = rhs[rhs.find("-")+1:].strip()
                    op = "-"
                elif rhs.find("*") != -1:
                    rhs1 = rhs[:rhs.find("*")].strip()
                    rhs2 = rhs[rhs.find("*")+1:].strip()
                    op = "*"
                elif rhs.find("/") != -1:
                    rhs1 = rhs[:rhs.find("/")].strip()
                    rhs2 = rhs[rhs.find("/")+1:].strip()
                    op = "/"
                else:
                    raise RuntimeError("expected + - * / as operation. |%s|" % (lines[i], ))

                assert rhs1 is not None
                assert rhs2 is not None
                assert op is not None

                t.add_instr(Operation(lhs, rhs1, op, rhs2))
            else:
                actname = lines[i].split("(")[0].strip()
                actps = lines[i].split("(")[1].split(")")[0].split(",")
                actps = [a.strip() for a in actps]
                t.add_instr(Action(actname, actps))
            i += 1
        inp.add_transaction(t)
    return inp



class State:
    def __init__(self, disk):
        self.disk = disk
        self.var2mem = {}
        self.mem = {}
    def print(self):
        if not self.mem:
            print ("")
        else:
            # print("MEMORY")
            memks = list(self.mem)
            memks.sort()
            print(" ".join(["%s %s" % (k, self.mem[k]) for k in memks]))

        diskks = list(self.disk)
        diskks.sort()
        print(" ".join(["%s %s" % (k, self.disk[k]) for k in diskks]))

NRoundRobin = int(sys.argv[2])
inp = parse()

def evalop(op, mem):
    p1 = mem[op.rhs1] if op.rhs1 in mem else int(op.rhs1)
    p2 = mem[op.rhs2] if op.rhs2 in mem else int(op.rhs2)
    if op.op == "+": mem[op.lhs] = p1 + p2
    elif op.op == "-": mem[op.lhs] = p1 - p2
    elif op.op == "*": mem[op.lhs] = p1 * p2
    elif op.op == "/": mem[op.lhs] = p1 / p2
    else: raise RuntimeError("unknown operation: |%s|" % (inst, ))


with open("20161105_1.txt", "w") as of:
    of.write("foobar");
    tcursors = [0 for t in inp.transactions]
    state = State(inp.elems)
    # import pudb; pudb.set_trace()
    while not all([tcursors[i] == len(t.instrs) + 1 for (i, t) in enumerate(inp.transactions)]):
        for tix in range(len(inp.transactions)):
            txn = inp.transactions[tix]
            for _ in range(NRoundRobin):
                if tcursors[tix] == 0:
                    print("<START %s>" % (txn.name))
                    state.print()

                if tcursors[tix] == len(txn.instrs) + 1: break
                elif tcursors[tix] == len(txn.instrs): 
                    print("<COMMIT %s>" % (txn.name))
                    tcursors[tix] += 1
                else:
                    inst = txn.instrs[tcursors[tix]]
                    if isinstance(inst, Operation):
                        evalop(inst, state.mem)
                        state.print()
                    elif isinstance(inst, Action):
                        if inst.name == "READ":
                            var = inst.params[0]
                            memname = inst.params[1] 
                            state.var2mem[var] = memname
                            state.mem[memname] = int(state.disk[var])
                            state.print()
                        elif inst.name == "WRITE":
                            var = inst.params[0]
                            memname = inst.params[1] 
                            state.disk[memname] = state.mem[memname]
                            state.print()
                        elif inst.name == "OUTPUT":
                            print(inst)
                        else: raise RuntimeError("unknown action: |%s|" % (inst, ))
                    else:
                        raise RuntimeError("unknown type of instructon: |%s|" % (inst, ))
                    tcursors[tix] += 1

print(inp)
