#!/usr/bin/env python3
import sys
import os
import os.path
import csv
import logging
import sqlparse
import numpy as np

logging.basicConfig(filename='db.log', level=logging.DEBUG)

BASEPATH='./files/'

class Table:
    def __init__(self, name, path, cols, rows):
        self.name = name
        self.path = path
        self.cols = cols
        self.rows = np.asarray(rows)

        for (i, row) in enumerate(self.rows):
            if len(row) != len(cols):
                logging.error("table:%s | row: %s| has length %s, expected %s"
                              % (name, i, len(cols)))
                raise RuntimeError("malformed table: %s(%s). Aborting" %
                                   (name,path))

class DB:
    def __init__(self, metapath, tables):
        self.metapath = metapath
        self.tables = tables
        for (i, k) in enumerate(self.tables):
            if not isinstance(self.tables[k], Table):
                logging.error("DB received non-table object at index %s: %s" % 
                              (i, t))
                raise RuntimeError("DB received non-table object at index %s: %s" % 
                              (i, t))


# path -> table
def load_table(name, path, cols):
    with open(path, "r") as f: rows=list(csv.reader(f, delimiter=','))
    logging.debug("table\n  path:|%s|\n  cols:|%s|\n  rows:\n%s\n--\n" %
                  (path, cols, rows))
    return Table(name, path, cols, rows)


# path -> DB
def load_db(path):
    with open(path, "r") as f: ls = f.readlines()
    ls = [l.strip() for l in ls]
    logging.debug("metadata file:\n%s\n--\n" % ls)

    tables = {}
    while ls:
        assert(ls[0] == "<begin_table>")
        i = 0
        while ls[i] != "<end_table>": i += 1
        #  ls[0] = begin_table
        # ls[1] = TABLE NAME
        # ls[2..i-1] = TABLE column names
        #  ls[i] = end_table
        name = ls[1]; cols=ls[2:i]; ls=ls[i+1:]
        tables[name] = load_table(name, 
                                 os.path.join(BASEPATH, name + ".csv"), cols)
    return DB(path, tables)



COLUMN_SELECT_ALL = "column_select_all"
COLUMN_SELECT_MAX = "column_select_max"
COLUMN_SELECT_MIN = "column_select_min"
COLUMN_SELECT_AVG = "column_select_avg"
COLUMN_SELECT_STAR = "column_select_star"
COLUMN_SELECT_DISTINCT = "column_select_distinct"
class ColumnSelector:
    def __init__(self, col, ty):
        self.col = col
        self.ty = ty
        assert self.ty in [COLUMN_SELECT_ALL, COLUMN_SELECT_AVG,
                           COLUMN_SELECT_MAX, COLUMN_SELECT_MIN,
                           COLUMN_SELECT_STAR, COLUMN_SELECT_DISTINCT]
        if self.ty != COLUMN_SELECT_STAR: assert self.col is not None

    def __repr__(self):
        return "%s(%s)" % (self.ty, self.col)

class Query:
    def __init__(self, tables, cols, filters):
        self.tables = tables
        self.cols = cols
        self.filters = filters

    def __repr__(self):
        return "tables: %s | cols: %s | filters: %s" % (self.tables, self.cols, self.filters)

class Filter: pass


class FilterAnd(Filter):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
        assert(isinstance(self.lhs, (Identifier, Int, Filter)))
        assert(isinstance(self.rhs, (Identifier, Int, Filter)))

    def __repr__(self):
        return "(OR %s %s)" % (self.lhs.__repr__(), self.rhs.__repr__())

class FilterOr(Filter):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
        assert(isinstance(self.lhs, (Identifier, Int, Filter)))
        assert(isinstance(self.rhs, (Identifier, Int, Filter)))

    def __repr__(self):
        return "(OR %s %s)" % (self.lhs.__repr__(), self.rhs.__repr__())


FILTER_RELATIONAL_EQ = "filter_relational_eq"
FILTER_RELATIONAL_GEQ = "filter_relational_geq"
FILTER_RELATIONAL_LEQ = "filter_relational_leq"
FILTER_RELATIONAL_LT = "filter_relational_lt"
FILTER_RELATIONAL_GT = "filter_relational_gt"
class FilterRelational(Filter):
    def __init__(self, lhs, ty, rhs):
        assert(isinstance(lhs, (Identifier, Int, Filter)))
        assert(isinstance(rhs, (Identifier, Int, Filter)))
        self.lhs = lhs
        self.ty = ty
        self.rhs = rhs
        assert self.ty in [FILTER_RELATIONAL_LT, FILTER_RELATIONAL_LEQ,
                           FILTER_RELATIONAL_EQ, FILTER_RELATIONAL_GT,
                           FILTER_RELATIONAL_GEQ]
        
    def __repr__(self):
        return "(%s %s %s)" % (self.ty, self.lhs.__repr__(), self.rhs.__repr__())

class Identifier:
    def __init__(self, s): self.s = s; assert(isinstance(s, str))
    def __repr__(self): return "Identifier(%s)" % (self.s, )

class Int:
    def __init__(self, i): self.i = i; assert(isinstance(i, int))
    def __repr__(self): return "Int(%s)" % (self.i, )



# parse a single column selector
def parse_col_selector(s):
    if type(s) == sqlparse.sql.Identifier:
        return ColumnSelector(str(s), COLUMN_SELECT_ALL)
    elif type(s) == sqlparse.sql.Function:
        print(s)
        name = s[0].value; parens=s[1]
        if type(parens) != sqlparse.sql.Parenthesis: 
            raise RuntimeError("expected parenthesis around column filter: %s" % (s))
        col = parens[1].value
        print("name: |%s| col: |%s|" % (name, col))

        if name == "max":
            return ColumnSelector(col, COLUMN_SELECT_MAX)
        elif name == "min":
            return ColumnSelector(col, COLUMN_SELECT_MIN)
        elif name == "avg":
            return ColumnSelector(col, COLUMN_SELECT_AVG)
        elif name == "distinct":
            return ColumnSelector(col, COLUMN_SELECT_DISTINCT)
        else:
            raise RuntimeError("unknown column filter function: |%s|" % (s, ))
    else: # neither identifier nor function
        print(s)
        raise RuntimeError("unknown column selector: |%s:%s" % (s, type(s)))


# parse list of sqlparse, return list of column names
# sqlparse.sql.query -> list<ColumnSelector>
def parse_col_selectors(l):
    # filter whitespace
    if type(l) == sqlparse.sql.Identifier: return [parse_col_selector(l)]
    elif type(l) == sqlparse.sql.IdentifierList:
        l = [x for x in l if not x.is_whitespace]
        cs = []
        while l:
          cs.append(parse_col_selector(l[0])); l = l[1:]
          # l still has more. ensure there was comma next.
          # We need , <QUERY>
          if l:
              if str(l[0]) != ",": raise RuntimeError("expected comma in column selector")
              l = l[1:]
        return cs
    elif type(l) == sqlparse.sql.Token and l.value == "*":
        return [ColumnSelector(None, COLUMN_SELECT_STAR)]
    else: # attempt to parse it as a query selector!
        return parse_col_selector(l)

# sqlparse.sql.query -> list[str]: table names
def parse_tables(l):
    if type(l) == sqlparse.sql.Token: return [l.value]
    elif type(l) == sqlparse.sql.Identifier: return [l.value]
    elif type(l) == sqlparse.sql.IdentifierList:
        l = [x for x in l if not x.is_whitespace]
        ts = []
        while l:
          assert type(l[0]) == sqlparse.sql.Identifier 
          ts.append(l[0].value); l = l[1:]
          # l still has more. ensure there was comma next.
          # We need , <QUERY>
          if l:
              if str(l[0]) != ",": raise RuntimeError("expected comma in column selector")
              l = l[1:]
        return ts
    else:
        raise RuntimeError("unknown table selector: |%s:%s|" % (l, type(l)))

# string -> COMPARE_TYPE
def parse_compare_op(opstr):
    if opstr == "=": return FILTER_RELATIONAL_EQ
    elif opstr == ">=": return FILTER_RELATIONAL_GEQ
    elif opstr == "<=": return FILTER_RELATIONAL_LEQ
    elif opstr == "<": return FILTER_RELATIONAL_LT
    elif opstr == ">": return FILTER_RELATIONAL_GT
    else: raise RuntimeError("unknown comparison: |%s|" % (opstr))

# string -> [identifier, int]
def parse_raw_param(p):
    assert(isinstance(p, str))
    def try_number(s):
        try: return Int(int(s))
        except ValueError: return None

    n = try_number(p)
    if n: return n
    return Identifier(str(p))

# list -> filter
def parse_where_clause(l):
    while l:
        assert(isinstance(l[0], sqlparse.sql.Comparison))
        # each where clause is an element of the list
        l = [x for x in l if not x.is_whitespace]
        raw_compare = l[0]; l = l[1:]
        raw_compare = [x for x in raw_compare if not x.is_whitespace]
        op = raw_compare[1]
        f = FilterRelational(parse_raw_param(raw_compare[0].value),
                    parse_compare_op(raw_compare[1].value), 
                    parse_raw_param(raw_compare[2].value))
        # there's no more
        if not l: return f
        else: # there's more, parse it
            if (l[0].value == 'and'):
                return FilterAnd(f, parse_where_clause(l[1:]))
            elif (l[0].value == 'or'):
                return FilterOr(f, parse_where_clause(l[1:]))
            else:
                raise RuntimeError("unknown comparison joiner: |%s|, where clause: |%s|" % (l[1], w))

    raise RuntimeError("parse_where_clause: UNREACHABLE")

# sqlparse.sql.where -> filter
def parse_where(w):
    assert(isinstance(w, sqlparse.sql.Where))
    # why the FUCK does it have whitespace
    l = [x for x in w[1:] if not x.is_whitespace]
    return parse_where_clause(l)


# really parse the query. The current thing returns some stupid tokenized
# list.
def parse_query(q):
    assert(isinstance(q, sqlparse.sql.Statement))
    q = [x for x in q if not x.is_whitespace]

    # <0|DML select> [1|cols:Ident|IdentList] 
    # <2|Keyword From>  [3|tables:Ident|IdentList]  <4|Where>
    COLSIX=1
    TABLESIX=3
    WHEREIX=4
    if q[0].value != 'select':
        raise RuntimeError("expected SELECT queries. Received: |%s|" % (q, ))

    cols = parse_col_selectors(q[COLSIX])
    tables = parse_tables(q[TABLESIX])

    if len(q) != 5: filters = []
    else: 
        print("parsing filters...")
        filters = parse_where(q[WHEREIX])
    return Query(tables, cols, filters)

# return a cross product of the rows
def table_cross(t1, t2):
    arr = np.empty((len(t1.rows) * len(t2.rows), t1.cols + t2.cols))
    # t1: 
    # a
    # b
    # c
    # t2:
    # x
    # y

    # arr: 
    # a x
    # b x
    # c x
    # a y
    # b y 
    # c y
    # >>> np.repeat([1, 2, 3], 3) := array([1, 1, 1, 2, 2, 2, 3, 3, 3])
    # >>> np.tile([1, 2, 3], 3) := array([1, 2, 3, 1, 2, 3, 1, 2, 3])

    arr[:, 0:t2.cols] = np.repeat(t1.rows, len(t2.rows))
    arr[:, t2.cols:] = np.tile(t2.rows, len(t1.rows))

    return Table(t1.name + "*" + t2.name, "NOPATH", t1.cols + t2.cols, rows)

def execute_query(db, q):
    assert(isinstance(db, DB))
    assert(isinstance(q, Query))


    print("executing query: |%s|" % (q, ))

    ts = []
    for traw in q.tables:
        if traw in db.tables: ts.append(db.tables[traw])
        else: raise RuntimeError("unknown table: |%s|" % (traw, ))

    # for each table, build the full cartesian product
    tfull = ts[0]
    assert(isinstance(tfull, Table))
    for t in ts[1:]: 
        assert(isinstance(t, Table))
        tfull = table_cross(t, tfull)

    print("full table:\n")
    print(tfull)
    print(tfull.cols)
    print(tfull.rows)




if __name__ == "__main__":
    db = load_db(os.path.join(BASEPATH, "metadata.txt"))

    if sys.argv[1] == "--inputfile":
        with open(sys.argv[2], "r") as f: 
            for raw in f:
                qs = list(sqlparse.parse(raw))
                for q in qs:
                    print("---")
                    print("raw query: |%s|" % (q, ))
                    q = parse_query(q)
                    execute_query(db, q)
    else:
        raw = sys.argv[1]
        logging.debug("raw query string:|%s|" %(raw, ))
        qs = list(sqlparse.parse(raw))
        logging.debug("raw query object:|%s|" %(qs, ))

        for q in qs:
            q = parse_query(q)
            execute_query(db, q)
