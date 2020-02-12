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
        for (i, t) in enumerate(self.tables):
            if not isinstance(t, Table):
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

    tables = []
    while ls:
        assert(ls[0] == "<begin_table>")
        i = 0
        while ls[i] != "<end_table>": i += 1
        #  ls[0] = begin_table
        # ls[1] = TABLE NAME
        # ls[2..i-1] = TABLE column names
        #  ls[i] = end_table
        name = ls[1]; cols=ls[2:i]; ls=ls[i+1:]
        tables.append(load_table(name, 
                                 os.path.join(BASEPATH, name + ".csv"), cols))
    return DB(path, tables)



COLUMN_SELECT_ALL = "column_select_all"
COLUMN_SELECT_MAX = "column_select_max"
COLUMN_SELECT_MIN = "column_select_min"
COLUMN_SELECT_AVG = "column_select_avg"
class ColumnSelector:
    def __init__(self, col, ty):
        self.col = col
        self.ty = ty
        assert self.ty in [COLUMN_SELECT_ALL, COLUMN_SELECT_AVG,
                           COLUMN_SELECT_MAX, COLUMN_SELECT_MIN]

    def __repr__(self):
        return "%s(%s)" % (self.ty, self.col)

class Query:
    def __init__(self, tables, cols, filters):
        self.tables = tables
        self.cols = cols
        self.filters = filters

class Filter:
    def __init__(self): pass

class FilterAnd:
    def __init__(self, l, r):
        self.l = l
        self.r = r

    def __repr__(self):
        return "(AND %s %s)" % (self.l.__repr__(), self.r.__repr__())

class FilterOr:
    def __init__(self, l, r):
        self.l = l
        self.r = r

    def __repr__(self):
        return "(AND %s %s)" % (self.l.__repr__(), self.r.__repr__())

FILTER_RELATIONAL_EQ = "filter_relational_eq"
FILTER_RELATIONAL_GEQ = "filter_relational_geq"
FILTER_RELATIONAL_LEQ = "filter_relational_leq"
FILTER_RELATIONAL_LT = "filter_relational_lt"
FILTER_RELATIONAL_GT = "filter_relational_gt"
class FilterRelational:
    def __init__(self, col, rel, val):
        self.col = col
        self.ty = ty
        self.val = val
        assert self.ty in [FILTER_RELATIONAL_LT, FILTER_RELATIONAL_LEQ,
                           FILTER_RELATIONAL_EQ, FILTER_RELATIONAL_GT,
                           FILTER_RELATIONAL_GEQ]


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
    else:
        raise RuntimeError("unknown column selector query: |%s:%s|" % (l, type(l)))

# sqlparse.sql.query -> list[str]: table names
def parse_tables(l):
    if type(l) == sqlparse.sql.Token: return [l.value]
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

# sqlparse.sql.where -> list[filter]
def parse_filters(l):
    pass


# really parse the query. The current thing returns some stupid tokenized
# list.
def parse_query(q):
    assert(isinstance(q, sqlparse.sql.Statement))

    # <0|DML select> <1|WS> [2|cols:Ident|IdentList] <3|WS> 
    # <4|Keyword From> <5|WS> [6|tables:Ident|IdentList] <6|WS> <7|Where>
    COLSIX=2
    TABLESIX=6
    WHEREIX=7
    if q[0].value != 'select':
        raise RuntimeError("expected SELECT queries. Received: |%s|" % (q, ))

    cols = parse_col_selectors(q[COLSIX])
    tables = parse_tables(q[TABLESIX])

    if len(q.tokens) != 9: filters = []
    else: filters = parse_filters(q[WHEREIX])

    print("cols: %s" % (cols, ))
    print("tables: %s" % (tables, ))
    print("filters: %s" % (filters, ))
    return Query(cols, tables, filters)

def execute_query(db, q):
    assert(isinstance(db, DB))
    assert(isinstance(q, Query))


if __name__ == "__main__":
    db = load_db(os.path.join(BASEPATH, "metadata.txt"))

    if sys.argv[1] == "--inputfile":
        with open(sys.argv[2], "r") as f: 
            for raw in f:
                logging.debug("raw query string:|%s|" %(raw, ))
                qs = list(sqlparse.parse(raw))
                logging.debug("raw query object:|%s|" %(qs, ))

                for q in qs:
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
