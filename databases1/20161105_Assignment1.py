#!/usr/bin/env python3
import sys
import os
import os.path
import csv
import logging
import sqlparse
from collections import defaultdict
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
COLUMN_SELECT_SUM = "column_select_sum"
COLUMN_SELECT_DISTINCT = "column_select_distinct"
class ColumnSelector:
    def __init__(self, col, ty):
        self.col = col
        self.ty = ty
        assert self.ty in [COLUMN_SELECT_ALL, COLUMN_SELECT_AVG,
                           COLUMN_SELECT_MAX, COLUMN_SELECT_MIN,
                           COLUMN_SELECT_STAR, COLUMN_SELECT_DISTINCT,
                          COLUMN_SELECT_SUM]
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

class Filter:
    #  check if this filter allows this row
    # (col2ix, row) -> bool
    # table for column info
    def run(self, col2ix, r): 
        raise RuntimeError("unimplemented function")


class FilterAnd(Filter):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
        assert(isinstance(self.lhs, (Identifier, Int, Filter)))
        assert(isinstance(self.rhs, (Identifier, Int, Filter)))

    def __repr__(self):
        return "(AND %s %s)" % (self.lhs.__repr__(), self.rhs.__repr__())

    def run(self, col2ix, r): 
        return self.lhs.run(col2ix, r) and self.rhs.run(col2ix, r)


class FilterOr(Filter):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs
        assert(isinstance(self.lhs, (Identifier, Int, Filter)))
        assert(isinstance(self.rhs, (Identifier, Int, Filter)))

    def __repr__(self):
        return "(OR %s %s)" % (self.lhs.__repr__(), self.rhs.__repr__())

    def run(self, col2ix, r): 
        return self.lhs.run(col2ix, r) or self.rhs.run(col2ix, r)

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

    def run(self, col2ix, r): 
        if self.ty == FILTER_RELATIONAL_LT:
            return int(self.lhs.run(col2ix,  r)) < int(self.rhs.run(col2ix, r))
        elif self.ty == FILTER_RELATIONAL_EQ:
            return self.lhs.run(col2ix,  r) == self.rhs.run(col2ix, r)
        elif self.ty == FILTER_RELATIONAL_GT:
            return int(self.lhs.run(cs,  r)) > int(self.rhs.run(col2ix, r))
        elif self.ty == FILTER_RELATIONAL_GEQ:
            return int(self.lhs.run(col2ix,  r)) >= int(self.rhs.run(col2ix, r))
        elif self.ty == FILTER_RELATIONAL_LEQ:
            return int(self.lhs.run(cs,  r)) <= int(self.rhs.run(col2ix, r))
        else: raise RuntimeError("unknown filter type when running filter: (%s)" % (self.ty))


class Identifier:
    def __init__(self, s): self.s = s; assert(isinstance(s, str))
    def __repr__(self): return "Identifier(%s)" % (self.s, )
    def run(self, col2ix, r): 
        # look for current index
        try:
            i = col2ix[self.s];  return r[i]
        except ValueError as v:
            raise RuntimeError("unable to find column(%s) in columns(%s)" % (self.s, cs))

class Int:
    def __init__(self, i): self.i = i; assert(isinstance(i, int))
    def __repr__(self): return "Int(%s)" % (self.i, )
    def run(self, col2ix, r): return self.i



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
        elif name == "sum":
            return ColumnSelector(col, COLUMN_SELECT_SUM)
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
        return [parse_col_selector(l)]

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
            if (l[0].value.lower() == 'and'):
                return FilterAnd(f, parse_where_clause(l[1:]))
            elif (l[0].value.lower() == 'or'):
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
    if q[0].value.lower() != 'select':
        raise RuntimeError("expected SELECT queries. Received: |%s|" % (q, ))

    cols = parse_col_selectors(q[COLSIX])
    tables = parse_tables(q[TABLESIX])

    if len(q) != 5: filters = None
    else: 
        print("parsing filters...")
        filters = parse_where(q[WHEREIX])
    return Query(tables, cols, filters)

# return a cross product of all the rows
# r1: NROWS1 x NCOLS1 | r2: NROWS2 x NCOLS2
# r1xr2: (NROWS1*NROWS2) x (NCOLS1+NCOLS2)
def rows_cartesian_product(r1s, r2s):
    nr1 = r1s.shape[0]; nc1 = r1s.shape[1]
    nr2 = r2s.shape[0]; nc2 = r2s.shape[1]
    
    arr = np.empty([nr1 * nr2, nc1 + nc2])

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
    i = 0
    for r1 in r1s:
        for r2 in r2s:
            arr[i][:nc1] = r1
            arr[i][nc1:] = r2
            i += 1
    return arr

# raw column string -> (column, table)
def raw_col_access_to_col_table(raw_col_name, db):
    # column name does not have table name, so search across all tables
    dotix = raw_col_name.find('.')
    if dotix == -1:
        # go through all tables
        potential_tables = []
        col_name = raw_col_name

        for tname in db.tables:
            for c in tname.cols: 
                if  col_name == c: potential_tables.push_back(c)

        if len(potential_tables) == 0:
            raise RuntimeError("unable to find column: %s" % (col_name))
        elif len(potential_tables) >= 1:
            raise RuntimeError("column (%s) found in mulitple tables: %s" % 
                    (col_name, potential_tables))
        return (col_name, potential_tables[0])
    else: 
        (col_name, table_name) = raw_col_name[:dotix], raw_col_name[dotix+1:]
        if table_name not in db.tables:
            raise RuntimeError("unable to find table: %s" % (table_name))
        t = db.tables[table_name]
        if col_name not in t.cols:
            raise RuntimeError("unable to find column: %s" % (col_name))
        return (col_name, table_name)


def col2ix_to_ix2cols(col2ix):
    i2cols = defaultdict(list)
    for c in col2ix: i2cols[col2ix[c]].append(c)
    return i2cols

# return a list of canonical column names, where 
# canon[i] = c => c ∈ col2ix[i] . 
def canonical_col_names(colixs, col2ix, ix2cols):
    canon = [None for _ in range(len(colixs))]
    i = 0
    for ix in colixs:
        # this column has a "small" name, which means 
        # it was safe.
        small = [c for c in ix2cols[ix] if not '.' in c]
        full = [c for c in ix2cols[ix] if '.' in c]
        if small: canon[i] = small[0]
        else: canon[i] = full[0]
        i += 1

    return canon


# delete all associated rows, given the column and the index
# in the column of a table
def del_row_in_table(i, cix, colix2data, colix2table):
    for ix in colix2table:
        if colix2table[ix] == colix2table[cix]:
            colix2data[ix] = np.delete(colix2data[ix], i)



def execute_query_2(db, q):
    # name each column uniquely, and store data per column
    ts = []
    for traw in q.tables:
        assert isinstance(traw, str)
        if traw in db.tables: ts.append(db.tables[traw])
        else: raise RuntimeError("unknown table: |%s|" % (traw, ))


    
    # build the cartesian product
    # create a map between column to tables containing the column
    col2table = defaultdict(list)
    for t in ts:
        for c in t.cols: 
            col2table[c].append(t)

    # map each table to new column names
    col2ix = {}
    colix2data = {}
    colix2table = {}
    # rename all columns that have multiple tables
    for t in ts:
        for (cix, c) in enumerate(t.cols):
            assert c in col2table 
            ix = len(colix2data)
            # this column occurs in multiple tables; rename it
            if len(col2table[c]) > 1: 
                col2ix[t.name + "." + c] = ix
            else: 
                col2ix[t.name + "." + c] = ix
                col2ix[c] = ix
            colix2data[ix] = t.rows[cix]
            colix2table[ix] = t.name

    ix2cols = col2ix_to_ix2cols(col2ix)


    # now run the column selectors from each table
    # ============================================
    # no index is selected
    colixs_selected = set()

    for cq in q.cols:
        if cq.ty.lower() == COLUMN_SELECT_STAR.lower(): 
            # add all tables in the query
            for traw in q.tables:
                for c in db.tables[traw].cols:
                    colixs_selected.add(col2ix[t.name + "." + c])
            break
        assert isinstance(cq, ColumnSelector)
        cix = col2ix[cq.col]
        d = colix2data[cix]
        colixs_selected.add(cix)
        if cq.ty == COLUMN_SELECT_ALL: pass # nothing to filter
        elif cq.ty == COLUMN_SELECT_MAX:
            m = np.max(d)
            # rows to kill
            tokill = []
            for i in len(d): 
                if d[i] < m: tokill.append(i)
            for i in tokill: del_row_in_table(i, cix, colix2data, colix2table)
        else:
            print("unhandled case")


    # find dimensions of each table
    total_rows = 1
    t2rows = {}
    for t in ts:
        # data of all columns. We should check that they all have the same
        # length
        nrows = None
        for c in t.cols:
            # column is not selected, skip
            ix = col2ix[c]
            if ix not in colixs_selected: continue;
            if not nrows: nrows = len(colix2data[ix])
            else: assert nrows == len(colix2data[ix])

        ncols = len(colixs_selected)
        if total_rows == 0 or ncols == 0:
            print(">>>>>>>>>>>NO DATA SELECTED!<<<<<<<<<<<"); return

        total_rows *= nrows
        t2rows[t.name] = nrows




    # mapping from column indexes to data in the _product_ table
    colix2cartdata = {}
    nreps = total_rows
    for t in ts:
        nreps //= t2rows[t.name]
        for c in t.cols: 
            ix = col2ix[c]
            if ix not in colixs_selected: continue

            colix2cartdata[ix] = np.empty(total_rows, dtype=np.float)

            dix = 0
            for d in colix2data[ix]:
                for _ in range(nreps):
                    colix2cartdata[ix][dix] = d
                    dix += 1


    ###PRINTING
    ###========

    canonical_names = canonical_col_names(colix2cartdata.keys(), col2ix, ix2cols)
    print("table after query:")
    for n in canonical_names: print("%10s" % n, end=" ")
    print("\n" + ("-" * 50))
    for r in range(total_rows):
        for c in canonical_names:
            print("%10s" % (colix2cartdata[col2ix[c]][r], ), end=" ")
        print("\n", end="")


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
                    execute_query_2(db, q)
    else:
        raw = sys.argv[1]
        logging.debug("raw query string:|%s|" %(raw, ))
        qs = list(sqlparse.parse(raw))
        logging.debug("raw query object:|%s|" %(qs, ))

        for q in qs:
            q = parse_query(q)
            execute_query_2(db, q)
