# Database engine

#### V1: can handle everything in this query
```
select col1, distinct(col2) from table1,table2 where cl1=10 and col2=20 or col3=40
```

#### using `sqlparse`:

```py
python3 -i 20161105_Assignment1.py "select col1, distinct(col2) from table1,table2 where cl1=10 and col2=20 or col3=40"
ut[3]: 
<DML 'select' at 0x7FC63DA252E8>,
<Whitespace ' ' at 0x7FC63DA25348>,
<IdentifierList 'col1, ...' at 0x7FC63DA37048>,
<Whitespace ' ' at 0x7FC63DA25648>,
<Keyword 'from' at 0x7FC63DA256A8>,
<Whitespace ' ' at 0x7FC63DA25708>,
<IdentifierList 'table1...' at 0x7FC63DA370C0>,
<Whitespace ' ' at 0x7FC63DA25888>,
<Where 'where ...' at 0x7FC63DC6CA20>]
n [2]: w=qs[0].tokens[-1];
n [3]: w.tokens
ut[3]: 
<Keyword 'where' at 0x7F50DA0498E8>,
<Whitespace ' ' at 0x7F50DA049948>,
<Comparison 'cl1=10' at 0x7F50DA290E58>,
<Whitespace ' ' at 0x7F50DA049AC8>,
<Keyword 'and' at 0x7F50DA049B28>,
<Whitespace ' ' at 0x7F50DA049B88>,
<Comparison 'col2=20' at 0x7F50DA290ED0>,
<Whitespace ' ' at 0x7F50DA049D08>,
<Keyword 'or' at 0x7F50DA049D68>,
<Whitespace ' ' at 0x7F50DA049DC8>,
<Comparison 'col3=40' at 0x7F50DA290F48>]
```
