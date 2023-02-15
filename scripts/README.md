### Spec Testing Scripts 

#### `nonDeterministicTestGenerator.py`

Generates and/or appends a Non-Deterministic test for a predicate or Lemma in Dafny.

Non-determinism in a spec could be a red flag that the spec is not what is fully intended.

Usage:
-h: help 

-i: inputfile    

-n: nameOfFunction 

-s: StateMachineFlag(default=False): 
>True: designated predicate is a state machine transition

>False: designated predicate is a standard predicate

-a: AppendFlag(default=False): 
>True: generated lemma is appended to bottom of input file

>False: generated lemma is only printed to console

**Example**: 
If the following predicate existed in a file `example.s.dfy`:

```
predicate PurchaseND(c:Constants, v:CokeMachine, v':CokeMachine) 
{
    && v.numCokes > 0
    && v'.numCokes <= v.numCokes - 1
}
```
Running the following command:

 `python scripts/nonDeterministicTestGenerator.py -i example.s.dfy -n "Restock" -s True`
 
 Will output the following lemma as a Test:
 
```
lemma is_PurchaseND_ND(c:Constants, v:CokeMachine, v':CokeMachine, v'':CokeMachine)
     requires PurchaseND(c, v, v')
     requires PurchaseND(c, v, v'')
     ensures  v' ==  v''
{
}
```

> **_NOTE:_**  Assumes Predicate is in the following form (With the body bracket on the next line after the parameters)

```
PREDICATE NAME(PARAM1, PARAM2)
{
}
```

#### `fuzzing.py`

Uses Z3py to automatically generate unique satisfying values for expresions. 

Rather than writing "unit-like" tests for predicates, this leverages z3 to automatically find
satisfying input,output pairs that then can be checked manually. By examining the output, the user can get a sense from the generated input,output pairs if their spec permits the intended implementation. 

> **_NOTE:_** Only works for expresions using INT type, and automatically checks with additional constraints of `INT.MAX` and `INT.MIN`

Usage:
-h: help 

-i: vals -- A dictionary of input type pairs

>EX:  '{ "a": "Int", "b": "Int" , "c":"Int"}'    

-q: query -- SMT query in String format

>EX: "And(c >= a, c >= b)" 

-n: number of Trials -- Number of unique satisfying assignments to ask Z3 for

`python scripts/fuzzing.py -v '{ "a": "Int", "b": "Int" , "c":"Int"}'  -q "And(c >= a, c >= b)" -n 4`

##### `fuzzing.py` Example Queries

```
predicate predMaxEx(a:int,b:int,c:int)
{
  && c > a
  && c > b
}
```

* `And(c >= a, c >= b)`

```
predicate PurchaseND(c:Constants, v:CokeMachine, v':CokeMachine) 
{
    && v.numCokes > 0
    && v'.numCokes <= v.numCokes - 1
}

predicate Inv(c:Constants, v:CokeMachine) 
{
    0 <= v.numCokes <= c.capacity
}
```

*  `And(v >= 0, v <= c, v > 0, w <= v - 1, c == 7)`

```
predicate Purchase(c:Constants, v:CokeMachine, v':CokeMachine) 
{
    && v.numCokes > 0
    && v'.numCokes == v.numCokes - 1
}

predicate Inv(c:Constants, v:CokeMachine) 
{
    0 <= v.numCokes <= c.capacity
}
```

*  `And(v >= 0, v <= c, v > 0, w == v - 1, c == 7)`
