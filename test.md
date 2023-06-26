# How to Write a Unit Test in Dafny 101
## Unit Test for a single predicate
### Setup
Specify each parameter of the predicate, which serves as the input of the test. There might be some fields that do not affect the expected result of the predicate.
* If you make any additional assumption on the specification / function you calls, you need to `assume` them. (For example, you need an additional property of an empty function.)
* How to make it comprehensive
    * consider cases that are expected to be either true / false, and assert accordingly
    * like traditional tests - 0,1,more
    * think through every case
* For some large data structures with many fields and layers, one can write a function that returns a basic form of it, and use it to generate various building blocks for the test.
* With these building blocks, one may automatically generate some tests. (limited)
### Proof
* If your assertion passes, the test passes!
* If not, first try negating the asserted statement, and see if it passes or not. If the negated one passes, then the test fails. (or assert false after this line, and if it passes, then the test fails, same check)

---
* assert / make explicit the key aspect of this test (why you think it should pass / fail, maybe it's that the specified parameters have some property), and dig deeper into it if it fails
* If it is an implicit exists, it will most likely need a witness.
* assert what you know about the variables you specified that is not necessarily captured -- `ironLock - test_self.dfy`
---
Basic techniques used for proof without prior knowledge about the predicate
* If both attempts do not pass, either you need more proof (usually you need a witness), or there is some behavior underspecified (like an empty function).
* Look into the predicate you are asserting, decompose it by its `&&`s and `||`s from the outside in. If it's `&&`s, assert all of them while replacing the parameter names with actual variable names and focus on those do not pass. Else if it's `||`s, assert the negation of all of them and focus on those do not pass. (or by inspection)
* For foralls: do recursively on the sub-expression using forall statement
* For exists: find a witness that you think will evaluate to true
* Do this recursively until the assertion is evaluated to true / false.
---
With prior knowledge about the predicate:
    find out where there is `exists` or `!forall`, and find witness for them

---
Witness:
* exists / !forall
* assert map non-empty (ironHT)
* find one such that (binarySearch)
? ironLock - test_self.dfy

