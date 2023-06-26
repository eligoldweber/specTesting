## Testing Concepts
* Regression Testing
    * assess whether future implementations still fix the bug
    * when you fix a bug, add a test that specifically exposes that bug
* Unit Testing
    * most are based on SUnit
    * xUnit: a piece of code (method) that establishes some preconditions, performs an operation, and asserts postconditions
        * test fixture: code to be run before/after each test case ==> each test is run in a "fresh" environment
        * isolation, small, fast: only test a specific unit
        * in terms of testSpec: test spec with another set of (not necessarily comprehensive) pre/postconditions
        * Java JUnit
        * Python unittest
        * C++ googletest
* Test-Driven Development
    * requirements are turned into very specific test cases, then the software is improved so that the tests pass
* Integration Testing
    * "End-to-end" testing: combines and tests individual software modules as a group
* Mocking

## Test Suite Quality Metrics
Informal Desideratum: The program passes the tests if and only if it does all the right things and none of the wrong things.
* All of the requirements should be covered by the test suite
    * "passing this test gives confidence that a program adheres to requirement Y"

* Line coverage: number of unique lines visited by the program when running the test suite
* Branch coverage
* Mutation analysis
    * defect seeding: the process of intentionally introducing a defect into a program
        * typically intentionally similar to defects introduced by real developers
        * typically done automatically (given a model of what human bugs look like) [481 hw3]
        * mutation operator: systematically changes a program point (modeled on historical human defects)
        * mutant (variant) - order: number of mutation operators applied
    * A test suite is said to kill (or detect, or reveal) a mutant if the mutant fails a test that the original passes
    * Mutation adequacy score: making a number of mutants and measuring the fraction of them killed by that test suite (higher is better)

    * Equivalent Mutant Problem: dilute the mutation score
        * an undecidable problem


## Test Inputs, Oracles and Generation
"Kill it with Math" vs. "Humans are central"

comparator may not be "must match exactly": known random output, precision limits, embedded dates

### Input
not only the test file itself

automatically generating:
* path coverage: enumerate every path
* path predicate (condition, constraint): a boolean formula over program variables that is true when the program executes a given path ==> satisfying assignments

### Oracles (Output)
correspond to **what the program should do**
generating them is an expensive problem
it can be done automatically through invariants and mutation: emperical


### Test suite minimization
