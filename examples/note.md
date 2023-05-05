## How can test spec be helpful
* before having an implementation, check if the spec is correct
* after having an implementation, cut down on the time to run the test cases

## Non-Deterministic Test
(I think it is an impressive idea, since it actually works rigorously for some cases, and is related to the potential problem with sorting spec)

Potential problem:
* dafny may not be able to prove - false negative
    * e.g., sort.dfy
* even if the spec is deterministic, it may not be correct - false positive
    * e.g., max_example2.dfy
* even if the spec is non-deterministic, it may be correct - false negative
    * desired implementation is non-deterministic
        * some random algorithm?
        * cannot address by non-deterministic test
    * desired implementation is deterministic
        <!-- * add additional layer to the spec to make its constraint as tight as the potential implementation (in absence of implementation) e.g., binary_search.dfy -->
            * in this case, if the detailed spec is non-deterministic, it is incorrect
            * not sure whether it is sensible to do so

## Fuzzing
### Intuition
1. spec is like an automated verifier for test case output
2. want to check if the automated verifier is consistent with "correct" human understanding of the problem
3. think the "correct" human understanding as a black box, that given an (input, output) pair, it can return true/false, but it's a black box so that we can never prove that the black box and the spec is equivalent
4. what we want to know: to some reasonable extent, is the spec equivalent to the black box?
5. assumption: mostly the spec we write are not stricter than the desired level of constraint, it is more common to have a spec that is too "loose"
6. to make it simple in this stage, is the spec looser than the black box?

only expose bugs when specification is weaker than expected

The whole point of formally verified code lies in that the implementation must satisfy what is specified in the specifications. However, people need to carefully examine through specifications to make sure that it is correct in the first place. The first method we propose is to simulating execution using the spec, generating (input, output) pairs that are accepted by the code, and asking the developers to manually examine whether those pairs make sense. The idea is similar to testing in traditional code bases, while the only difference is that the result is generated by a solver instead of by running the implementation.

We utilize z3 library in Python to "run" the specifications. Given constraints in the specification, it will automatically generate valid (input, output) pairs. Since the search space is likely to be very large (even infinite), some constraints on the input are sometimes added so that z3 gives more diverse result in terms of functionality of the code.

However, the translation from pre/post conditions in dafny to z3 expressions is manual currently, which could be automated in the future.

### Fuzzing
* wrap our spec (although can be transparent to us) as a black box
* want to find sth. in the spec black box but not in the human black box
* use heuristics (e.g. z3) to automatically generate "test cases" that is in spec black box, and check manually by the human black box
#### Approaches and potential problems
1. randomness - require significant amount of manual work (and can never be automated)
2. edge cases - not all problems are at the edge
<!-- 3. potential improvement of 1: extract duplicated pattern on top of the test cases generated
    * need to establish equivalency of cases (e.g., for sorting, the pattern [2,1,3]->[1,2,3] is nothing different from [5,4,6]->[4,5,6] in some sense)
        * is there any related research on perhaps traditional testing that automated generation of test cases, and how do they address the issue? -->

If 3 works, it is a good alternative to testing with automatically generated test cases in normal code for specs in my opinion.

#### Notes
<!-- BTW, I think coming up with test cases by human is not unhelpful because that is exactly the case when people write traditional codes and write test cases for them. In that case, what people do is just forget about the implementation (in our case, equivalently, the spec), and write test cases from their own understanding. -->

(A potential problem with this may be that for non-deterministic specs it is hard to produce all possible result the spec accept, or even with those results, how to remove duplicates to cut down on manual work as in 3.)

But for deterministic specs, people can just run the test case, and (if possible by z3) generate the only output that the spec can accept, as what people do in traditional testing.

I think for testing spec it is not sensitive to write a verifier for the output of the test since essentially the spec itself is one and we are trouble-shooting it now.

## Mutation Testing
Work in presence of implementation
### Basic working model
* mutate the spec (spec0 -> spec1)
* check if the spec1 includes spec0
    * if yes, then continue
* check if the compilation still passes
    * passes if the mutated spec is not stricter than the implementation
* if compilation passes, then spec0 is weaker than the implementation
### Terminology
* equivalence of spec and implementation: they accept exactly the same set of (input, output) pairs
* partial order(?) of specs: if $s_1<s_2$, then every (input, output) pairs accepted by $s_1$ is accepted by $s_2$
* spec0: original spec
* spec[n] (n != 0): mutated spec
* spec*: a spec that is equivalent to the implementation (theoretical)
* deterministic: given one input $i$ that fulfills the `requires` clause, there is one and only one of ($i$, output) pair that are accepted by the spec (or produced by the implementation)
### Logic
1. We assume spec0 passes compilation with the implementation ==> spec0 >= spec*
2. spec1 does not include spec0 ==> spec1 not greater than or equal to spec0
3. compilation passes ==> spec1 >= spec*
4. 2,3 ==> spec0 != spec*, 1 ==> spec0 > spec*
Thus, if one mutation passes the test, the conclusion is that the spec is weaker than the implementation
## Non deterministic spec & implementation discussion (Presence of Implementation)
Note: only available in presence of implementation

* focus on correctness of implementation or relationship between implementation & spec
* note that besides the methods listed below, we can always turn to the test in absence of implementation
* we can also turn to traditional end-to-end testing given the implementation, possible downsides
    * slow
    * spec's correctness still unknown, only test the implementation

Assumption: 
* "requires" is the same for spec & implementation (both theoretically and in terms of dafny code)
* for all input $i$ that fulfills `requires` clause, there exists at least one ouptut $o$ such that $(i,o)$ in accepted by the spec
* the same for implementation

> cannot think of a counter-example for this, since in some sense exception thrown is another kind of $o$

Whether spec is deterministic:
* We have our non-deterministic test!

Whether implementation is deterministic:
* if not using some randomness lib, it should be deterministic

1. Implementation should be deterministic, spec should be deterministic
    * theoretical perspective
        * the acceptable (input, output) pairs are exactly the same
        * ==> spec0 = spec*
    * implementation perspective (use determinism of the true spec and implementation)
        * the input set for spec0 and spec* are the same
        * spec* <= spec0, both deterministic
        * ==> spec0 = spec*
        * Thus, if one can make sure both the spec and implementation (our version) are deterministic, one can be certain that spec0 = spec* without any further testing.
    * implementation perspective (without knowing determinisim of the true spec)
        * assume the true implementation is deterministic
        * Approaches:
            * non-determinism of spec is equivalent to a passing spec1
            * in this case, finding a non-deterministic spec or finding a passing spec1 gives us a shot
            * fuzzing can also work by checking if it is non-deterministic (by just generating the test case and see if there are the same input with different output, or by feeding the correct input to implementation and check if it is the same)

2. Implementation should be deterministic, spec could be non-deterministic
    * check implementation is deterministic, which can be easily checked
    * reduce spec to deterministic version and then same as 1
    
3. Implementation could be non-deterministic, spec could be non-deterministic
    1. ideally spec0 = spec*
        * mutation testing should work
    2. spec0 > spec*
        * reduce spec0 to spec* (may not be feasible)

## Absence of implementation
* non-deterministic testing
* fuzzing
1. Both should be deterministic
    * essential difference with testing traditional deterministic code: non-determinism of spec*
    * non-deterministic test
    * after ensuring determinism of the spec, only left is whether (input, output) pairs are desirable, can use fuzzing or traditional testing(run using z3 as traditional testing)
        * might not be as efficient as end-to-end testing in presence of implementation
2. Both could be non-deterministic (e.g., random algorithm)
    * fuzzing
    * how do people test this in traditional non-deterministic code?

3. Spec0 could be non-deterministic, implementation should be deterministic
    * reduce spec to deterministic and use 1
        * e.g., define previously "undefined behavior" in another layer of spec
    * modified non-deterministic test and use 1
        * change equality constraint of ND test to something else (e.g., output from the spec are in the same range instead of being exactly the same)
    * anything that works for 2


It might be considered tedious to manually examine the cases generated by fuzzing, and thus we also propose two other testing method that checks general property of a codebase.

In presence of implementation for a codebase, we expect that specification is exactly equal to the implementation (all (input, output) pairs accepted by them are exactly the same) for a considerable proportion of them. We mutate the specification and ask Dafny whether the original implementation meets the new spec. If it does, and the mutated specification is not absolutely weaker than or equal to the original one, then we can conclude that there exists some (input, output) pair that are accepted by the spec, but can never be generated by the implementation, raising a red flag.



Non-deterministic

Under cases where the code is expected to behave deterministically, and that the specification is exactly equal to the implementation, the specification itself should give deterministic result. By asking Dafny to prove that two (input, output) pairs with the same input accepted by the specification gives the same output, we can know about determinism of the specification. A non-deterministic flag servers as a warning to the user, telling that the specification is specifying a non-deterministic behavior.