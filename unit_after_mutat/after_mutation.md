## What to do after finding alive mutataions
### Theoretical Discussion
1. What an alive mutation means: the original spec allows more behavior than the implementation
2. What an alive mutation can give us: a "stronger" spec that allows this implementation (i.e., the intersection between the original spec and the mutant)
    * Proof: implementation $\subset$ original && implementation $\subset$ mutant ==> implementation $\subset$ (original $\cap$ mutant)
3. The ultimate question we want to ask in correctness tests:
    * Does there exist some invalid behavior that is allowed by the original spec?
4. The question we want to ask with alive mutations:
    * Does all acceptable behaviors have the property specified by the intersection? Is  ({original} - {mutat}) $\subset$ {invalid behavior}?
    * Does there exist some invalid behavior that is allowed by the original spec, but not the mutant? Is there any invalid behavior $\in$ ({original} - {mutat})?
5. Analysis
    * The first question gets hint from the mutation framework most directly. We might miss some bugs in this way.
    * The second question gets some kind of hint from the mutation framework, catches more cases, but requires more manual effort. Could not theoretically prove it is more efficient than correctness testing without mutations. Can try based on emperical experience.
    * We do not ask whether there are invalid behavior inside the intersection, because there are no hints from the alive mutation that there could be any issue.
6. How to answer the questions
    * Answering the first question is easy, since enough hint has been given by the alive mutations.
        * 1st step: try to manually judge whether {original} $\cap$ {mutat} is a must for valid input. If it is, then we know there is a bug. If it is not, then the answer to the question is no.
        * 2nd step: If we cannot manully judge, we only need to find a single instance from ({original} - {mutat}). If it is valid, the the answer to the question is no. If it is invalid, then we know there is a bug.
    * Answering the second question is a less "deterministic" behavior, as it is for most testing procedures. The goal is then to find a counterexample which:
        1. is invalid beahvior
        2. $\in$ {original}
        3. $\notin$ {mutat}
    
7. Solutions
    1. try to manually judge whether {original} $\cap$ {mutat} is a must for valid input. If it is, then we know there is a bug. If it is not, or it is nontrivial to judge, then go to step 2.
    2. Find an instance from ({original} - {mutat}), which is nonempty, see if it is valid/invalid. If it is invalid, then there is a bug. If it is not, we do not know, go to step 3.
    3. One can end here right away, because the first question has been answered. If one want to exploit the "hints" more thoroughly (emperically), then one can *find more instances and repeat the procedure*. (Essentially find a counterexample.)

    * Besides the "structured way" mentioned above, one could also try to find a counterexample that have all of the following. Replacing or parellelizing all later steps starting from any of 1,2,3
        1. is invalid beahvior
        2. $\in$ {original}
        3. $\notin$ {mutat}

### Method used to find a counterexample such that
1. is invalid beahvior: human judgement
2. $\in$ {original}: expression
3. $\notin$ {mutat}: expression
---


Indicator: efficiency (of manual effort) and coverage

If we use hint from mutation framework, and tries only to answer question 1 and 2, we compromises coverage, but it is fine.
##### Finding counterexamplese without mutation
Recall correctness testing without mutations. There we are essentially finding a counterexample such that
1. is invalid behavior
2. $\in$ {spec}

Apart from mutation testing, we have two ideas
1. Unit-like tests: Finding all kinds of invalid behaviors (1), check it against spec (2)
2. Fuzzing-like tests: Finding all kinds of behavior allowed by spec (2), judge if it is valid/invalid (1) *I even think manual fuzzing will be a viable technique in manual testing now, because spec is simpler than traditional implementation which we are going to test.*

Of course we can also find a counterexample directly, which take both (1) and (2) into consideration at the same time. But we do not expect people who can do that with a specific spec to use our testing method, and we do not place assumptions on how they would do this. I do guess that manually finding a counterexample involves separating 1 and 3 because I do it this way, but I cannot prove that.

All testings are essentially helping this thinking.

##### Finding counterexamples with alive mutation
Let's permutate the possible steps we can take in face of the three conditions for the counterexample:
(x) -> (y) means do x, then check y

1. Doing (1(23)) all at once: It is about finding a counterexample directly. (23) can be combined algorithmically. So the case would be exactly the same as in cases without mutation, except for a shrunk {spec}. It is a more "focused" search for counterexample. We do not know if it is easier or not compared to the case without mutation, so it could be easier (empirically).

2. (1) -> (23): The manual effort will be finding all cases according to 1. However, this effort is exactly the same as the case one would spend without mutations. Worse, if one already have (1), checking against (2) only provides more coverage.

3. (2) -> (13): The manual effort will be fuzzing (2). However, this effort is exactly the same as the case one would spend without mutations. It is strictly worse than (23) -> (1), which has less to fuzz, taking less manual effort in this step.

4. (3) -> (12): It is also strictly worse than (23) -> (1).

5. (12) -> (3): This requires finding a general case counterexample in the first place. Once (12) is met, we have already known there is a bug. It does not use any hint from the mutation framework.

6. (13) -> (2): (13) is finding a "counterexample"ish thing. Doing 1 and 3 separately boils down to 2 and 4. I do not see a way to combine 1 and 3 together in thinking because they are "heterogenuous"(?) And if there is, I do not see why combining 1 and 3 together is easier than combining 1 and 2, or combining 1 and (23), which directly solve the problem. And even if that is, I do not see why the easy results from (13) will contain those has property (2). The reason we are testing is purely to get rid of this process of finding a counterexample directly. 

7. (23) -> (1): (23) can be algorithmatically reduced to one expression. The manual effort will be fuzzing (23). It is better than fuzzing (2) in the case without mutation because the fuzzing space is smaller.