## Refinement Examples

### Sharded Key-Value Store
Refinement-specific

1. `ch06exerciese01.dfy`: the original (correct spec with refinement proof)
2. `key_value_const.dfy`: an example with constant-value spec, variable-to-const abstraction, and correct protocol
    * abstraction may be incorrect
        * all different states in protocol boils down to the same one in the spec
        * a malformed abstraction function may be able to counterfeit the state transition, especially for boolean (or finite) -variable specs
3. `key_value_noop.dfy`: The protocol can only transfer.
    * the protocol might have only implemented a portion of the functionality of the high-level spec (not guaranteed by refinement)
4. `key_value_wrong.dfy`: Query predicate in protocol is incorrect (always return a constant value).
    * protocol's transition with output may not correspond to a transition with output in spec (Noop in this case)
    * key issue:
        * output is not modeled in the state
        * the protocol might have only implemented a portion of the functionality of the high-level spec (not guaranteed by refinement)
        * not trivial to tell which functions have been implemented, and which are not
5. correct spec + incorrect protocol + incorrect abstraction
    * observations: the protocol must have kept all the information that can produce a corresponding state in the correct spec (assume no output)
    * but both the state and the transition might not be "corresponding" in an expected way
    * possible problems:
        * state not corresponding in an expected way (i => i + 1) -- test abstraction function `key_value_int_abstraction.dfy` - `test_abstraction.dfy`
        * transition unspecified (insert => noop) -- "at least mentioned once" in refinement proof (or following the paradigm and check if all are asserted in the desired way) (4.)
        * transition mixedup `increment_decrement.dfy`
        * state and transition both mixed up

SpecTesting

`key_value_int_spec.dfy` - `test_int_spec.dfy`: original spec and test cases

`key_value_int_wrong*.dfy` - `test_int_wrong*.dfy`: mutated spec and corresponding test cases' behavior


