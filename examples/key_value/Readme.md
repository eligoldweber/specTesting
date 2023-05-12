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

SpecTesting

`key_value_int_spec.dfy` - `test_int_spec.dfy`: original spec and test cases

`key_value_int_wrong*.dfy` - `test_int_wrong*.dfy`: mutated spec and corresponding test cases' behavior


