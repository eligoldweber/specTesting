include "spec.dfy"
// non-deterministic
// unit test

lemma InitLemma(c: Constants) returns (v: Variables)
    ensures v.WellFormed(c)
    ensures v.server.Server?
    ensures forall i:nat | i < |v.client| :: !v.client[i]

lemma InitNonDeterministicTest(c: Constants) {
    var a := InitLemma(c);
    var b := InitLemma(c);
    assert a == b;
}

lemma InitUnitTest1() {
    // normal case
    var v := InitLemma(Constants(5));
    assert v == Variables(Server, [false, false, false, false, false]);
}

lemma InitUnitTest2() {
    // empty
    var v := InitLemma(Constants(0));
    assert v == Variables(Server, []);
}

lemma InitUnitTest3() {
    // one element
    var v := InitLemma(Constants(1));
    assert v == Variables(Server, [false]);
}

// problem: if we specify the correct behavior, then similar to specification
