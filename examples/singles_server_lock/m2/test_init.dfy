include "spec.dfy"

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
    var c := Constants(5);
    var v := InitLemma(c);
    assert v == Variables(Server, [false, false, false, false, false]);
    assert Safety(c, v);
}

lemma InitUnitTest2() {
    // empty
    var c := Constants(0);
    var v := InitLemma(c);
    assert v == Variables(Server, []);
    assert Safety(c, v);
}

lemma InitUnitTest3() {
    // one element
    var c := Constants(1);
    var v := InitLemma(c);
    assert v == Variables(Server, [false]);
    assert Safety(c, v);
}
