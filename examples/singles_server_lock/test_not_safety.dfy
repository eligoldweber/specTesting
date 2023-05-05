include "spec.dfy"
lemma SafetyTest1() {
    var c := Constants(3);
    var v := Variables(Server, [true, true, true]);
    assert v.client[0];
    assert v.client[1];
    assert !Safety(c, v);
}

lemma SafetyTest2() {
    var c := Constants(3);
    var v := Variables(Client(1), [true, false, false]);

    assert Safety(c, v);
}

lemma SafetyTest3() {
    var c := Constants(3);
    var v := Variables(Client(1), [true, true, false]);
    assert v.client[0];
    assert v.client[1];
    assert !Safety(c, v);
}