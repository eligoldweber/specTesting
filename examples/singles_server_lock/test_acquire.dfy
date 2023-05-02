include "spec.dfy"

lemma AcquireLemma(c: Constants, v: Variables, index: nat) returns (v': Variables)
  requires v.WellFormed(c)
  requires index < c.numClient
  requires v.server.Server?
  ensures v'.WellFormed(c)
  ensures v'.server.Client?
  ensures v'.server.index == index
  ensures v'.client == v.client[index := true]

lemma AcquireNonDeterministicTest(c: Constants, v: Variables, index: nat)
  requires v.WellFormed(c)
  requires index < c.numClient
  requires v.server.Server?
{
    var a := AcquireLemma(c, v, index);
    var b := AcquireLemma(c, v, index);
    assert a == b;
}

// how to know a state is reachable or not ==> invariant

// invariant and safety condition proof is a way to test correctness of the specification

lemma AcquireUnitTest1() {
    // init normal case
    var c := Constants(5);
    var v := Variables(Server, [false, false, false, false, false]);
    var index := 0;
    var v' := AcquireLemma(c, v, index);
    assert v' == Variables(Client(0), [true, false, false, false, false]);
}

lemma AcquireUnitTest2() {
    // init one element case
    var c := Constants(1);
    var v := Variables(Server, [false]);
    var index := 0;
    var v' := AcquireLemma(c, v, index);
    assert v' == Variables(Client(0), [true]);
}

lemma AcquireUnitTest3() {
    var c := Constants(5);
    var v := Variables(Client(2), [false, false, true, false, false]);
    // var v' := AcquireLemma(c, v, 2);
    // assert v' == Variables(Client(0), [true]);
    // is it meaningful to test precondition?
}
