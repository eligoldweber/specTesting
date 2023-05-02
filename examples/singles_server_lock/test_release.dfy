include "spec.dfy"

lemma ReleaseLemma(c: Constants, v: Variables, index: nat) returns (v': Variables)
  requires v.WellFormed(c)
  requires index < c.numClient
  requires v.server.Client?
  requires v.server.index == index
  requires v.client[index]
  ensures v'.WellFormed(c)
  ensures v'.server.Server?
  ensures v'.client == v.client[index := false]
  
lemma ReleaseNonDeterministicTest(c: Constants, v: Variables, index: nat)
  requires v.WellFormed(c)
  requires index < c.numClient
  requires v.server.Client?
  requires v.server.index == index
  requires v.client[index]
{
    var a := ReleaseLemma(c, v, index);
    var b := ReleaseLemma(c, v, index);
    assert a == b;
}

lemma ReleaseUnitTest1() {
    // normal case
    var c := Constants(5);
    var v := Variables(Client(1), [false, true, false, false, false]);
    var v' := ReleaseLemma(c, v, 1);
    assert v' == Variables(Server, [false, false, false, false, false]);
}

lemma ReleaseUnitTest2() {
    // init one element case
    var c := Constants(1);
    var v := Variables(Client(0), [true]);
    var index := 0;
    var v' := ReleaseLemma(c, v, index);
    assert v' == Variables(Server, [false]);
}

lemma ReleaseUnitTest3() {
    // missing precondition
    // but in implementation, this lemma should not be run in this case
    var c := Constants(5);
    var v := Variables(Client(1), [false, true, false, false, false]);
    // var v' := ReleaseLemma(c, v, 2);
    // assert v' == Variables(Server, [false, true, false, false, false]);
}
