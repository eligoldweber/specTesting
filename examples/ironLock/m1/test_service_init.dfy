include "service.dfy"

// lemma pradigm
lemma Service_Init_Lemma(serverAddresses:set<EndPoint>) returns (s:ServiceState)
    ensures s.hosts == serverAddresses
    ensures exists e:: e in serverAddresses && s.history == [e]

// for non-deterministic spec, can only check general properties
lemma Service_Init_Lemma_Test1() {
    var serverAddresses := {EndPoint([1,2]),EndPoint([1]),EndPoint([3,4]),EndPoint([4])};
    var s := Service_Init_Lemma(serverAddresses);
    assert s.history[0] in s.hosts;
    assert s.history[0] in serverAddresses;
}

// point check
// well-suited for non-deterministic spec
// valid cases
lemma Service_Init_Test1() {
    // normal case
    var serverAddresses := {EndPoint([1,2]),EndPoint([1]),EndPoint([3,4]),EndPoint([4])};
    var s := ServiceState'({EndPoint([1,2]),EndPoint([1]),EndPoint([3,4]),EndPoint([4])}, [EndPoint([1])]);
    assert Service_Init(s, serverAddresses);
}

lemma Service_Init_Test2() {
    // only one host
    var serverAddresses := {EndPoint([1])};
    var s := ServiceState'({EndPoint([1])}, [EndPoint([1])]);
    assert Service_Init(s, serverAddresses);
}

lemma Service_Init_Test3() {
    // only one host
    var serverAddresses := {EndPoint([1])};
    var s := ServiceState'({EndPoint([1])}, [EndPoint([1])]);
    assert Service_Init(s, serverAddresses);
}


// invalid cases
lemma Service_Init_Test_Invalid1() {
    // no hosts
    var serverAddresses := {};
    var s := ServiceState'({}, [EndPoint([1])]);
    assert !Service_Init(s, serverAddresses);
}

lemma Service_Init_Test_Invalid2() {
    // history not in hosts
    var serverAddresses := {EndPoint([0]), EndPoint([2])};
    var s := ServiceState'({EndPoint([0]), EndPoint([2])}, [EndPoint([1])]);
    assert !Service_Init(s, serverAddresses);
}


lemma Service_Init_Test_Invalid3() {
    // empty history
    var serverAddresses := {EndPoint([0]), EndPoint([2])};
    var s := ServiceState'({EndPoint([0]), EndPoint([2])}, []);
    assert !Service_Init(s, serverAddresses);
}

lemma Service_Init_Test_Invalid4() {
    // |history| > 1 but both in hosts
    var serverAddresses := {EndPoint([0]), EndPoint([2])};
    var s := ServiceState'({EndPoint([0]), EndPoint([2])}, [EndPoint([0]), EndPoint([2])]);
    assert !Service_Init(s, serverAddresses);
}

lemma Service_Init_Test_Invalid5() {
    // |history| > 1 and some in hosts
    var serverAddresses := {EndPoint([0]), EndPoint([2])};
    var s := ServiceState'({EndPoint([0]), EndPoint([2])}, [EndPoint([0]), EndPoint([1])]);
    assert !Service_Init(s, serverAddresses);
}

lemma Service_Init_Test_Invalid6() {
    // |history| > 1 and not in hosts
    var serverAddresses := {EndPoint([0]), EndPoint([2])};
    var s := ServiceState'({EndPoint([0]), EndPoint([2])}, [EndPoint([3]), EndPoint([1])]);
    assert !Service_Init(s, serverAddresses);
}

lemma Service_Init_Test_Invalid7() {
    // serverAddresses != hosts
    var serverAddresses := {EndPoint([1]), EndPoint([3])};
    var s := ServiceState'({EndPoint([0]), EndPoint([2])}, [EndPoint([3]), EndPoint([1])]);
    assert !Service_Init(s, serverAddresses);
}


// kind of like writing c < 100 in the max example
lemma Service_Init_Property1(s:ServiceState, serverAddresses:set<EndPoint>)
    requires Service_Init(s, serverAddresses)
{
    // assert serverAddresses == s.hosts;
    assert s.history[0] in s.hosts;
    // assert s.history[0] in serverAddresses;
}
