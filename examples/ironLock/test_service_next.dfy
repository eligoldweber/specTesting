include "service.dfy"

lemma Service_Next_Test1() {
    var hosts := {EndPoint([1]),EndPoint([2]),EndPoint([3]),EndPoint([4])};
    var s := ServiceState'(hosts, [EndPoint([1])]);
    var s' := ServiceState'(hosts, [EndPoint([1]), EndPoint([2])]);
    assert Service_Next(s, s');
}

lemma Service_Next_Test2() {
    var hosts := {EndPoint([1]),EndPoint([2]),EndPoint([3]),EndPoint([4])};
    var s := ServiceState'(hosts, [EndPoint([1]), EndPoint([2])]);
    var s' := ServiceState'(hosts, [EndPoint([1]), EndPoint([2]), EndPoint([3])]);
    assert Service_Next(s, s');
}


lemma Service_Next_Test_Invalid1() {
    // s.hosts != s'.hosts
    var hosts := {EndPoint([1]),EndPoint([2]),EndPoint([3]),EndPoint([4])};
    var s := ServiceState'(hosts, [EndPoint([1])]);
    var s' := ServiceState'({EndPoint([1]),EndPoint([2]),EndPoint([3])}, [EndPoint([1])]);
    assert !Service_Next(s, s');
}

lemma Service_Next_Test_Invalid2() {
    // unchanged
    var hosts := {EndPoint([1]),EndPoint([2]),EndPoint([3]),EndPoint([4])};
    var s := ServiceState'(hosts, [EndPoint([1])]);
    var s' := ServiceState'(hosts, [EndPoint([1])]);
    assert !Service_Next(s, s');
}

lemma Service_Next_Test_Invalid3() {
    // new lock not in hosts NOTE: need some proof
    var hosts := {EndPoint([1]),EndPoint([2]),EndPoint([3]),EndPoint([4])};
    var s := ServiceState'(hosts, [EndPoint([1])]);
    var s' := ServiceState'(hosts, [EndPoint([1]), EndPoint([5])]);
    assert s'.history[|s.history|] == EndPoint([5]);
    // assert s'.history == s.history + [EndPoint([5])];
    assert !Service_Next(s, s');
}

// generalized test -- check general property
lemma Service_Next_Property_1(s:ServiceState, s':ServiceState)
    requires Service_Next(s, s')
{
    // history changed
    assert |s'.history| == |s.history| + 1;
    assert s'.history[0..|s'.history| - 1] == s.history;
}

lemma Service_Next_Property_2(s:ServiceState, s':ServiceState)
    requires Service_Next(s, s')
{
    // hosts unchanged
    assert s.hosts == s'.hosts;
}

