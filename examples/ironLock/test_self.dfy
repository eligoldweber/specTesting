include "service.dfy"

lemma Service_Self_Test() {

    var serverAddresses := {EndPoint([1,2]),EndPoint([1]),EndPoint([3,4]),EndPoint([4])};
    var s := ServiceState'({EndPoint([1,2]),EndPoint([1]),EndPoint([3,4]),EndPoint([4])}, [EndPoint([1])]);
    var s' := ServiceState'({EndPoint([1,2]),EndPoint([1]),EndPoint([3,4]),EndPoint([4])}, [EndPoint([1]), EndPoint([1])]);

    // original spec
    assert Service_Next(s, s');

    // new lock holder
    assert s.history == s'.history[..|s'.history| - 1];
    assert !Service_Next_More_Constrained(s, s');
}
