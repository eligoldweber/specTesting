include "service.dfy"

lemma Service_Self_Test() {

    var serverAddresses := {EndPoint([1,2]),EndPoint([1]),EndPoint([3,4]),EndPoint([4])};
    var s := ServiceState'({EndPoint([1,2]),EndPoint([1]),EndPoint([3,4]),EndPoint([4])}, [EndPoint([1])]);
    var s' := ServiceState'({EndPoint([1,2]),EndPoint([1]),EndPoint([3,4]),EndPoint([4])}, [EndPoint([1]), EndPoint([1])]);

    // original spec
    assert Service_Next(s, s');

    // new lock holder
    assert forall new_lock_holder | new_lock_holder in s.hosts :: new_lock_holder == s.history[|s.history| - 1] || s'.history[|s'.history| - 1] != new_lock_holder;
    assert !Service_Next_More_Constrained(s, s');
}
