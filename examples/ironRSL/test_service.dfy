include "service.dfy"

import opened Native__NativeTypes_s

lemma TestInit() {
    var serverAddresses:set<EndPoint> := {EndPoint([0]), EndPoint([0, 0])};
    var ss := ServiceState'(serverAddresses, [], {}, {});
    assert Service_Init(ss, serverAddresses);

    var ss2 := ServiceState'(serverAddresses, [1], {}, {});
    assert !Service_Init(ss2, serverAddresses);
    
}

lemma TestExecute() {

}

