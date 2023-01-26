module sm {

datatype Constants = Constants(capacity:int)
datatype CokeMachine = CokeMachine(numCokes:int)


predicate Init(c:Constants, v:CokeMachine) {
    && c.capacity == 7
    // && v.numCokes == -1
    && v.numCokes == 0
}

predicate Purchase(c:Constants, v:CokeMachine, v':CokeMachine) {
    && v.numCokes > 0
    && v'.numCokes == v.numCokes - 1
}

predicate Restock(c:Constants, v:CokeMachine, v':CokeMachine, numRestock:int)
{
    //normal
    && numRestock > 0
    && v.numCokes + numRestock <= c.capacity
    // && v'.numCokes == numRestock
    && v'.numCokes == v.numCokes + numRestock
    
    //satisfies proof, but too strong! 

}

predicate Next(c:Constants, v:CokeMachine, v':CokeMachine) {
    || Purchase(c, v, v')
    || (exists num :: Restock(c, v, v', num))
}


predicate Inv(c:Constants, v:CokeMachine) {
    0 <= v.numCokes <= c.capacity
}

lemma SafetyProof()
    ensures forall c, v | Init(c, v) :: Inv(c, v)
    ensures forall c, v, v' | Inv(c, v) && Next(c, v, v') :: Inv(c, v')
{
    forall c, v, v' | Inv(c, v) && Next(c, v, v')
        ensures Inv(c, v')
    {
        // assert Next(c,v,v') ==> false;
        if(Purchase(c, v, v')) {
            assert Inv(c, v');
        } else {
            var num :| Restock(c, v, v', num);
            assert Inv(c, v');
        }
    }
}

// "UNIT LIKE" tests

predicate sm_test_basic()
{
    var c := Constants(7);
    var v := CokeMachine(0);
    Inv(c,v)
}

predicate sm_test_more_basic_inv()
{
    var c := Constants(7);
    var v := CokeMachine(0);
    Inv(c,v)
}


predicate sm_test_next2()
{
    var c := Constants(7);
    var v := CokeMachine(-1);
    exists v' :: Next(c,v,v')
}

predicate init_satisfies_inv()
{
    forall c,v :: Init(c,v) ==> Inv(c,v)
}


lemma testSM()
{
    var c := Constants(7);
    var v := CokeMachine(-1);
    
    var v' := CokeMachine(3);

    assert Restock(c,v,v',4);
    assert exists n ::  Restock(c,v,v',n);
    var n :| Restock(c,v,v',n);
    assert Restock(c,v,v',n);
    assert !Purchase(c,v,CokeMachine(-2));
    assert Next(c,v,v');
    assert sm_test_next2();
}

lemma tests()
{
    assert sm_test_basic();
    assert sm_test_more_basic_inv();
    // assert sm_test_next();
    assert init_satisfies_inv();

}


}





