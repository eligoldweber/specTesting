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
    // && numRestock > 0
    // && v.numCokes + numRestock <= c.capacity
    // // && v'.numCokes == numRestock
    // && v'.numCokes == v.numCokes + numRestock
    
    //satisfies proof, but too strong! 
    && numRestock == 0
    && v'.numCokes == v.numCokes + numRestock
    && v.numCokes + numRestock <= c.capacity

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

// ND tests
lemma testNext(c:Constants, v:CokeMachine,num:int) returns (v':CokeMachine,v'':CokeMachine)
     ensures !(Purchase(c,v,v') && v' != v'' && Purchase(c,v,v''))
     ensures !(Restock(c,v,v',num) && v' != v'' && Restock(c,v,v'',num))
    {
    }

lemma testNextRevisedPurchased(c:Constants, v:CokeMachine,num:int,v':CokeMachine,v'':CokeMachine)
     requires Purchase(c,v,v') && Purchase(c,v,v'')
     ensures v' == v''
    {
        // v'' := v';
    }

lemma testNextRevisedRestock(c:Constants, v:CokeMachine,num:int,v':CokeMachine,v'':CokeMachine)
     requires Restock(c,v,v',num) && Restock(c,v,v'',num)
     ensures v' == v''
    {
        // v'' := v';
    }

// reachable tests
predicate ValidReachableBehavior(c:Constants, b:seq<CokeMachine>,len:int)
    requires len > 0
{
    && |b| == len
    && Init(c,b[0])
    && (forall i :: 0 <= i < |b|-1 ==> Next(c,b[i],b[i+1]))
    && (forall i :: 0 <= i < |b| ==> Inv(c,b[i]))
}

lemma witnessReachableBehavior(c:Constants,b:seq<CokeMachine>) returns (b':seq<CokeMachine>)
    requires |b| > 1
    requires (forall i :: 0 <= i < |b|-1 ==> Next(c,b[i],b[i+1]))
    requires (forall i :: 0 <= i < |b| ==> Inv(c,b[i]))
    ensures |b'| > 0
    ensures b' == b[1..]
    ensures Next(c,b[0],b'[0])
{
    var remainder := b[1..];
    assert |remainder| > 0;
    return remainder;
}

// is there a satisfying assignemnt s.t. Next(last(b),v') && this next step is a purchase step
    //  ensures forall v', v'' | nextD(v,v') && nextD(v,v'') :: v' == v''
// ensures exists v' | Next(c,b[|b|-1],v') && Purchase(c,b[|b|-1],v')

// limit is 32
lemma PurchaseReachableInNSteps(c:Constants, b:seq<CokeMachine>) returns (v':CokeMachine)
    requires ValidReachableBehavior(c,b,32); 
    ensures !(Next(c,b[|b|-1],v') && Purchase(c,b[|b|-1],v'))
{
     var a := witnessReachableBehavior(c,b);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
    //  a := witnessReachableBehavior(c,a);
}



lemma PurchaseReachableInNStepsSimplified(c:Constants, b:seq<CokeMachine>)returns (v':CokeMachine)
    requires ValidReachableBehavior(c,b,3); 
    ensures !(Next(c,b[|b|-1],v') && Purchase(c,b[|b|-1],v'))
{
    var a := witnessReachableBehavior(c,b);
     a := witnessReachableBehavior(c,a);
}

lemma RestockReachableInNStepsSimplified(c:Constants, b:seq<CokeMachine>)
    requires ValidReachableBehavior(c,b,4); 
    ensures exists v' :: Next(c,b[|b|-1],v') && exists num :: Restock(c, b[|b|-1], v', num)
{
    var a := witnessReachableBehavior(c,b);
     a := witnessReachableBehavior(c,a);
}


lemma RestockReachableInNSteps(c:Constants, b:seq<CokeMachine>) returns (v':CokeMachine)
    requires ValidReachableBehavior(c,b,5); 
    // ensures !(Next(c,b[|b|-1],v') &&  exists num :: Restock(c, b[|b|-1], v', num))
{
     var a := witnessReachableBehavior(c,b);
     a := witnessReachableBehavior(c,a);
     a := witnessReachableBehavior(c,a);
}

//triviality

predicate NON_TrivialSequence(c:Constants,b:seq<CokeMachine>)
{
    // |b| == 1
    !(forall i :: 0 <= i < |b|-1 ==> b[i] == b[i+1])
}


lemma witnessTrivialBehavior(c:Constants,b:seq<CokeMachine>) returns (b':seq<CokeMachine>)
    requires |b| > 1
    requires (forall i :: 0 <= i < |b|-1 ==> Next(c,b[i],b[i+1]))
    ensures |b'| > 0
    ensures b' == b[1..]
    ensures Next(c,b[0],b'[0])
{
    var remainder := b[1..];
    assert |remainder| > 0;
    return remainder;
}

lemma IsTrivial(c:Constants,b:seq<CokeMachine>) returns (b':seq<CokeMachine>)
    // requires |b| > 0
    requires ValidReachableBehavior(c,b,4); 
    // ensures !(TrivialSequence(c,b[1..]))
{
    var a := witnessTrivialBehavior(c,b);
     a := witnessTrivialBehavior(c,a);
     a := witnessTrivialBehavior(c,a);

} 

lemma IsTrivialSimplified(c:Constants, b:seq<CokeMachine>)
    requires ValidReachableBehavior(c,b,4); 
    // ensures NON_TrivialSequence(c,b[1..])
{
    var a := witnessTrivialBehavior(c,b);
    a := witnessTrivialBehavior(c,a);
}
 

}





