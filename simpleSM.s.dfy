module simpleSM{


datatype State = State(
    a:int,
    b:int,
    c:int
)


predicate init(v:State)
{
    && v.a == 0
    && v.b == 0
    && v.c == 0    
}

predicate isValid(v:State)
{
    && v.a >= 0
    && v.b >= 0
    && v.c >= 0   
}

predicate isValid2(v:State)
{
    && v.a > 0
    && v.b > 0
    && v.c > 0   
}

predicate next(v:State,v':State)
{
    && v'.a > v.a
    && v'.b == v.b
    && v'.c == v.c
}

predicate nextD(v:State,v':State)
{
    && v'.a == v.a + 42
    && v'.b == v.b
    && v'.c == v.c
}

lemma testNext(v:State,v':State,v'':State)
     requires next(v,v') && next(v,v'')
     ensures v' == v''
    {
        // v'' := v';
    }


// !(Next(v,v') && v' != v'' && Next(v,v''))

lemma testNextD(v:State) 
     ensures forall v', v'' | nextD(v,v') && nextD(v,v'') :: v' == v''
    {

    }


//////////////////// Simple "unit" tests

lemma test1()
{
    var v := State(0,0,0);
    assert init(v);
}

lemma test2()
{
    var v := State(0,0,0);
    var v' := State(42,0,0);
    assert init(v); 
    assert isValid(v) && isValid(v');
    assert nextD(v,v');
}

lemma test3()
{
    var v := State(0,0,0);
    var v' := State(42,0,0);
    assert init(v); 
    assert !(isValid2(v) && isValid2(v'));
    assert nextD(v,v');
}

lemma test4()
{
    var v := State(0,0,0);
    var v' := State(2,0,0);
    assert init(v); 
    assert isValid(v) && isValid(v');
    assert !nextD(v,v');
}

// fuzzing nextD
lemma test_fuzzing(v:State,v':State)
    requires isValid(v) && isValid(v')
    ensures  !nextD(v,v');
{

}

}