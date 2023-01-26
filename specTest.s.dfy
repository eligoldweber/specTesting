module specTest {

// *** MAX ***
// spec
predicate maxTestSpec(a:int,b:int,c:int)
{
	&& c >= a
	&& c >= b
}

predicate maxTestSpecFull(a:int,b:int,c:int)
{
	&& c >= a
	&& c >= b
    && (c == a || c == b)
}

lemma deterministicTest(a:int,b:int) returns (c:int,d:int)
    // ensures !(maxTestSpec(a,b,c) && d != c && maxTestSpec(a,b,d))
{
}

lemma deterministicTestFull(a:int,b:int) returns (c:int,d:int)
    ensures !(maxTestSpecFull(a,b,c) && d != c && maxTestSpecFull(a,b,d))
{
}
// body
lemma max(a:int,b:int) returns (c:int)
    //   ensures (maxTestSpec(a,b,c))
{
}

// method test

method maxMethod(a:int,b:int) returns (c:int)
    // ensures maxTestSpec(a,b,c)
    ensures c >= a && c >= b;
{
    var x :| x >= a && x >= b;
    return x;
} 

method maxMethodFull(a:int,b:int) returns (c:int)
    // ensures maxTestSpec(a,b,c)
    ensures c >= a && c >= b && (c == a || c == b) ;
{
    var x :| x >= a && x >= b && (x == a || x == b) ;
    return x;
} 

// method testMaxMethod(a:int,b:int)
// {
//     var c := maxMethod(a,b);
//     var d := maxMethod(a,b);
//     assert c == d;
// }


method testMaxMethodFull(a:int,b:int)
{
    var c := maxMethodFull(a,b);
    var d := maxMethodFull(a,b);
    assert c == d;
}


// "Unit Tests"
predicate maxTestSpec_simple()
{
    maxTestSpec(0,0,0)
}

predicate maxTestSpec_a_is_larger()
{
    maxTestSpec(42,0,42)
}

predicate maxTestSpec_b_is_larger()
{
    maxTestSpec(42,100,100)
}

predicate maxTestSpec_c_is_smaller()
{
    maxTestSpec(42,100,0)
}

predicate maxTestSpec_c_is_larger_ne()
{
    maxTestSpec(1,2,4)
}

lemma max_tests()
{
    assert maxTestSpec_simple();
    assert maxTestSpec_a_is_larger();
    assert maxTestSpec_b_is_larger();
    assert !maxTestSpec_c_is_smaller();
    assert maxTestSpec_c_is_larger_ne();
}

// *** SORT ***

predicate sortSpec(input:seq<int>, output:seq<int>)
{
   (forall idx :: 0 <= idx < |output|-1 ==> output[idx] <= output[idx+1])
}

lemma sort(input:seq<int>) returns (output:seq<int>)
	// ensures (sortSpec(input,output))
{
}

predicate sortTestSpec_simple()
{
    sortSpec([5,4,3,2,1],[1,2,3,4,5])
}

predicate sortTestSpec_empty()
{
    sortSpec([],[])
}

predicate sortTestSpec_empty_out()
{
    sortSpec([5,4,3,2,1],[])
}

lemma sort_tests()
{
    assert sortTestSpec_simple();
    assert sortTestSpec_empty();
    // assert !sortTestSpec_empty_out();
}

}