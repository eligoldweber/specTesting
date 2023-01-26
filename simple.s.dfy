

module sort {

// function intSet() : set<int>
// {
// 		set x:int |-0x80 <= x < 0x80 
// }

// predicate Spec(input:seq<int>, output:seq<int>)
// 	//   requires |output| == |input|
// 	requires |input| > 0
// {
//    (forall idx :: 0 <= idx < |output|-1 ==> output[idx] <= output[idx+1])
//     //   && recurseIntWitness(output)
// 	//   && lessthan(output)
//       && (|output| == |input|)
// 	//   && |input| == 5
// 	//   && recurseIntWitness(output[2..])
// 	&& recurseIntWitness(output)
// 	&& forall i :: 0 <= i < |output| ==> recurseIntWitness(output[i..])

// 	//   && output[0] <= output[1]
// 	//   && output[1] <= output[2]
// 	// && exists i :: i in input && i in intSet()
// 	//   && forall i :: i in input ==> i in intSet()
//    //    && (forall x :: x in input ==> x in output)
//      && (multiset(output) == multiset(input))
// 	// && input[0] in output
// 	// && input[1] in output
// 	// && multisetRecurse(input,output)
// 	// && forall i :: 0 <= i < |input| ==> multisetRecurse(input[i..],output)
//    }

// predicate lessthan(a:seq<int>)
// 	decreases |a|
// {
// 	if |a| < 2 then
// 		true
// 	else
// 		(a[0] <= a[1]) && lessthan(a[1..])
// }

// predicate recurseIntWitness(a:seq<int>)
// 	decreases |a|
// {
// 	if |a| == 0 then
// 		true
// 	else
// 		(a[0] in intSet()) && recurseIntWitness(a[1..])
// }

// predicate intWitness(i:int)
// {
// 	i in intSet()
// }

// predicate multisetRecurse(a:seq<int>, b:seq<int>)
// {
// 	if |a| == 0 then 
// 		true
// 	else	
// 		a[0] in b && multisetRecurse(a[1..],b)
// }

// lemma sort(input:seq<int>) returns (output:seq<int>)
//     requires |input| > 5
// 	requires recurseIntWitness(input)
// 	requires forall i :: 0 <= i < |input| ==> recurseIntWitness(input[i..])
// 	// requires forall i :: 0 <= i < |input| ==> intWitness(input[i])
// 	// requires recurseIntWitness(input[])
// 	// requires exists out1:seq<int> :: (forall idx :: 0 <= idx < |out1|-1 ==> out1[idx] <= out1[idx+1]);
// 	// requires forall x :: x in input ==> x > 0 && x < 10
// 	// requires
// 	ensures !(Spec(input,output))
// 	{
// 	}

predicate testSpec(a:int,b:int)
{
	b > a
	  // && b < 10
	&& (b != 40)
	&& (b != 41)
	&& (a != 1)
	&& b == a + a
	&& b < 10
}

lemma double(a:int) returns (b:int)
      requires a > 0
      	       // ensures !testSpec(a,b)
	       {

}


predicate maxTestSpec(a:int,b:int,c:int)
{
	&& c >= a
	&& c >= b
	      //
	// && b > a
	// && (a  !=-38)
	// && (a  !=-37)
		// &&(c == a || c == b || c == 0)
		// && (a < 0 && b < 0 ==> c == 0)
}

lemma max(a:int,b:int) returns (c:int)
      ensures !(maxTestSpec(a,b,c))
    {

	}

lemma maxBody(a:int,b:int) returns (c:int)
      ensures !(maxTestSpec(a,b,c))
    {
		if (a >= b)
		{
			return a;
		}else{
			return b+1;
		}
	}

method a(s:seq<int>) 
requires |s| == 4 
{
assert s[0] != 4;
}

      method a1(s1:string, s2:string) 
	  requires |s1| == 1 && |s2| == 1 
	  {
        var sCat:string := s2 + s1;
        assert sCat[0] != 'a' || sCat[1] != 'b';
      }

	    method test(value:int)
		 {
        var m := map[3 := -1];
        var b := m[3] == -1;
        m := m[3 := value];
        assert b && m[3] <= 0;
      }
}