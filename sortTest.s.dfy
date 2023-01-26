module sort {

function intSet() : set<int>
{
	// set x:int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000
		set x:int | -0x80 <= x < 0x80
}

predicate Spec(input:seq<int>, output:seq<int>)
	//   requires |output| == |input|
	requires |input| > 0
{
   (forall idx :: 0 <= idx < |output|-1 ==> output[idx] <= output[idx+1])
    //   && recurseIntWitness(output)
	//   && lessthan(output)
      && (|output| == |input|)
	//   && |input| == 5
	//   && recurseIntWitness(output[2..])
	&& recurseIntWitness(output)
	&& forall i :: 0 <= i < |output| ==> recurseIntWitness(output[i..])

	//   && output[0] <= output[1]
	//   && output[1] <= output[2]
	// && exists i :: i in input && i in intSet()
	//   && forall i :: i in input ==> i in intSet()
   //    && (forall x :: x in input ==> x in output)
    //  && (multiset(output) == multiset(input))
	// && input[0] in output
	// && input[1] in output
	// && multisetRecurse(input,output)
	// && forall i :: 0 <= i < |input| ==> multisetRecurse(input[i..],output)
   }

predicate lessthan(a:seq<int>)
	decreases |a|
{
	if |a| < 2 then
		true
	else
		(a[0] <= a[1]) && lessthan(a[1..])
}

predicate recurseIntWitness(a:seq<int>)
	requires |a| > 0
	ensures (forall i | 0 <= i < |a| ::  a[i] in intSet()) == recurseIntWitness(a)
	decreases |a|
{
	if |a| == 1 then
		a[0] in intSet()
	else
		(a[0] in intSet()) && recurseIntWitness(a[1..])
}

predicate intWitness(i:int)
{
	i in intSet()
}

predicate multisetRecurse(a:seq<int>, b:seq<int>)
{
	if |a| == 0 then 
		true
	else	
		a[0] in b && multisetRecurse(a[1..],b)
}

lemma sort(input:seq<int>) returns (output:seq<int>)
    requires |input| > 5
	// requires forall i :: i in input ==> i in intSet()
	// requires input[0] in intSet()

	requires recurseIntWitness(input)
	requires forall i :: 0 <= i < |input| ==> recurseIntWitness(input[i..])
	// requires forall i :: 0 <= i < |input| ==> intWitness(input[i])
	// requires recurseIntWitness(input[])
	// requires exists out1:seq<int> :: (forall idx :: 0 <= idx < |out1|-1 ==> out1[idx] <= out1[idx+1]);
	// requires forall x :: x in input ==> x > 0 && x < 10
	// requires
	ensures !(Spec(input,output))
	{

	}

}