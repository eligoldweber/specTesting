

//#title Coke Machine
//#desc The first state machine specification exercise: fill in actions.
//#elide
//#elide Its complexity is about the same as the library. We
//#elide provide the boilerplate for everything, but leave the state
//#elide transitions as an exercise.
//#elide It comes with a safety proof that we expect the students to use as an
//#elide oracle for whether they got the state transitions right.

// You are asked to define the state machine for a coke vending machine.
// The machine starts empty and has a maximum capacity of 7 cokes.
// The machine should support the following actions:
// Purchase: dispense one coke from the machine
// Restock: add a number of cokes to the machine

datatype Constants = Constants(capacity:int)
datatype CokeMachine = CokeMachine(numCokes:int)

predicate Init(c:Constants, v:CokeMachine) {
    && c.capacity == 7
    && v.numCokes == 0
}

predicate Purchase(c:Constants, v:CokeMachine, v':CokeMachine) {
    && v.numCokes > 0
    && v'.numCokes == v.numCokes - 1
}
predicate PurchaseStronger(c:Constants, v:CokeMachine, v':CokeMachine) {
    && v.numCokes == 5
    && v'.numCokes == v.numCokes - 1
} 


predicate Restock(c:Constants, v:CokeMachine, v':CokeMachine, numRestock:int)
{
    && numRestock >= 0
    && v.numCokes + numRestock <= c.capacity
    && v'.numCokes == v.numCokes + numRestock
    // && false
}
predicate RestockVac(c:Constants, v:CokeMachine, v':CokeMachine, numRestock:int)
{
    && numRestock >= 0
    && v.numCokes + numRestock <= c.capacity
    && v'.numCokes == v.numCokes + numRestock
    && false
}


predicate Next(c:Constants, v:CokeMachine, v':CokeMachine) {
    || Purchase(c, v, v')
    || (exists num :: Restock(c, v, v', num))
}

//==========================
// Everything below this line is not part of the specification. It allows
// you to use the verifier to confirm that your state machine has a number
// of desirable properties.

lemma isStrongerTransition()
    ensures forall c,v,v',num | RestockVac(c,v,v',num) :: RestockVac(c,v,v',num)
{
}

predicate Inv(c:Constants, v:CokeMachine) {
    0 <= v.numCokes <= c.capacity
}
////
lemma vacousPurchase()
{
    forall c, v, v' | Inv(c, v) && Next(c, v, v')
    {
        // assert (Purchase(c, v, v') ==> false);
    }
}

// lemma vacousRestock()
//     requires (exists num :: Restock(c, v, v', num))
// {
//     forall c, v, v' | var num :| Restock(c, v, v', num);  && Inv(c, v) && Restock(c, v, v', num)
//     {
//         assert (var num :| Restock(c, v, v', num); && Restock(c, v, v', num) ==> false);
//     }
// }

lemma SafetyProof()
    ensures forall c, v | Init(c, v) :: Inv(c, v)
    ensures forall c, v, v' | Inv(c, v) && Next(c, v, v') :: Inv(c, v')
{
    forall c, v, v' | Inv(c, v) && Next(c, v, v')
        ensures Inv(c, v')
    {
        if(Purchase(c, v, v')) {
            assert Inv(c, v');
        } else {
            var num :| Restock(c, v, v', num);
            assert Inv(c, v');
        }
    }
}

// lemma NonTrivialPurchase()
//     ensures exists c, v, v' :: Inv(c, v) && Next(c, v, v') && v'.numCokes + 1 == v.numCokes
// {
//     var c := Constants(7);
//     var v := CokeMachine(1);
//     var v' := CokeMachine(0);
//     assert Inv(c, v) && Next(c, v, v') && v'.numCokes + 1 == v.numCokes;
// }

// lemma NonTrivialRestock()
//     ensures exists c, v, v' :: Inv(c, v) && Next(c, v, v') && v.numCokes < v'.numCokes
// {
//     var c := Constants(7);
//     var v := CokeMachine(4);
//     var v' := CokeMachine(7);
//     assert Restock(c, v, v', 3);
//     assert Inv(c, v) && Next(c, v, v') && v.numCokes < v'.numCokes;

// }

///// SORT EXAMPLE ////

//original 
predicate sortSpec(input:seq<int>, output:seq<int>)
{
   (forall idx :: 0 <= idx < |output|-1 ==> output[idx] <= output[idx+1])
}

//Proof FAILS
predicate strongerSortSpec1(input:seq<int>, output:seq<int>)
{
   && (forall idx :: 0 <= idx < |output|-1 ==> output[idx] <= output[idx+1])
   && |input| == 42
}

//Proof PASSES
predicate strongerSortSpec2(input:seq<int>, output:seq<int>)
{
   && (forall idx :: 0 <= idx < |output|-1 ==> output[idx] < output[idx+1])
}

predicate strongerSortSpec3(input:seq<int>, output:seq<int>)
{
   && (forall idx :: 0 <= idx < |output|-1 ==> output[idx] <= output[idx+1])
   && |input| == |output|
}

//Proof FAILS
predicate correctSpec(input:seq<int>, output:seq<int>)
{
   && (forall idx :: 0 <= idx < |output|-1 ==> output[idx] <= output[idx+1])
   && (multiset(output) == multiset(input))
}

//Proof FAILS
predicate correctSpecStronger1(input:seq<int>, output:seq<int>)
{
   && (forall idx :: 0 <= idx < |output|-1 ==> output[idx] < output[idx+1])
   && (multiset(output) == multiset(input))
}

predicate correctSpecStronger2(input:seq<int>, output:seq<int>)
{
   && (forall idx :: 0 <= idx < |output|-1 ==> output[idx] < output[idx+1])
   && (multiset(output) == multiset(input))
   && |input| == 42
}
// Check to see if 'mutation' is stronger
lemma isStrongerSpec()
    ensures  forall i,o | strongerSortSpec1(i,o) :: sortSpec(i,o);
    ensures  forall i,o | strongerSortSpec2(i,o) :: sortSpec(i,o);
    ensures  forall i,o | correctSpec(i,o) :: sortSpec(i,o);
    ensures  forall i,o | correctSpecStronger1(i,o) :: correctSpec(i,o);
    // ensures  forall i,o | correctSpec(i,o) :: strongerSortSpec3(i,o);

{
}

// proof w/ incorrect impl 
/*
    sortSpec = Pass
    strongerSortSpec1 = FAIL
    strongerSortSpec2 = PASS
    strongerSortSpec3 = FAIL
    correctSpec = FAIL
    correctSpecStronger1 = FAIL
    correctSpecStronger2 = FAIL

    Mutation Score = (Killed Mutants / Total number of Mutants) * 100
    = 5/6 == 83%

*/
lemma sort(input:seq<int>) returns (output:seq<int>)
	ensures (sortSpec(input,output))
{ 
        return [];
}


/*
    sortSpec = PASS
    strongerSortSpec1 = FAIL
    strongerSortSpec2 = FAIL
    strongerSortSpec3 = PASS (WITH ADDITONAL INVARIANT)
    correctSpec = PASS
    correctSpecStronger1 = FAIL
    correctSpecStronger2 = FAIL

    Mutation Score = (Killed Mutants / Total number of Mutants) * 100
    = 5/6 == 83%
    = 4/6 == 66%** 
*/

method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures strongerSortSpec3(input, output)
{
  if |input| <= 1 {
    output := input;
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    var leftSorted := left;
    leftSorted := merge_sort(left);
    var rightSorted := right;
    rightSorted := merge_sort(right);
    output := merge(leftSorted, rightSorted);
    assert left + right == input;
  }
}

predicate IsSorted(seqint:seq<int>)
{
  forall idx :: 0 <= idx < |seqint|-1 ==> seqint[idx] <= seqint[idx+1]
}

method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
  requires IsSorted(seqa)
  requires IsSorted(seqb)
  ensures strongerSortSpec3(seqa+seqb, output)
{
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |seqa| || bi < |seqb|
    invariant 0 <= ai <= |seqa|
    invariant 0 <= bi <= |seqb|
    invariant 0 < |output| && ai < |seqa| ==> output[|output|-1] <= seqa[ai]
    invariant 0 < |output| && bi < |seqb| ==> output[|output|-1] <= seqb[bi]
    invariant forall i :: 0 <= i < |output|-1 ==> output[i] <= output[i+1]
    invariant multiset(output) == multiset(seqa[..ai]) + multiset(seqb[..bi])
    invariant |output| == (|seqa[..ai]| + |seqb[..bi]|) //ADDED
    decreases |seqa|-ai + |seqb|-bi
  {
    ghost var outputo := output;
    ghost var ao := ai;
    ghost var bo := bi;
    if ai == |seqa| || (bi < |seqb| && seqa[ai] > seqb[bi]) {
      output := output + [seqb[bi]];
      bi := bi + 1;
      assert seqb[bo..bi] == [seqb[bo]];  // discovered by calc
    } else {
      output := output + [seqa[ai]];
      ai := ai + 1;
      assert seqa[ao..ai] == [seqa[ao]];  // discovered by calc
    }
    assert seqa[..ai] == seqa[..ao] + seqa[ao..ai];  // discovered by calc
    assert seqb[..bi] == seqb[..bo] + seqb[bo..bi];  // discovered by calc

  }
  assert seqa == seqa[..ai];  // derived by calc
  assert seqb == seqb[..bi];

}

/// "Fuzzing Test" vs Unit // 

lemma sortSpecFuzzing(input:seq<int>, output:seq<int>)
    requires |input| == 2
{
    // assert !(sortSpec(input,output)); //out = []
}

lemma sortSpecUnit()
{
    var input := [4,3,2,2,1];
    var out := [1,2,2,3,4];
    assert sortSpec(input,out);

    //
    assert !correctSpec(input,[]); // This does pass

    // assert !sortSpec(input,[]); // expect this to pass..requires thought 

}