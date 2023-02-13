//====================CORRECT SM===============
datatype Constants = Constants(capacity:int)
datatype CokeMachine = CokeMachine(numCokes:int)

predicate /*A comment*//*A comment*//*A comment*//*First comment*/Init(c:Constants, v:CokeMachine) {
    && c.capacity == 7
    && v.numCokes == 0
}

predicate Purchase(c:Constants, v:CokeMachine, v':CokeMachine) {
    && v.numCokes > 0
    && v'.numCokes == v.numCokes - 1
}


predicate Restock(c:Constants, v:CokeMachine, v':CokeMachine, numRestock:int)
{
    && numRestock >= 0
    && v.numCokes + numRestock <= c.capacity
    && v'.numCokes == v.numCokes + numRestock
}

lemma is_Restock_ND(c:Constants, v:CokeMachine, v':CokeMachine, numRestock:int, v'':CokeMachine)
        requires Restock(c, v, v', numRestock)
        requires Restock(c, v, v'', numRestock)
        ensures  v' ==  v''
{

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
        if(Purchase(c, v, v')) {
            assert Inv(c, v');
        } else {
            var num :| Restock(c, v, v', num);
            assert Inv(c, v');
        }
    }
}

//====================CORRECT SM===============

//========================== Arbitrary Stronger State Transitions ===========
predicate PurchaseStronger(c:Constants, v:CokeMachine, v':CokeMachine) {
    && v.numCokes == 5 // changed from " && v.numCokes > 0"
    && v'.numCokes == v.numCokes - 1
} 

predicate RestockVac(c:Constants, v:CokeMachine, v':CokeMachine, numRestock:int)
{
    && numRestock >= 0
    && v.numCokes + numRestock <= c.capacity
    && v'.numCokes == v.numCokes + numRestock
    && false //Added
}
predicate RestockTrivial(c:Constants, v:CokeMachine, v':CokeMachine, numRestock:int)
{
    && numRestock == 0 // Changed from " && numRestock >= 0"
    && v.numCokes + numRestock <= c.capacity
    && v'.numCokes == v.numCokes + numRestock
}
//Shows that constructed lemmas are stronger than original 
lemma isStrongerTransition()
    ensures forall c,v,v',num | RestockVac(c,v,v',num) :: Restock(c,v,v',num)
    ensures forall c,v,v',num | RestockTrivial(c,v,v',num) :: Restock(c,v,v',num)
    ensures forall c,v,v' | PurchaseStronger(c,v,v') :: Purchase(c,v,v')
{
}

lemma fuzzingPurchaseStronger(c:Constants, v:CokeMachine, v':CokeMachine)
    requires Inv(c,v)
{
    // assert !(PurchaseStronger(c,v,v'));
}
    // c:_module.Constants = Constants(capacity := 43)
    // v:_module.CokeMachine = CokeMachine(numCokes := 5)
    // v':_module.CokeMachine = CokeMachine(numCokes := 4)
        //NOTE: This is not a reachable state b/c Init(c,v) sets the capacity to 7, so having capacity at 43 is not reachable.
        // .    this can be 'fixed' by requiring that (c,v) is a 'reachable' state 
        // .    (the limitation is that it must be 'reachable' in n finite steps, where n is small*)

    // simulated fuzzing with different approach
lemma fuzzingPurchaseStronger1(c:Constants, v:CokeMachine, v':CokeMachine)
    requires Inv(c,v)
    requires v.numCokes != 5
{
    assert !(PurchaseStronger(c,v,v')); //nothing?
    // assert false;
}

lemma fuzzingRestockTrivial(c:Constants, v:CokeMachine, v':CokeMachine,num:int)
requires Inv(c,v)
{
    // assert !RestockTrivial(c,v,v',num);
}
// At "{" (file:///home/edgoldwe/counterExampleTest/specTesting/specMutationTest.s.dfy:99):
//     c:_module.Constants = Constants(capacity := 38)
//     v:_module.CokeMachine = CokeMachine(numCokes := 36, numCokes := 36)
//     v':_module.CokeMachine = v
//     num:int = 0
lemma fuzzingRestockTrivial_ChangingNum(c:Constants, v:CokeMachine, v':CokeMachine,num:int)
    requires Inv(c,v)
    requires num != 0;
{
    assert !RestockTrivial(c,v,v',num);
}

predicate NextArbitrary(c:Constants, v:CokeMachine, v':CokeMachine) {
    || PurchaseStronger(c, v, v')
    || (exists num :: RestockTrivial(c, v, v', num))
}

lemma SafetyProofArbitrary()
    ensures forall c, v | Init(c, v) :: Inv(c, v)
    ensures forall c, v, v' | Inv(c, v) && NextArbitrary(c, v, v') :: Inv(c, v')
{
    forall c, v, v' | Inv(c, v) && NextArbitrary(c, v, v')
        ensures Inv(c, v')
    {
        if(PurchaseStronger(c, v, v')) {
            assert Inv(c, v');
        } else {
            var num :| RestockTrivial(c, v, v', num);
            assert Inv(c, v');
        }
    }
}

//========================== Incorrect Spec w/proof ===========

predicate PurchaseV(c:Constants, v:CokeMachine, v':CokeMachine) {
    && v.numCokes < 0
    && v'.numCokes == v.numCokes - 1
}


predicate NextV(c:Constants, v:CokeMachine, v':CokeMachine) {
    || PurchaseV(c, v, v')
    || (exists num :: Restock(c, v, v', num))
}

lemma areTranistionsVac(c:Constants, v:CokeMachine, v':CokeMachine)
  // requires Inv(c,v)
{
    assert forall c,v,v' | Inv(c, v) && PurchaseV(c,v,v') :: false;
    forall c, v, v' | Inv(c, v) && PurchaseV(c, v, v')
    {
      assert false;
    }
}
// proof still passes 
lemma SafetyProofV()
    ensures forall c, v | Init(c, v) :: Inv(c, v)
    ensures forall c, v, v' | Inv(c, v) && NextV(c, v, v') :: Inv(c, v')
{
    forall c, v, v' | Inv(c, v) && NextV(c, v, v')
        ensures Inv(c, v')
    {
        if(PurchaseV(c, v, v')) {
            assert Inv(c, v');
        } else {
            var num :| Restock(c, v, v', num);
            assert Inv(c, v');
        }
    }
}
//==========================
// Everything below this line is not part of the specification. It allows
// you to use the verifier to confirm that your state machine has a number
// of desirable properties.


predicate StrongerInv(c:Constants, v:CokeMachine) {
    && 0 <= v.numCokes <= c.capacity
    && v.numCokes % 2 == 0
}
lemma StrongerInvIsStronger()
    ensures forall c,v | StrongerInv(c,v) :: Inv(c,v);
{
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


lemma SafetyProofStrongerInv()
    ensures forall c, v | Init(c, v) :: StrongerInv(c, v)
    // ensures forall c, v, v' | Inv(c, v) && Next(c, v, v') :: StrongerInv(c, v')
{
    forall c, v, v' | StrongerInv(c, v) && Next(c, v, v')
        // ensures StrongerInv(c, v')
    {
        if(Purchase(c, v, v')) {
            // assert StrongerInv(c, v');
        } else {
            var num :| Restock(c, v, v', num);
            // assert StrongerInv(c, v');
        }
    }
}

//====================================================================================
///// SORT EXAMPLE ////

//original  
predicate sortSpec(input:seq<int>, output:seq<int>)
{
   (forall idx :: 0 <= idx < |output|-1 ==> output[idx] <= output[idx+1])
}

// method sortSpecMeth(input:seq<int>) returns (output:seq<int>)
// {
//   output :| (forall idx :: 0 <= idx < |output|-1 ==> output[idx] <= output[idx+1]);
// }

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
predicate correctSpec'(input:seq<int>, output:seq<int>)
{
   && (forall idx :: 0 <= idx < |output|-1 ==> output[idx] <= output[idx+1])
   && (forall i :: i in input <==> i in output)
   && |input| == |output|
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
    // ensures  forall i,o | sortSpec(i,o) :: strongerSortSpec2(i,o);
    ensures  forall i,o | correctSpec(i,o) :: sortSpec(i,o);
    ensures  forall i,o | correctSpecStronger1(i,o) :: correctSpec(i,o);
    // ensures  forall i,o | correctSpec(i,o) :: strongerSortSpec3(i,o);

{
}

// proof w/ incorrect impl 
/*
    (wrong) sortSpec = Pass
    
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
   (wrong) sortSpec = PASS

    strongerSortSpec1 = FAIL
    strongerSortSpec2 = FAIL
    strongerSortSpec3 = PASS (WITH ADDITONAL INVARIANT) -- FAIL

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
    assert correctSpec(input,out);
    //
    assert !correctSpec(input,[]); // This does pass

    // assert !sortSpec(input,[]); // expect this to pass..requires thought 

}


//// Abstract Functions/Lemmas //ie. axioms 

lemma {:axiom} sorts(input:seq<int>) returns (out:seq<int>)
    ensures correctSpec(input,out)

function {:axiom}givesSort(input:seq<int>) : (out:seq<int>)
    ensures correctSpec(input,out)

lemma correctSpecIsDeterministic(input:seq<int>,out:seq<int>,out':seq<int>)
    requires input == [4,3,2,2,1];
    requires correctSpec(input,out)
    requires correctSpec(input,out')
    requires out' != [-8098,1,2,3,4]
    requires out == [1,2,2,3,4]
    // ensures out == out'
{
    assert (forall idx :: 0 <= idx < |out|-1 ==> out[idx] <= out[idx+1]);
    assert (forall idx :: 0 <= idx < |out'|-1 ==> out'[idx] <= out'[idx+1]);
    assert out[1] <= out[2]; 
    assert out[0] <= out[1]; 
    assert out[2] <= out[3]; 
    assert out[3] <= out[4]; 

    assert out'[1] <= out'[2]; 
    assert out'[0] <= out'[1]; 
    assert out'[2] <= out'[3]; 
    assume out'[3] <= out'[4]; 
    assert multiset(input) == multiset(out); 
    assert multiset(input) == multiset(out'); 
    assert multiset{1,2,2,3,4} == multiset(input);

    assert  multiset(out) ==  multiset(out');
    assert multiset{1,2,2,3,4} == multiset(out);
    assert multiset{1,2,2,3,4} == multiset(out');
    // assert multiset{1,2,2,3,4} == multiset{1,2,3,4,4};
    // assert multiset{1,2,3,4,4} == multiset(out');
    assert out == [1,2,2,3,4];
     multisetSequence(out,multiset(out));
    multisetSequence(out',multiset(out'));
    multisetSequence(input,multiset(input));

    // assert out' == [1,2,2,3,4];
    //  assert multiset{1,1,2,3,4} == multiset(out);
    // assert out == out';
    // assert false;
}
lemma seqAreEqualIfMultiSetIsEqual(a:seq<int>,b:seq<int>)
    requires multiset(a) == multiset(b);
{
    multisetSequence(a,multiset(a));
    assert |a| == |b|;

}

lemma multisetSequence(nums: seq<int>, ms: multiset<int>) 
    requires multiset(nums) == ms;
    ensures multiset(nums) == ms 
    ensures |nums| == |ms|
{
}


lemma correctSpecIsWeird(input:seq<int>,out:seq<int>)
    requires input == [4,3,2,2,1];
    // requires correctSpec(input,out)
    requires out == [1,1,2,3,4]
    // ensures out == out'
{
    assert (forall idx :: 0 <= idx < |out|-1 ==> out[idx] <= out[idx+1]);
    assert out[1] <= out[2]; 
    assert out[0] <= out[1]; 
    assert out[2] <= out[3]; 
    assert out[3] <= out[4]; 
    // assert multiset(input) == multiset(out);
    assert multiset{1,1,2,3,4} == multiset(out);
    assert multiset{1,2,2,3,4} == multiset(input);
    // assert correctSpec(input,out);
}

lemma sortsTest()
{
    var input := [4,3,2,2,1];
    var out := sorts(input);
    assert sortSpec(input,out); // this is meaningless 
    assert correctSpec(input,out); 
    assert multiset(input) == multiset{1,2,2,3,4};
    // assert multiset(input) == multiset{1,2,3,4};
    var o := [-8098, 1, 2, 3, 4];
    // assert multiset(input) == multiset(o);
    // assert correctSpec(input,o); 
    // assert out == [1,2,2,3,4];
    // assert out == []; 
}

// At "{" (file:///home/edgoldwe/counterExampleTest/specTesting/specMutationTest.s.dfy:418):
//     input:seq<int> = [4, 3, 2, 2, 1]
//     out:seq<int> = [-8098, 1, 2, 3, 4]
//     out':seq<int> = (Length := 5, [0] := 2, [1] := 3, [2] := 4, [4] := 1)

// At "{" (file:///home/edgoldwe/counterExampleTest/specTesting/specMutationTest.s.dfy:418):
//     input:seq<int> = [4, 3, 2, 2, 1]
//     out:seq<int> = (Length := 5, [0] := 1, [1] := 3, [3] := 2, [4] := 4)
//     out':seq<int> = (Length := 5, [0] := 2, [1] := 3, [3] := 1, [4] := 4)

// At "{}" (file:///home/edgoldwe/counterExampleTest/specTesting/specMutationTest.s.dfy:418):
//     input:seq<int> = [4, 3, 2, 2, 1]
//     out:seq<int> = (Length := 5, [0] := 4, [2] := 1, [3] := 2, [4] := 3)
//     out':seq<int> = (Length := 5, [0] := 3, [2] := 1, [3] := 2, [4] := 4)

// At "{" (file:///home/edgoldwe/counterExampleTest/specTesting/specMutationTest.s.dfy:421):
//     input:seq<int> = ()
//     out:seq<int> = ()
//     o:seq<int> = ()

// At "var input := [4,3,2,2,1];" (file:///home/edgoldwe/counterExampleTest/specTesting/specMutationTest.s.dfy:422):
//     input:seq<int> = [4, 3, 2, 2, 1]
//     out:seq<int> = ()
//     o:seq<int> = ()

// At "var out := sorts(input);" (file:///home/edgoldwe/counterExampleTest/specTesting/specMutationTest.s.dfy:423):
//     input:seq<int> = [4, 3, 2, 2, 1]
//     out:seq<int> = (Length := 5, [0] := 1, [1] := 3, [3] := 2, [4] := 4)
//     o:seq<int> = ()

// At "var o := [1,2,2,3,4];" (file:///home/edgoldwe/counterExampleTest/specTesting/specMutationTest.s.dfy:428):
//     input:seq<int> = [4, 3, 2, 2, 1]
//     out:seq<int> = (Length := 5, [0] := 1, [1] := 3, [3] := 2, [4] := 4)
//     o:seq<int> = [1, 2, 2, 3, 4]