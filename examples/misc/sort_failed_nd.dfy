predicate IsSorted(seqint:seq<int>)
{
  forall idx :: 0 <= idx < |seqint|-1 ==> seqint[idx] < seqint[idx+1]
}

predicate IsDistinct(seqint: seq<int>)
{
    // forall i, j :: i < j && i in seqint && j in seqint ==> i != j
    forall i,j :: 0 <= i < j < |seqint| ==> seqint[i] != seqint[j]
}

predicate sameElement(seqint1: seq<int>, seqint2: seq<int>)
  requires IsDistinct(seqint1)
  requires IsDistinct(seqint2)
{
  && (forall i | 0 <= i < |seqint1| :: (exists j | 0 <= j < |seqint2| :: seqint1[i] == seqint2[j]))
  && (forall i | 0 <= i < |seqint2| :: (exists j | 0 <= j < |seqint1| :: seqint2[i] == seqint1[j]))
}

//seems that the definition of sort is not perfect enough

lemma sort(input:seq<int>) returns (output:seq<int>)
  requires IsDistinct(input)
  ensures IsDistinct(output)
  ensures IsSorted(output)
  ensures |input|==|output|
  ensures sameElement(input, output)

lemma sort_nd(input:seq<int>)
  requires IsDistinct(input)
{
    var output := sort(input);
    var output' := sort(input);

    assert |output| == |output'|;
    assert IsSorted(output);
    assert IsSorted(output');
    assert IsDistinct(output);
    assert IsDistinct(output');


    assert output == output';
}

  