include "binary_search_specs.dfy"

lemma FindFirst(intSeq: seq<int>, key: int) returns (r: nat)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    requires exists i : nat | i < |intSeq| :: intSeq[i] == key
    ensures r < |intSeq| && intSeq[r] == key
    ensures forall i: nat | i < r :: intSeq[i] < key
{
    var count := 0;
    while count < |intSeq|
    invariant 0 <= count <= |intSeq|
    invariant forall i: nat | i < count :: intSeq[i] < key
    {
        if (intSeq[count] == key) {
            return count;
        }
        count := count + 1;
    }
}

lemma BinarySearchDeterministicNonRealisticTest(intSeq: seq<int>, key: int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    if (forall i | 0 <= i < |intSeq| :: intSeq[i] != key) {
        assert BinarySearchDeterministicTransition(intSeq, key, -1);
    } else {
        var r := FindFirst(intSeq, key);
        assert BinarySearchDeterministicTransition(intSeq, key, r);
    }
    assert exists r :: BinarySearchDeterministicTransition(intSeq, key, r);
}

lemma deterministicTest(intSeq:seq<int>, key:int)
requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    var r1 := BinarySearchDeterministic(intSeq, key);
    var r2 := BinarySearchDeterministic(intSeq, key);
    assert r1 == r2;
}

lemma BinarySearchDeterministicUnitTest1() {
    // normal case
    var arr := [1,2,3];
    var index := BinarySearchDeterministic(arr,2);
    assert arr[1] == 2;
    assert index == 1;
}

lemma BinarySearchDeterministicUnitTest2() {
    // multiple matches
    var arr := [1,2,2,3];
    var index := BinarySearchDeterministic(arr,2);
    assert arr[1] == 2;
    assert index == 1 || index == 2;
}


lemma BinarySearchDeterministicUnitTest3() {
    // first element
    var arr := [1,2,2,3];
    var index := BinarySearchDeterministic(arr,1);
    assert arr[0] == 1;
    assert index == 0;
}

lemma BinarySearchDeterministicUnitTest4() {
    // last element
    var arr := [1,2,2,3];
    var index := BinarySearchDeterministic(arr,3);
    assert arr[3] == 3;
    assert index == 3;
}

lemma BinarySearchDeterministicUnitTest5() {
    // middle element, odd array
    var arr := [1,2,3,4,5];
    var index := BinarySearchDeterministic(arr,3);
    assert arr[2] == 3;
    assert index == 2;
}

lemma BinarySearchDeterministicUnitTest6() {
    // middle element, odd array
    var arr := [1,2,3,4,4,5];
    var index := BinarySearchDeterministic(arr,3);
    assert arr[2] == 3;
    assert index == 2;
}

lemma BinarySearchDeterministicUnitTest7() {
    // element smaller / equal to mid
    var arr := [1,2,3,4,5,6,7];
    var index := BinarySearchDeterministic(arr, 2);
    assert arr[1] == 2;
    assert index == 1;

    index := BinarySearchDeterministic(arr, 6);
    assert arr[5] == 6;
    assert index == 5;
}

lemma BinarySearchDeterministicUnitTestNotFound1() {
    // empty array
    var arr := [];
    var index := BinarySearchDeterministic(arr,2);
    assert index < 0;
}

lemma BinarySearchDeterministicUnitTestNotFound2() {
    // not found, even array
    var arr := [1,3,4,5,6,7,7,8];
    var index := BinarySearchDeterministic(arr,2);
    assert index < 0;
}

lemma BinarySearchDeterministicUnitTestNotFound3() {
    // not found, odd array
    var arr := [1,3,4,5,6,7,7,8,9];
    var index := BinarySearchDeterministic(arr,2);
    assert index < 0;
}

