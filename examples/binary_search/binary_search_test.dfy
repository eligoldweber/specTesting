include "binary_search_specs.dfy"
lemma BinarySearchNonRealisticTest(intSeq: seq<int>, key: int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures exists r:: BinarySearchTransition(intSeq, key, r);
{
    if (forall i | 0 <= i < |intSeq| :: intSeq[i] != key) {
        assert BinarySearchTransition(intSeq, key, -1);
    } else {
        assert exists r :: 0 <= r < |intSeq| && intSeq[r] == key && BinarySearchTransition(intSeq, key, r);
    }
}

lemma deterministicTest(intSeq:seq<int>, key:int)
requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    var r1 := BinarySearch(intSeq, key);
    var r2 := BinarySearch(intSeq, key);
    assert r1 == r2;
}

lemma BinarySearchUnitTest1() {
    // normal case
    var arr := [1,2,3];
    var index := BinarySearch(arr,2);
    assert arr[1] == 2;
    assert index == 1;
}

lemma BinarySearchUnitTest2() {
    // multiple matches
    var arr := [1,2,2,3];
    var index := BinarySearch(arr,2);
    assert arr[1] == 2;
    assert index == 1 || index == 2;
}


lemma BinarySearchUnitTest3() {
    // first element
    var arr := [1,2,2,3];
    var index := BinarySearch(arr,1);
    assert arr[0] == 1;
    assert index == 0;
}

lemma BinarySearchUnitTest4() {
    // last element
    var arr := [1,2,2,3];
    var index := BinarySearch(arr,3);
    assert arr[3] == 3;
    assert index == 3;
}

lemma BinarySearchUnitTest5() {
    // middle element, odd array
    var arr := [1,2,3,4,5];
    var index := BinarySearch(arr,3);
    assert arr[2] == 3;
    assert index == 2;
}

lemma BinarySearchUnitTest6() {
    // middle element, odd array
    var arr := [1,2,3,4,4,5];
    var index := BinarySearch(arr,3);
    assert arr[2] == 3;
    assert index == 2;
}

lemma BinarySearchUnitTest7() {
    // element smaller / equal to mid
    var arr := [1,2,3,4,5,6,7];
    var index := BinarySearch(arr, 2);
    assert arr[1] == 2;
    assert index == 1;

    index := BinarySearch(arr, 6);
    assert arr[5] == 6;
    assert index == 5;
}

lemma BinarySearchUnitTestNotFound1() {
    // empty array
    var arr := [];
    var index := BinarySearch(arr,2);
    assert index < 0;
}

lemma BinarySearchUnitTestNotFound2() {
    // not found, even array
    var arr := [1,3,4,5,6,7,7,8];
    var index := BinarySearch(arr,2);
    assert index < 0;
}

lemma BinarySearchUnitTestNotFound3() {
    // not found, odd array
    var arr := [1,3,4,5,6,7,7,8,9];
    var index := BinarySearch(arr,2);
    assert index < 0;
}

