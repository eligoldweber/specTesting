include "binary_search_specs.dfy"
lemma BinarySearchWrong3NonRealisticTest(intSeq: seq<int>, key: int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    assert BinarySearchWrong3Transition(intSeq, key, -1);
    assert exists r :: BinarySearchWrong3Transition(intSeq, key, r);
}

lemma deterministicTest(intSeq:seq<int>, key:int)
requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    var r1 := BinarySearchWrong3(intSeq, key);
    var r2 := BinarySearchWrong3(intSeq, key);
    assert r1 == r2;
}

lemma BinarySearchWrong3UnitTest1() {
    // normal case
    var arr := [1,2,3];
    var index := BinarySearchWrong3(arr,2);
    assert arr[1] == 2;
    assert index == 1;
}

lemma BinarySearchWrong3UnitTest2() {
    // multiple matches
    var arr := [1,2,2,3];
    var index := BinarySearchWrong3(arr,2);
    assert arr[1] == 2;
    assert index == 1 || index == 2;
}


lemma BinarySearchWrong3UnitTest3() {
    // first element
    var arr := [1,2,2,3];
    var index := BinarySearchWrong3(arr,1);
    assert arr[0] == 1;
    assert index == 0;
}

lemma BinarySearchWrong3UnitTest4() {
    // last element
    var arr := [1,2,2,3];
    var index := BinarySearchWrong3(arr,3);
    assert arr[3] == 3;
    assert index == 3;
}

lemma BinarySearchWrong3UnitTest5() {
    // middle element, odd array
    var arr := [1,2,3,4,5];
    var index := BinarySearchWrong3(arr,3);
    assert arr[2] == 3;
    assert index == 2;
}

lemma BinarySearchWrong3UnitTest6() {
    // middle element, odd array
    var arr := [1,2,3,4,4,5];
    var index := BinarySearchWrong3(arr,3);
    assert arr[2] == 3;
    assert index == 2;
}

lemma BinarySearchWrong3UnitTest7() {
    // element smaller / equal to mid
    var arr := [1,2,3,4,5,6,7];
    var index := BinarySearchWrong3(arr, 2);
    assert arr[1] == 2;
    assert index == 1;

    index := BinarySearchWrong3(arr, 6);
    assert arr[5] == 6;
    assert index == 5;
}

lemma BinarySearchWrong3UnitTestNotFound1() {
    // empty array
    var arr := [];
    var index := BinarySearchWrong3(arr,2);
    assert index < 0;
}

lemma BinarySearchWrong3UnitTestNotFound2() {
    // not found, even array
    var arr := [1,3,4,5,6,7,7,8];
    var index := BinarySearchWrong3(arr,2);
    assert index < 0;
}

lemma BinarySearchWrong3UnitTestNotFound3() {
    // not found, odd array
    var arr := [1,3,4,5,6,7,7,8,9];
    var index := BinarySearchWrong3(arr,2);
    assert index < 0;
}

