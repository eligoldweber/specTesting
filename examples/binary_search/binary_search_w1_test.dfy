include "binary_search_specs.dfy"
lemma BinarySearchWrong1NonRealisticTest(intSeq: seq<int>, key: int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    assert exists r :: BinarySearchWrong1Transition(intSeq, key, r);
}

lemma deterministicTest_W1(intSeq:seq<int>, key:int)
requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    var r1 := BinarySearchWrong1(intSeq, key);
    var r2 := BinarySearchWrong1(intSeq, key);
    assert r1 == r2;
}

lemma BinarySearchWrong1UnitTest1() {
    // normal case
    var arr := [1,2,3];
    var index := BinarySearchWrong1(arr,2);
    assert arr[1] == 2;
    assert index == 1;
}

lemma BinarySearchWrong1UnitTest2() {
    // multiple matches
    var arr := [1,2,2,3];
    var index := BinarySearchWrong1(arr,2);
    assert arr[1] == 2;
    assert index == 1 || index == 2;
}


lemma BinarySearchWrong1UnitTest3() {
    // first element
    var arr := [1,2,2,3];
    var index := BinarySearchWrong1(arr,1);
    assert arr[0] == 1;
    assert index == 0;
}

lemma BinarySearchWrong1UnitTest4() {
    // last element
    var arr := [1,2,2,3];
    var index := BinarySearchWrong1(arr,3);
    assert arr[3] == 3;
    assert index == 3;
}

lemma BinarySearchWrong1UnitTest5() {
    // middle element, odd array
    var arr := [1,2,3,4,5];
    var index := BinarySearchWrong1(arr,3);
    assert arr[2] == 3;
    assert index == 2;
}

lemma BinarySearchWrong1UnitTest6() {
    // middle element, odd array
    var arr := [1,2,3,4,4,5];
    var index := BinarySearchWrong1(arr,3);
    assert arr[2] == 3;
    assert index == 2;
}

lemma BinarySearchWrong1UnitTest7() {
    // element smaller / equal to mid
    var arr := [1,2,3,4,5,6,7];
    var index := BinarySearchWrong1(arr, 2);
    assert arr[1] == 2;
    assert index == 1;

    index := BinarySearchWrong1(arr, 6);
    assert arr[5] == 6;
    assert index == 5;
}

lemma BinarySearchWrong1UnitTestNotFound1() {
    // empty array
    var arr := [];
    var index := BinarySearchWrong1(arr,2);
    assert index < 0;
}

lemma BinarySearchWrong1UnitTestNotFound2() {
    // not found, even array
    var arr := [1,3,4,5,6,7,7,8];
    var index := BinarySearchWrong1(arr,2);
    assert index < 0;
}

lemma BinarySearchWrong1UnitTestNotFound3() {
    // not found, odd array
    var arr := [1,3,4,5,6,7,7,8,9];
    var index := BinarySearchWrong1(arr,2);
    assert index < 0;
}

