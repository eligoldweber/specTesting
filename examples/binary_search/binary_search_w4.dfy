include "binary_search_specs.dfy"

lemma BinarySearchWrong4NonRealisticTest(intSeq: seq<int>, key: int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    assert exists r :: BinarySearchWrong4Transition(intSeq, key, r);
}

lemma BinarySearchWrong4UnitTest1() {
    // normal case
    var arr := [1,2,3];
    var index := BinarySearchWrong4(arr,2);
    assert arr[1] == 2;
    assert index == 1;
}

lemma BinarySearchWrong4UnitTest2() {
    // multiple matches
    var arr := [1,2,2,3];
    var index := BinarySearchWrong4(arr,2);
    assert arr[1] == 2;
    assert index == 1 || index == 2;
}


lemma BinarySearchWrong4UnitTest3() {
    // first element
    var arr := [1,2,2,3];
    var index := BinarySearchWrong4(arr,1);
    assert arr[0] == 1;
    assert index == 0;
}

lemma BinarySearchWrong4UnitTest4() {
    // last element
    var arr := [1,2,2,3];
    var index := BinarySearchWrong4(arr,3);
    assert arr[3] == 3;
    assert index == 3;
}

lemma BinarySearchWrong4UnitTest5() {
    // middle element, odd array
    var arr := [1,2,3,4,5];
    var index := BinarySearchWrong4(arr,3);
    assert arr[2] == 3;
    assert index == 2;
}

lemma BinarySearchWrong4UnitTest6() {
    // middle element, odd array
    var arr := [1,2,3,4,4,5];
    var index := BinarySearchWrong4(arr,3);
    assert arr[2] == 3;
    assert index == 2;
}

lemma BinarySearchWrong4UnitTest7() {
    // element smaller / equal to mid
    var arr := [1,2,3,4,5,6,7];
    var index := BinarySearchWrong4(arr, 2);
    assert arr[1] == 2;
    assert index == 1;

    index := BinarySearchWrong4(arr, 6);
    assert arr[5] == 6;
    assert index == 5;
}

lemma BinarySearchWrong4UnitTestNotFound1() {
    // empty array
    var arr := [];
    var index := BinarySearchWrong4(arr,2);
    assert index < 0;
}

lemma BinarySearchWrong4UnitTestNotFound2() {
    // not found, even array
    var arr := [1,3,4,5,6,7,7,8];
    var index := BinarySearchWrong4(arr,2);
    assert index < 0;
}

lemma BinarySearchWrong4UnitTestNotFound3() {
    // not found, odd array
    var arr := [1,3,4,5,6,7,7,8,9];
    var index := BinarySearchWrong4(arr,2);
    assert index < 0;
}

