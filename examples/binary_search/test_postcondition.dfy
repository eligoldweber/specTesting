include "binary_search_specs.dfy"

predicate pre_binary(intSeq:seq<int>, key:int)
{
    forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
}

predicate post_binary(intSeq:seq<int>, key:int, r:int)
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
}

/// to establish its usefulness ///
lemma post_binary_point()
{
    var intSeq:seq<int> := [0,1,2];
    var key:int :| key in intSeq;

    var ret := BinarySearch(intSeq, key);
    assert ret == key;

    var r:int :| r > key;
    assert !post_binary(intSeq, key, r);

    intSeq := [0,1,2];
    key :| (key >= 3);
    r :| r >= 0;
    assert !post_binary(intSeq, key, r);

    intSeq := [];
    key :| true;
    r :| r >= 0;
    assert !post_binary(intSeq, key, r);

    intSeq := [1];
    key := 1;
    r :| r > 0;
    assert !post_binary(intSeq, key, r);

    r :| r < 0;
    assert intSeq[0] == 1;
    assert !post_binary(intSeq, key, r);

    ret := BinarySearch(intSeq, key);
    assert ret == 0;

    intSeq := [1];
    key := 2;
    r :| r > 0;
    assert !post_binary(intSeq, key, r);
}

lemma post_binary_point_1(intSeq:seq<int>, key:int, r:int)
    requires intSeq == [0,1,2]
    requires key in intSeq
    requires r != key
    ensures !post_binary(intSeq, key, r)
{

}

lemma post_binary_point_2(intSeq:seq<int>, key:int, r:int)
    requires intSeq == [1,2,2,4]
    requires key == 2
    requires r != 1 && r != 2
    ensures !post_binary(intSeq, key, r)
{
    assert intSeq[2] == 2;
}


/// to make sure it can be proven ///
lemma test_post_binary_non_realistic_point()
{
    var intSeq:seq<int> := [0,1,2];
    var key:int :| key in intSeq;
    var r := key;
    assert post_binary(intSeq, key, r);

    intSeq := [0,1,2];
    key :| key > 3;
    r := -1;
    assert post_binary(intSeq, key, r);

    intSeq := [];
    key :| true;
    r := -1;
    assert post_binary(intSeq, key, r);

    intSeq := [1];
    key := 2;
    r := -1;
    assert post_binary(intSeq, key, r);

}

lemma post_binary_non_realistic_point_1(intSeq:seq<int>, key:int, r:int)
    requires intSeq == [0,1,2]
    requires key in intSeq
    requires r == key
    ensures post_binary(intSeq, key, r)
{

}