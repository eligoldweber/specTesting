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
/// to make sure it can be called ///
lemma test_pre_binary_point(key:int)
{
    var intSeq:seq<int> := [];
    assert pre_binary(intSeq, key);

    intSeq := [1];
    assert pre_binary(intSeq, key);

    intSeq := [1,2,4];
    assert pre_binary(intSeq, key);

    intSeq := [1,2,2,4];
    assert pre_binary(intSeq, key);

}

// an exportable form of the preceding lemma 
lemma test_pre_binary_point_1(intSeq:seq<int>, key:int)
    requires intSeq == []
    ensures pre_binary(intSeq, key)
{
    
}

lemma test_pre_binary_property(intSeq:seq<int>, key:int)
    requires forall i, j | 0 <= i < j < |intSeq| :: intSeq[i] < intSeq[j] 
    // note that this is a slightly stronger version than the precondition of binary search
    ensures pre_binary(intSeq, key);
{
}


/// non-realistic test ///
lemma test_pre_binary_non_realistic(intSeq:seq<int>, key:int)
    requires pre_binary(intSeq, key)
    ensures exists r :: post_binary(intSeq, key, r)
{
    if (forall i | 0 <= i < |intSeq| :: intSeq[i] != key) {
        assert post_binary(intSeq, key, -1);
    } else {
        var r :| 0 <= r < |intSeq| && intSeq[r] == key;
        assert post_binary(intSeq, key, r);
    }
}

/// non-realistic: pre-conditions only ///
lemma test_pre_binary_non_realistic_point(key:int)
{
    var intSeq:seq<int> := [3,2,1];
    assert intSeq[0] > intSeq[1];
    assert !pre_binary(intSeq, key);

    intSeq := [1,3,2];
    assert intSeq[1] > intSeq[2];
    assert !pre_binary(intSeq, key);

    intSeq := [5,3];
    assert intSeq[0] > intSeq[1];
    assert !pre_binary(intSeq, key);
}

lemma test_pre_binary_non_realistic_point_1(intSeq:seq<int>, key:int)
    requires intSeq == [3,2,1]
    ensures !pre_binary(intSeq, key)
{
    assert intSeq[0] > intSeq[1];
}