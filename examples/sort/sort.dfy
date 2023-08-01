method quickSort(intSeq:array<int>)
    modifies intSeq
    ensures forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
    ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))

predicate post_sort(prevSeq:seq<int>, curSeq:seq<int>)
{
    && (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    && multiset(prevSeq) == multiset(curSeq)
}

// to check it is functioning
// postcondition
// iterate cases from the point of view of inputs' variation
lemma test_post_sort_point_1(prevSeq:seq<int>, curSeq:seq<int>)
    requires |curSeq| != |prevSeq|
    ensures !post_sort(prevSeq, curSeq)
{
    assert |multiset(curSeq)| != |multiset(prevSeq)|;
}

lemma test_post_sort_point_2(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [3,2,1]
    requires |curSeq| != |prevSeq|
    ensures !post_sort(prevSeq, curSeq)
{}

lemma test_post_sort_point_3(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [3,2,1]
    requires post_sort(prevSeq, curSeq)
    ensures curSeq == [1,2,3]
{}

lemma test_post_sort_point_4(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == []
    requires curSeq != []
    ensures !post_sort(prevSeq, curSeq)
{
    assert |multiset(prevSeq)| != |multiset(curSeq)|;
}

lemma test_post_sort_point_5'(prevSeq:seq<int>, curSeq:seq<int>)
    requires |prevSeq| == 1
    requires curSeq != prevSeq
    ensures !post_sort(prevSeq, curSeq)
{
    assert post_sort(prevSeq, [prevSeq[0]]);
}

// sometimes a specific case is easier to prove
lemma test_post_sort_point_5(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1]
    requires curSeq != prevSeq
    ensures !post_sort(prevSeq, curSeq)
{}

lemma test_post_sort_point_6(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,2,3,4]
    requires curSeq != prevSeq
    ensures !post_sort(prevSeq, curSeq)
{}

lemma test_post_sort_point_7(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,3,2,4]
    requires curSeq != [1,2,3,4]
    ensures !post_sort(prevSeq, curSeq)
{}

lemma test_post_sort_point_8(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [4,3,2,1]
    requires curSeq != [1,2,3,4]
    ensures !post_sort(prevSeq, curSeq)
{}

lemma test_post_sort_point_9(prevSeq:seq<int>, curSeq:seq<int>)
    requires forall i:nat, j:nat | i <= j < |prevSeq| :: prevSeq[i] <= prevSeq[j]
    requires curSeq != prevSeq
    // ensures !post_sort(prevSeq, curSeq)
{
    // assert post_sort(prevSeq, prevSeq);
    // if (|curSeq| == |prevSeq|) {

    // } else {
    //     assert |multiset(prevSeq)| != |multiset(curSeq)|;
    // }
}

// to check it is implementable
lemma test_post_sort_realistic_point_1(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == []
    requires curSeq == []
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_2(prevSeq:seq<int>, curSeq:seq<int>)
    requires |prevSeq| == 1
    requires curSeq == prevSeq
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_3(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,2,3,4]
    requires curSeq == prevSeq
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_4(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [1,3,2,4]
    requires curSeq == [1,2,3,4]
    ensures post_sort(prevSeq, curSeq)
{
}

lemma test_post_sort_realistic_point_5(prevSeq:seq<int>, curSeq:seq<int>)
    requires prevSeq == [4,3,2,1]
    requires curSeq == [1,2,3,4]
    ensures post_sort(prevSeq, curSeq)
{
}

lemma multisetAdditivity(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
    requires m1 == m2 + m3
    requires m1 == m2 + m4
    ensures m3 == m4
    {
        assert m3 == m1 - m2;
        assert m4 == m1 - m2;
    }


lemma twoSortedSequencesWithSameElementsAreEqual(s1:seq<int>, s2:seq<int>)
    requires (forall i:nat, j:nat | 0 <= i <= j < |s1| :: s1[i] <= s1[j])
    requires (forall i:nat, j:nat | 0 <= i <= j < |s2| :: s2[i] <= s2[j])
    requires multiset(s1) == multiset(s2)
    requires |s1| == |s2|
    ensures s1 == s2
{
    if (|s1| != 0) {
        if s1[|s1|-1] == s2[|s2|-1] {
        assert multiset(s1[..|s1|-1]) == multiset(s2[..|s2|-1]) by {
            assert s1 == s1[..|s1|-1] + [s1[|s1|-1]];
            assert multiset(s1) == multiset(s1[..|s1|-1]) + multiset([s1[|s1|-1]]);

            assert s2 == s2[..|s1|-1] + [s2[|s1|-1]];
            assert multiset(s2) == multiset(s2[..|s1|-1]) + multiset([s2[|s1|-1]]);

            assert multiset([s1[|s1|-1]]) == multiset([s2[|s1|-1]]);

            multisetAdditivity(multiset(s1), multiset([s1[|s1|-1]]), multiset(s1[..|s1|-1]), multiset(s2[..|s1|-1]));
        }
        twoSortedSequencesWithSameElementsAreEqual(s1[..|s1|-1], s2[..|s2|-1]);
        } else if s1[|s1|-1] < s2[|s2|-1] {
            assert s2[|s2|-1] !in multiset(s1);
            assert false;
        } else {
            assert s1[|s1|-1] !in multiset(s2);
            assert false;
        }
    }
}

lemma sort_determinisitc(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{
    if (|curSeq| != |curSeq'|) {
        assert |multiset(curSeq)| != |multiset(curSeq')|;
    } else {
        twoSortedSequencesWithSameElementsAreEqual(curSeq, curSeq');
    }
}