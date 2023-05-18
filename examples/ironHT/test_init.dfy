include "HT.s.dfy"

module TestInit {
    import opened SHT__HT_s
    lemma test1() {
        var h:map<int,int> := map[];
        assert SpecInit(h);
    }
    lemma test2() {
        var h:map<Key,Value> := map[1 := 1];
        assert 1 in h;
        assert !SpecInit(h);
    }
    lemma test3() {
        var s := {1,2,3,4,5};
        var h:map<Key,Value> := map i | i in s :: i;
        assert 2 in h;
        assert !SpecInit(h);
    }
}

module TestSet {
    import opened SHT__HT_s
    import opened Collections__Maps2_s
    lemma test1() {
        var h:map<int,int> := map[];
        var ov := ValueAbsent();
        assert Set(h, h, 0, ov);
    }
    lemma test_p1() {
        var ov := ValueAbsent();
        
        forall h:map<int,int>, i:int | !(i in h)
            ensures Set(h,h,i,ov)
        {}
    }
    lemma test2() { // remove element
        // normal case
        var s := {1,2,3,4,5};
        var h:map<Key,Value> := map i | i in s :: i;
        var s' := {1,2,4,5};
        var h':map<Key,Value> := map i | i in s' :: i;
        assert Set(h, h', 3, ValueAbsent());

        // map does not change - invalid
        assert 3 in h;
        assert !Set(h, h, 3, ValueAbsent());

        // map changes other way - invalid

        // another element deleted
        var s'' := {1,4,5};
        var h'':map<Key,Value> := map i | i in s'' :: i;
        assert 2 in mapremove(h, 3);
        assert !Set(h, h'', 3, ValueAbsent());

        // other elements' value changes
        var s''' := {1,2,4,5};
        var h''':map<Key,Value> := map i | i in s''' :: i + 1;
        assert !Set(h,h''', 3, ValueAbsent);

        // this element's value changes but not deleted
        var s'''' := {1,2,3,4,5};
        var h'''':map<Key,Value> := map[1:=1, 2:=2, 3:=4, 4:=4, 5:=5];
        assert !Set(h,h'''', 3, ValueAbsent);
    }

    lemma test3() { // set value
        var s := {1,2,3,4,5};
        var h:map<Key,Value> := map i | i in s :: i;
        var s' := {1,2,3,4,5,6};
        var h':map<Key,Value> := map i | i in s' :: i;

        // new value
        assert Set(h, h', 6, ValuePresent(6));
        
        // more value
        var h_ := h'[7:=7];
        assert 7 in h_;
        assert !Set(h, h_, 6, ValuePresent(6));

        // less value
        var h__ := map[6:=6];
        assert !(1 in h__);
        assert !Set(h, h__, 6, ValuePresent(6));

        // change value
        var h'' := h[2:=5];
        assert Set(h, h'', 2, ValuePresent(5));

        // value unchanged
        assert Set(h, h, 2, ValuePresent(2));

    }

    lemma Set_Lemma(h:Hashtable, k:Key, ov:OptionalValue) returns (h':Hashtable)
        ensures if ov.ValuePresent? then
            h' == h[k := ov.v]
          else
            h' == mapremove(h, k)

    lemma NonDeterministic(h:Hashtable, k:Key, ov:OptionalValue) {
        var a := Set_Lemma(h, k, ov);
        var b := Set_Lemma(h, k, ov);
        assert a == b;
        assert exists h':Hashtable :: Set(h, h', k, ov) by {
            if (ov.ValuePresent?) {
                assert Set(h, h[k := ov.v], k, ov);
            } else {
                assert Set(h, mapremove(h, k), k, ov);
            }
        }
        var h1 :| Set(h, h1, k, ov);
        var h2 :| Set(h, h2, k, ov);
        assert h1 == h2;
    }

}

module TestGet {
    import opened SHT__HT_s
    import opened Collections__Maps2_s
    lemma Get_Lemma(h:Hashtable, k:Key) returns (h':Hashtable, ov:OptionalValue)
        ensures h' == h
        ensures ov == if k in h then ValuePresent(h[k]) else ValueAbsent()
    lemma NonDeterministic(h:Hashtable, k:Key) {
        var h1, ov1 := Get_Lemma(h, k);
        var h2, ov2 := Get_Lemma(h, k);
        assert h1 == h2;
        assert ov1 == ov2;
    }
    lemma test_p1(h:Hashtable, k:Key, h':Hashtable, ov:OptionalValue)
        requires k in h
        requires Get(h, h', k, ov)
        ensures h' == h
        ensures ov.ValuePresent?
        ensures ov.v == h[k]
        {}
    lemma test_p2(h:Hashtable, k:Key, h':Hashtable, ov:OptionalValue)
        requires !(k in h)
        requires Get(h, h', k, ov)
        ensures h' == h
        ensures ov.ValueAbsent?
        {}
}
