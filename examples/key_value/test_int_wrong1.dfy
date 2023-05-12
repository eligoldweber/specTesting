include "key_value_int_wrong1.dfy"

module Test { 
    import opened Types
    import opened MapSpec


    lemma TestInit() {
        // normal case
        var v := Variables(map key | key in AllKeys() :: DefaultValue());
        assert Init(v);

        // one of the element is not equal to DefaultValue
        var v2 := Variables(v.mapp[2 := 1]);
        assert v2.mapp[2] == 1;
        assert !Init(v2); // a not forall equal ==> need a witness

        // reassign one of the variable to 0, do not need a witness
        var v3 := Variables(v.mapp[2 := 0]);
        assert Init(v3);
        
    }

    lemma TestInsert() {
        // normal case
        var v := Variables(map key | key in AllKeys() :: DefaultValue());
        var v2 := Variables(v.mapp[2 := 1]);
        assert InsertOp(v, v2, 2, 1);

        var v3 := Variables(v2.mapp[3 := 1]);

        assert InsertOp(v2, v3, 3, 1);

        assert v3.mapp[3] == 1;
        assert !InsertOp(v, v3, 2, 1);

        var v4 := Variables(v3.mapp[11 := 2]);
        assert !InsertOp(v3, v4, 11, 2);
    }

    lemma TestQuery() {
        var v := Variables(map key | key in AllKeys() :: DefaultValue());
        var v2 := Variables(v.mapp[2 := 1]);
        var v3 := Variables(v2.mapp[3 := 1]);

        assert QueryOp(v, v, 1, 0);

        // no forall / exists ==> do not need a witness
        assert !QueryOp(v, v, 1, 1);

        // an implicit forall / exists here because of map
        assert v.mapp[2] != v2.mapp[2];
        assert !QueryOp(v, v2, 1, 0);

        assert !QueryOp(v, v, 11, 0);

        assert QueryOp(v2, v2, 1 , 0);
        assert QueryOp(v2, v2, 2, 1);
        assert !QueryOp(v2, v2, 2, 0);

        var v4 := Variables(v3.mapp[11 := 2]);
        assert !QueryOp(v3, v4, 11, 2);
    }
}
