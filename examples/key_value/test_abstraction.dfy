include "key_value_int_abstraction.dfy"

module TestAbstraction {
    import opened Types
    import MapSpec
    import opened RefinementProof
    import opened ShardedKVProtocol
    
    lemma test1() {
        var m:map<Key, Value> := map x:nat | x in AllKeys() :: x;
        var sv := MapSpec.Variables(m);

        var c := Constants(5);
        var v := Variables([m, map[], map[], map[], map[]]);

        assert Abstraction(c, v).mapp.Keys == AllKeys() by {
            assert MapDomains(c, v)[0] == AllKeys();
            HostKeysSubsetOfKnownKeys(c, v, c.mapCount);
            KnownKeysSubsetOfHostKeys(c, v);
        }

        forall key | key in AllKeys() 
            ensures AbstractionOneKey(c, v, key) == m[key]
        {
            assert HostHasKey(c, v, 0, key);
        }

        assert !(Abstraction(c, v) == sv);
    }

}