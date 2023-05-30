include "../dafny/ver/L1/theorems.dfy"

// trace nat -> DSState

// datatype DSState = DSState(
//         configuration: Configuration,
//         environment: Network,
//         nodes: map<Address, NodeState>,
//         adversary: Adversary
//     )    

module test_consistency {
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_Adversary
    import opened L1_DistributedSystem
    import opened L1_Theorems
    import opened L1_TheoremsDefs
    import opened L1_AuxiliaryFunctionsAndLemmas

    
    function t1(i:nat): DSState
    {
        var h0 := BlockHeader(1, 0, {}, 0, 0);
        var c := Configuration([0,1,2], Block(h0, "", []), 0);
        var env := Network([0,1,2], multiset{}, 0, multiset{});

        var n0 := NodeState([], 0, 0, 0, c, {}, None, None, None, 0);
        var nodes := map[0 := n0, 1 := n0.(id := 1), 2 := n0.(id := 2)];
        var adv := Adversary({}, {});
        var ds := DSState(c, env, nodes, adv);
        ds
    }
    lemma test1() {
        assert consistency(t1);
    }


    function t2(i:nat): DSState
    {
        var header := BlockHeader(1, 0, {}, 0, 0);
        var c := Configuration([1,2,3], Block(header, "", []), 0);
        var env := Network([0,1,2], multiset{}, 0, multiset{});
        var adv := Adversary({}, {});

        var b1 := Block(header, "this is body", ["trans1"]);
        var b2 := Block(header, "empty", ["trans2"]);

    
        var n0 := NodeState([b1, b2], 0, 0, 0, c, {}, None, None, None, 0);
        var nodes := map[0 := n0, 1 := n0.(blockchain := [b1]), 2 := n0];

        DSState(c, env, nodes, adv)
    }
    lemma test2() {
        var header := BlockHeader(1, 0, {}, 0, 0);
        var c := Configuration([1,2,3], Block(header, "", []), 0);
        assert consistency(t2);
    }


    function t3(i:nat): DSState
    {
        var header := BlockHeader(1, 0, {}, 0, 0);
        var c := Configuration([1], Block(header, "", []), 0);
        var env := Network([0,1,2], multiset{}, 0, multiset{});
        var adv := Adversary({}, {});

        var b1 := Block(header, "this is body", ["trans1"]);
        var b2 := Block(header, "empty", ["trans2"]);

    
        var n0 := NodeState([b1, b2], 0, 0, 0, c, {}, None, None, None, 0);
        var nodes := map[0 := n0, 1 := n0.(blockchain := [b1]), 2 := n0.(blockchain := [b2])];

        DSState(c, env, nodes, adv)
    }
    lemma test3() {
        var b1 := t3(0).nodes[1].blockchain;
        var b2 := t3(0).nodes[2].blockchain;

        var rbc1 := fromBlockchainToRawBlockchain(b1);
        var rbc2 := fromBlockchainToRawBlockchain(b2);

        assert !(rbc2[0] in rbc1);

        assert !consistentBlockchains(b1, b2);

        assert !consistency(t3);
    }


}