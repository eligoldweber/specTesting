include "ch06exercise02.dfy"

module Test {
    import opened AtomicCommit
    import opened CommitTypes
    import opened UtilitiesLibrary
    
    lemma TestInit() {
        var c0 := Constants(0,[]);
        var v0 := Variables(None, []);
        assert Init(c0, v0);

        var c1 := Constants(1, [Yes]);
        var v1 := Variables(None, [None]);
        assert Init(c1, v1);

        var v1' := Variables(None, [Some(Commit)]);
        assert v1'.participantDecisions[0].Some?;
        assert !Init(c1, v1');

        var v1'' := Variables(Some(Commit), [None]);
        assert !Init(c1, v1'');

        var v1''' := Variables(Some(Commit), [Some(Commit)]);
        assert !Init(c1, v1''');

        var c2 := Constants(5, seq(5, i => Yes));
        var v2 := Variables(None, seq(5, i => None));
        assert Init(c2, v2);

        var v2' := Variables(None, v2.participantDecisions[2 := Some(Commit)]);
        assert v2'.participantDecisions[2].Some?;
        assert !Init(c2, v2');

        var v2'' := Variables(Some(Commit), v2.participantDecisions);
        assert !Init(c2, v2');

        var v2''' := Variables(Some(Commit), v2.participantDecisions[2 := Some(Commit)]);
        assert v2'''.participantDecisions[2].Some?;
        assert !Init(c2, v2''');
    }

    lemma TestCoordinatorDecides() {
        var c0 := Constants(0,[]);
        var v0 := Variables(None, []);
        assert CoordinatorDecides(c0, v0, Variables(Some(Commit), []));
        assert !CoordinatorDecides(c0, v0, Variables(Some(Abort), []));
        
        var c1 := Constants(1, [Yes]);
        var v1 := Variables(None, [None]);
        assert CoordinatorDecides(c1, v1, Variables(Some(Commit), [None]));
        assert !CoordinatorDecides(c1, v1, Variables(Some(Abort), [None]));
        assert !CoordinatorDecides(c1, v1, Variables(None, [Some(Commit)]));
        assert !CoordinatorDecides(c1, v1, Variables(Some(Commit), [Some(Commit)]));

        var c2 := Constants(5, seq(5, i => Yes));
        var v2 := Variables(None, seq(5, i => None));
        assert CoordinatorDecides(c2, v2, Variables(Some(Commit), seq(5, i => None)));
        assert !CoordinatorDecides(c2, v2, Variables(Some(Abort), seq(5, i => None)));

        var v2' := [None, None, None, Some(Commit), None];
        assert v2'[3].Some?;
        assert !CoordinatorDecides(c2, v2, Variables(Some(Commit), v2'));

        var c3 := Constants(5, seq(5, i => No));
        assert c3.preferences[0] == No;
        assert CoordinatorDecides(c3, v2, Variables(Some(Abort), seq(5, i => None)));
        var v3 := [None, None, None, Some(Abort), None];
        assert !CoordinatorDecides(c3, v2, Variables(Some(Abort), v3));

    }
    
    lemma TestParticipantDecides() {
        var c0 := Constants(0,[]);
        var v0 := Variables(None, []);
        assert !ParticipantDecides(c0, v0, v0, 0);
        assert !ParticipantDecides(c0, v0, Variables(Some(Commit), [Some(Commit)]), 0);
        
        var c1 := Constants(1, [Yes]);
        var v1 := Variables(None, [None]);
        assert ParticipantDecides(c1, v1, Variables(None, [Some(Commit)]), 0);
        assert !ParticipantDecides(c1, v1, Variables(Some(Commit), [None]), 0);
        assert !ParticipantDecides(c1, v1, v1, 0);
        
        var c2 := Constants(5, seq(5, i => Yes));
        var v2 := Variables(None, seq(5, i => None));
        var v3 := [None, None, None, Some(Commit), None];
        assert ParticipantDecides(c2, v2, Variables(None, v3), 3);
    }
    
}