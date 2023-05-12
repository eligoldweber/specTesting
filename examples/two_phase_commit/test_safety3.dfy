include "exercise02.dfy" 

module TestSafetyAC2 {
    import opened UtilitiesLibrary
    import opened CommitTypes
    import ParticipantHost
    import CoordinatorHost
    import opened DistributedSystem
    import opened Obligations

    lemma Test1_SafetyAC3()
    {
        // a positive forall does not need supplement
        // var c:Constants :| c.WF() && forall i:nat | i < |c.hosts| - 1 :: c.hosts[i].participant.preference == Yes;
        // var v:Variables :| v.WF(c) && Last(v.hosts).coordinator.decision == Some(Commit);

        var cc:Host.Constants := Host.CoordinatorConstants(CoordinatorHost.Constants(5));
        var pc:seq<Host.Constants> := seq(5, i requires i >= 0 => Host.ParticipantConstants(ParticipantHost.Constants(i, Yes)));
        var c := Constants(pc + [cc], Network.Constants);

        var cv:Host.Variables := Host.CoordinatorVariables(CoordinatorHost.Variables(Some(Commit), seq(5, i => Some(Yes))));
        var pv:seq<Host.Variables> := seq(5, i => Host.ParticipantVariables(ParticipantHost.Variables(Some(Commit))));
        var v := Variables(pv + [cv], Network.Variables({}));

        assert SafetyAC3(c, v);
    }

    lemma TestInvalid1_SafetyAC3()
    {
        // exists need a witness
        // Some participant prefers No
        var cc:Host.Constants := Host.CoordinatorConstants(CoordinatorHost.Constants(5));
        var pc:seq<Host.Constants> := seq(5, i requires i >= 0 => Host.ParticipantConstants(ParticipantHost.Constants(i, Yes)));
        var pc2 := pc[2 := Host.ParticipantConstants(ParticipantHost.Constants(2, No))];
        var c := Constants(pc2 + [cc], Network.Constants);

        var cv:Host.Variables := Host.CoordinatorVariables(CoordinatorHost.Variables(Some(Commit), seq(5, i => Some(Yes))));
        var pv:seq<Host.Variables> := seq(5, i => Host.ParticipantVariables(ParticipantHost.Variables(Some(Commit))));
        var v := Variables(pv + [cv], Network.Variables({}));
        
        // need witness for this - a negation of forall need a witness
        assert GetDecisionForHost(Last(v.hosts)).Some? && GetDecisionForHost(Last(v.hosts)).value.Commit?;
        assert c.hosts[2].participant.preference == No;
        // assert !AllPreferencesAreYes(c);

        assert !SafetyAC3(c, v);
    }

    lemma Test2_SafetyAC3()
    {
        // all decisions are abort or none, and preferences are all Nos
        var cc:Host.Constants := Host.CoordinatorConstants(CoordinatorHost.Constants(5));
        var pc:seq<Host.Constants> := seq(5, i requires i >= 0 => Host.ParticipantConstants(ParticipantHost.Constants(i, No)));
        var c := Constants(pc + [cc], Network.Constants);

        var cv:Host.Variables := Host.CoordinatorVariables(CoordinatorHost.Variables(None, seq(5, i => Some(Yes))));
        var pv:seq<Host.Variables> := seq(5, i => Host.ParticipantVariables(ParticipantHost.Variables(Some(Abort))));
        var v := Variables(pv + [cv], Network.Variables({}));
        
        // do not need a witness, this is a forall
        assert SafetyAC3(c, v);
    }
}