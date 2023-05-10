include "exercise02.dfy" 

module TestSafetyAC1 {
    import opened UtilitiesLibrary
    import opened CommitTypes
    import ParticipantHost
    import CoordinatorHost
    import opened DistributedSystem
    import opened Obligations

    lemma Test1_SafetyAC1()
    {
        // a positive forall does not need supplement
        var cc:Host.Constants := Host.CoordinatorConstants(CoordinatorHost.Constants(5));
        var pc:seq<Host.Constants> := seq(5, i requires i >= 0 => Host.ParticipantConstants(ParticipantHost.Constants(i, Yes)));
        var c := Constants(pc + [cc], Network.Constants);

        var cv:Host.Variables := Host.CoordinatorVariables(CoordinatorHost.Variables(Some(Commit), seq(5, i => Some(Yes))));
        var pv:seq<Host.Variables> := seq(5, i => Host.ParticipantVariables(ParticipantHost.Variables(Some(Commit))));
        var v := Variables(pv + [cv], Network.Variables({}));

        assert SafetyAC1(c, v);
    }

    lemma TestInvalid1_SafetyAC1()
    {
        // Host differs
        var cc:Host.Constants := Host.CoordinatorConstants(CoordinatorHost.Constants(5));
        var pc:seq<Host.Constants> := seq(5, i requires i >= 0 => Host.ParticipantConstants(ParticipantHost.Constants(i, Yes)));
        var c := Constants(pc + [cc], Network.Constants);

        var cv:Host.Variables := Host.CoordinatorVariables(CoordinatorHost.Variables(Some(Abort), seq(5, i => Some(Yes))));
        var pv:seq<Host.Variables> := seq(5, i => Host.ParticipantVariables(ParticipantHost.Variables(Some(Commit))));
        var v := Variables(pv + [cv], Network.Variables({}));
        
        // need witness for this - a negation of forall need a witness
        assert GetDecisionForHost(Last(v.hosts)).Some? && GetDecisionForHost(Last(v.hosts)).value.Abort?;
        assert GetDecisionForHost(v.hosts[0]).Some? && GetDecisionForHost(v.hosts[0]).value.Commit?;

        assert !SafetyAC1(c, v);
    }

    lemma TestInvalid2_SafetyAC1()
    {
        // One of the participant differs
        var cc:Host.Constants := Host.CoordinatorConstants(CoordinatorHost.Constants(5));
        var pc:seq<Host.Constants> := seq(5, i requires i >= 0 => Host.ParticipantConstants(ParticipantHost.Constants(i, Yes)));
        var c := Constants(pc + [cc], Network.Constants);

        var cv:Host.Variables := Host.CoordinatorVariables(CoordinatorHost.Variables(Some(Commit), seq(5, i => Some(Yes))));
        var pv:seq<Host.Variables> := seq(5, i => Host.ParticipantVariables(ParticipantHost.Variables(Some(Commit))));
        var pv2 := pv[2 := Host.ParticipantVariables(ParticipantHost.Variables(Some(Abort)))];
        var v := Variables(pv2 + [cv], Network.Variables({}));
        
        // need witness for this - a negation of forall need a witness
        assert GetDecisionForHost(Last(v.hosts)).Some? && GetDecisionForHost(Last(v.hosts)).value.Commit?;
        assert GetDecisionForHost(v.hosts[2]).Some? && GetDecisionForHost(v.hosts[2]).value.Abort?;

        assert !SafetyAC1(c, v);
    }
}