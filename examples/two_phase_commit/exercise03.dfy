//#title Two Phase Commit Safety Proof
//#desc Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "exercise02.dfy"
//#extract exercise02.template solution exercise02.dfy

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

/*{*/
/*
  want to prove the protocol is safe
  prove some property on the state machine
  inductive proof
  find some inductive invariant that holds at init and after every transition
  the founded inductive invariant should imply safety property
  why safety itself is not inductive: do not specify something that is essential
  like allow some state to change unexpectedly
  need to specify the state of such state variable
  however, unlike the protocol, the inductive property is going to say something static
  whether a property is inductive is solely related to the Next predicate

  abstraction that does not concern number of steps - static
  all static behavior of a system is the state (all it have is states and transitions, and transitions are dynamic)
  abstraction about the states
  properties about the states

  why it should cover all states - assuming all states are interrelated in implementation
  but two disjoint sets of states that are interrelated only internally may be both needed in safety after all, otherwise why bother having it?
  if some state can go wrong, next step the inv might not hold anymore

  how tight it should be to describe each state: as far as it can go, and whatever makes sense - after all it is describing the desired behavior of the system in a more abstract format

  relationship with safety property: safety should follow from the property as long as it has described the behavior of every single state

*/





  // why is the whole system correct and how does it work
  // why does it work

  // decision agree with decision message
  // decision message agree with decision
  // decisions agree with internal data structure
  // internal data structure agree with message
  // message agree with preference

  // vote messages agree with preference
  predicate VoteMsgsAgreeWithPreference(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall m:Message | m in v.network.sentMsgs && m.VOTE? && m.hostid < |v.hosts| - 1 :: c.hosts[m.hostid].participant.preference == m.vote
  }
  // internal data structure agree with voteMsgs
  predicate VotesAgreeWithVoteMsgs(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall i:nat | i < |c.hosts| - 1 :: Last(v.hosts).coordinator.votes[i].Some? ==> VOTE(i, Last(v.hosts).coordinator.votes[i].value) in v.network.sentMsgs
  }
  // decision agree with internal data structure
  predicate DecisionAgreeWithVotes(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && (if Last(v.hosts).coordinator.decision.Some? && Last(v.hosts).coordinator.decision.value.Commit? // generalizable
      then ((forall i:nat | i < |v.hosts| - 1 :: Last(v.hosts).coordinator.votes[i].Some? && Last(v.hosts).coordinator.votes[i].value.Yes?))
      else !(DECISION(Commit) in v.network.sentMsgs))
    && (if Last(v.hosts).coordinator.decision.Some? && Last(v.hosts).coordinator.decision.value.Abort?
      then (forall i:nat | i < |v.hosts| - 1 :: Last(v.hosts).coordinator.votes[i].Some?) && !(forall i:nat | i < |v.hosts| - 1 :: Last(v.hosts).coordinator.votes[i].value.Yes?)
      else true)
  }

  // if coordinator is commit ==> internal data structure is all yes ==> vote message is all and yes ==> all preference is yes && no abort messages==> noone can abort


  // participant decision agree with DECISION or preference
  predicate ParticipantDecisionAgreeWithDecisionMsgs(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && ((exists i:nat | i < |v.hosts| - 1 :: GetDecisionForHost(v.hosts[i]).Some? && GetDecisionForHost(v.hosts[i]).value.Commit?) ==> DECISION(Commit) in v.network.sentMsgs)// has commit msg
    && (forall i:nat | i < |v.hosts| - 1 && GetDecisionForHost(v.hosts[i]).Some? && GetDecisionForHost(v.hosts[i]).value.Abort? :: (DECISION(Abort) in v.network.sentMsgs) || c.hosts[i].participant.preference.No?)
  }
/*}*/
  // This is a conjunct of the inductive invariant, indicating that the messages carrying
  // decisions should reflect the votes of the participants as relayed to the coordinator
  predicate DecisionMsgsAgreeWithDecision(c: Constants, v: Variables)
    requires v.WF(c)
  {
/*{*/
    forall m:Message | m in v.network.sentMsgs && m.DECISION? :: Last(v.hosts).coordinator.decision.Some? && m.decision == Last(v.hosts).coordinator.decision.value
/*}*/
  }

  predicate Inv(c: Constants, v: Variables)
  {
/*{*/
    && v.WF(c)
    && VoteMsgsAgreeWithPreference(c, v)
    && VotesAgreeWithVoteMsgs(c, v)
    && DecisionAgreeWithVotes(c, v)
    && ParticipantDecisionAgreeWithDecisionMsgs(c, v)
/*}*/
    // We give you the blueprint for one invariant to get you started...
    && DecisionMsgsAgreeWithDecision(c, v)
    // ...but you'll need more.
    // && Safety(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
/*{*/
/*}*/
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
/*{*/
  
/*}*/
  }


  lemma CommitMeansCommit(c: Constants, v: Variables)
      requires Inv(c, v)
      requires Last(v.hosts).coordinator.decision == Some(Commit)
      ensures AllPreferencesAreYes(c)
    {
      // assert (forall i:nat | i < |v.hosts| - 1 :: Last(v.hosts).coordinator.votes[i].Some? && Last(v.hosts).coordinator.votes[i].value.Yes?);

      forall i:nat | i < |v.hosts| - 1
        ensures c.hosts[i].participant.preference == Yes;
      {
        assert Last(v.hosts).coordinator.votes[i].Some? && Last(v.hosts).coordinator.votes[i].value.Yes?;
      }
    }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
    if (Last(v.hosts).coordinator.decision == Some(Commit)) {
      CommitMeansCommit(c, v);
    }
    // assert SafetyAC1(c, v);
    
    // assert SafetyAC3(c, v);
    // assert SafetyAC4(c, v);
  }
}

