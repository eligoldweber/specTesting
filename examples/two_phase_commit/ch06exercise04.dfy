//#title Refinement proof for 2PC
//#desc Show that Two Phase Commit refines the Atomic Commit sate machine spec.

// This proof shouldn't be terribly brutal, since you have a roadmap for the
// relevant invariants from chapter05. You can discard the AC properties (since
// those are proven about the spec in exercise03, and therefore about any state
// machine that refines the spec).

include "ch06exercise02.dfy"
//#extract ch06exercise02.template solution ch06exercise02.dfy

// Copy chapter05/{CommitTypes,exercise01,exercise02,exercise03}.dfy into the
// current directory. (This inclusion of your chapter 5 work, by the way, is why
// the exercises in this chapter have fancy new conflict-resistant filenames.)
include "exercise03.dfy" 
//#extract ../../chapter05-distributed-state-machines/exercises/exercise03.template solution exercise03.dfy

// This Dafny "abstract module" establishes the proof obligations for the
// refinement: later in the file you will be obligated to fill in the function
// and lemma bodies in a module that `refines` this one.
// (This structure is a nice way to separate the statement of the theorem from
// its proof.)
abstract module RefinementTheorem {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened TwoPCInvariantProof
  import AtomicCommit

  function ConstantsAbstraction(c: DistributedSystem.Constants) : AtomicCommit.Constants
    requires c.WF()

  function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : AtomicCommit.Variables
    requires v.WF(c)

  predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

  lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    requires DistributedSystem.Init(c, v)
    ensures Inv(c, v)
    ensures AtomicCommit.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))

  lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables)
    requires DistributedSystem.Next(c, v, v')
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || VariablesAbstraction(c, v) == VariablesAbstraction(c, v')

}

module RefinementProof refines RefinementTheorem {
  // No imports needed because we inherited them from the abstract module RefinementTheorem
  import opened Obligations
  import opened CoordinatorHost
  
  // Here are some handy accessor functions for dereferencing the coordinator
  // and the participants out of the sequence in Hosts.
  function CoordinatorConstants(c: DistributedSystem.Constants) : CoordinatorHost.Constants
    requires c.WF()
  {
    Last(c.hosts).coordinator
  }

  function CoordinatorVars(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : CoordinatorHost.Variables
    requires v.WF(c)
  {
    Last(v.hosts).coordinator
  }

  // Here's a handy function to save you some typing.
  function ParticipantCount(c: DistributedSystem.Constants) : nat
    requires c.WF()
  {
/*{*/
    CoordinatorConstants(c).participantCount // this may change, depending on your implementation
/*}*/
  }

  // The main challenge of setting up a refinement: abstracting from the
  // low-level (protocol) state to the high-level (spec) state.
  function ConstantsAbstraction(c: DistributedSystem.Constants) : AtomicCommit.Constants
  {
/*{*/
    var participantCount := CoordinatorConstants(c).participantCount;
    var preferences:seq<Vote> := seq(ParticipantCount(c), idx requires 0 <= idx < ParticipantCount(c) => c.hosts[idx].participant.preference);
    AtomicCommit.Constants(participantCount, preferences)
/*}*/
  }

  function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : AtomicCommit.Variables
  {
/*{*/
    var coordinatorDecision:Option<Decision> := CoordinatorVars(c, v).decision;
    var participantDecisions:seq<Option<Decision>> := seq(ParticipantCount(c), idx requires 0 <= idx < ParticipantCount(c) => v.hosts[idx].participant.decision);
    AtomicCommit.Variables(coordinatorDecision, participantDecisions)
/*}*/
  }

  predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
  {
    // Just point at the invariant from the chapter05 proof (in exercise03).
    // Be certain to fully-qualify the invariant name (mention its module
    // explicily) to avoid inadvertently referring to the shadowing definition
    // RefinementTheorem.Inv.
/*{*/
    // property of the whole state variables ==> same as chapter05
    TwoPCInvariantProof.Inv(c, v)
/*}*/
  }

  lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    // Obligations inherited from RefinementTheorem.RefinementInit
    // requires DistributedSystem.Init(c, v)
    // ensures Inv(c, v)
    // ensures AtomicCommit.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
  {
  }

  lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables)
    // Obligations inherited from RefinementTheorem.RefinementNext
    // requires DistributedSystem.Next(c, v, v')
    // requires Inv(c, v)
    // ensures Inv(c, v')
    // ensures AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || VariablesAbstraction(c, v) == VariablesAbstraction(c, v')
  {
    // Advice: appeal to the existing proof to get Inv(c, v')!
/*{*/
    var hostStep :| DistributedSystem.NextStep(c, v, v', hostStep);
    assert Host.Next(c.hosts[hostStep.hostid], v.hosts[hostStep.hostid], v'.hosts[hostStep.hostid], hostStep.msgOps);
    var hostC := c.hosts[hostStep.hostid];
    var hostV := v.hosts[hostStep.hostid];
    var hostV' := v'.hosts[hostStep.hostid];
    if (hostC.CoordinatorConstants?) {
      var step :| CoordinatorHost.NextStep(hostC.coordinator, hostV.coordinator, hostV'.coordinator, step, hostStep.msgOps);
      match step
      {
        case BroadCastStep | ReceiveStep => assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
        case DecideStep => assert AtomicCommit.NextStep(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), AtomicCommit.CoordinatorDecidesStep()) by {
          // assert Decide(hostC.coordinator, hostV.coordinator, hostV'.coordinator, hostStep.msgOps);
          assert (forall i:nat | i < ParticipantCount(c) :: Last(v.hosts).coordinator.votes[i].value == ConstantsAbstraction(c).preferences[i]);
          // assert hostV'.coordinator.decision.value == AtomicCommit.UltimateDecision(ConstantsAbstraction(c));
        }
      }
    } else {
      assert hostC.ParticipantConstants?;
      var step :| ParticipantHost.NextStep(hostC.participant, hostV.participant, hostV'.participant, step, hostStep.msgOps);
      match step
      {
        case VoteStep => {
          if hostC.participant.preference == No {
            assert ConstantsAbstraction(c).preferences[hostStep.hostid] == No;
            assert AtomicCommit.NextStep(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), AtomicCommit.ParticipantDecidesStep(hostStep.hostid));
          } else {
            assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
          }
        }
        case CommitDecisionStep => assert AtomicCommit.NextStep(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), AtomicCommit.ParticipantDecidesStep(hostStep.hostid)) by {
          // assert hostV'.participant.decision.value == Commit;
          // assert Last(v.hosts).coordinator.decision.value == Commit;
          assert forall i:nat | i < ParticipantCount(c) :: Last(v.hosts).coordinator.votes[i].value == ConstantsAbstraction(c).preferences[i] == Yes;
          // assert AtomicCommit.UltimateDecision(ConstantsAbstraction(c)) == Commit;
        }
      }

    }
/*}*/

    // The "new" part of this proof is to explain which AtomicCommit
    // (spec-level) action happened in response to each 2PC (protocol-level)
    // action. So the general strategy is: use skolemization (var :|) to "learn"
    // which thing happened in the DistributedSystem, split the cases, and
    // assert the right AtomicCommit.NextStep() predicate. Mostly, Dafny needs
    // those asserts because they're witnesses to the `exists` in AtomicCommit.Next().
/*{*/
/*}*/
  }
}
