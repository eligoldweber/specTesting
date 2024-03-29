//#title Two Phase Commit Safety Specification Predicate
//#desc Express the English Atomic Commit safety properties as predicates
//#desc over the compound state machine model from exercise01.

// 2PC should satisfy the Atomic Commit specification. English design doc:
//
// AC-1: All processes that reach a decision reach the same one.
// AC-3: The Commit decision can only be reached if all processes prefer Yes.
// AC-4: If all processes prefer Yes, then the decision must be Commit.
//
// Note that the full Atomic Commit spec includes these additional properties,
// but you should ignore them for this exercise:
// AC-2: (stability) A process cannot reverse its decision after it has reached one.
//       (best modeled with refinement)
// AC-5: (liveness) All processes eventually decide.

// Note that we include the model of exercise01, so you should write your 
// spec accordingly. Of course, that also means double-checking that your
// model performs all actions as described.
include "exercise01.dfy"
//#extract exercise01.template solution exercise01.dfy
 
module Obligations {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem

/*{*/
predicate AllPreferencesAreYes(c: Constants)
  requires c.WF()
{
  forall i:nat | i < |c.hosts| - 1 :: c.hosts[i].participant.preference == Yes
}

/*}*/

  // AC-1: All processes that reach a decision reach the same one.
  predicate SafetyAC1(c: Constants, v: Variables)
    requires v.WF(c)
  {
    // All hosts that reach a decision reach the same one
/*{*/
    forall i:nat, j:nat | i < j < |v.hosts| :: (GetDecisionForHost(v.hosts[i]).Some? && GetDecisionForHost(v.hosts[j]).Some?) ==> (GetDecisionForHost(v.hosts[i]) == GetDecisionForHost(v.hosts[j]))
/*}*/
  }

  // AC2 is sort of a history predicate; we're going to ignore it.

  // AC-3: The Commit decision can only be reached if all processes prefer Yes.
  predicate SafetyAC3(c: Constants, v: Variables)
    requires v.WF(c)
  {
/*{*/
    (exists i:nat | i < |v.hosts| :: GetDecisionForHost(v.hosts[i]).Some? && GetDecisionForHost(v.hosts[i]).value.Commit?)
      ==> AllPreferencesAreYes(c)
/*}*/
  }

  // AC-4: If all processes prefer Yes, then the decision must be Commit.
  predicate SafetyAC4(c: Constants, v: Variables)
    requires v.WF(c)
  {
/*{*/
    (AllPreferencesAreYes(c))
      ==> (forall i:nat | i < |v.hosts| :: GetDecisionForHost(v.hosts[i]).Some? ==> GetDecisionForHost(v.hosts[i]).value.Commit?)
/*}*/
  }

  // AC5 is a liveness proprety, we're definitely going to ignore it.

  predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    && SafetyAC1(c, v)
    && SafetyAC3(c, v)
    && SafetyAC4(c, v)
  }
}
