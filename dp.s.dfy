//#title Dining Philosophers
//#desc A more challenging state machine: define the state datatype.

// Define the state machine for the Dining Philosophers.
// There are N philosophers sitting around a round table.
// Between every pair of philosophers lies a chopstick.
// Every philosopher has three possible actions:
//  * Acquire the chopstick to their left.
//  * Acquire the chopstick to their right.
//  * Release both chopsticks (in a single step).

// can I change this spec st. Saftey proof still passes but not live? && deterministic

datatype Constants = Constants(tableSize:nat)

datatype Pair = Pair(left:bool, right:bool)
//Use this datatype to define all the relevant state
datatype Variables = Variables(philosophers:seq<Pair>)

// An initial predicate to define well-formed constants.
// Feel free to add more if you need them
predicate WellFormedConstants(c:Constants) {
    && 0 < c.tableSize
}

// An initial predicate to define well-formed state.
// Feel free to add to this predicate, if necessary
predicate WellFormed(c:Constants, v:Variables) {
    && WellFormedConstants(c)
    && |v.philosophers| == c.tableSize
}

predicate Init(c:Constants, v:Variables) {
    && WellFormed(c, v)
    && (forall pi | 0 <= pi < |v.philosophers| :: v.philosophers[pi] == Pair(false, false))
}

// Philosopher with index pi acquires left chopstick
predicate AcquireLeft(c:Constants, v:Variables, v':Variables, pi:nat) {
    && WellFormed(c, v)
    && pi < c.tableSize
    && !(v.philosophers[pi].left) // prevents this action from being a no-op
    && !(v.philosophers[PhilosopherToTheLeftOf(c,pi)].right) // comment this line to create bug
    && v' == v.(philosophers := v.philosophers[pi := Pair(true, v.philosophers[pi].right)])
    // && v.philosophers[0].l
}

// Philosopher with index pi acquires right chopstick
predicate AcquireRight(c:Constants, v:Variables, v':Variables, pi:nat) {
    && WellFormed(c, v)
    && pi < c.tableSize
    && !(v.philosophers[pi].right) // prevents this action from being a no-op
    && !(v.philosophers[PhilosopherToTheRightOf(c,pi)].left) // comment this line to create bug
    && v' == v.(philosophers := v.philosophers[pi := Pair(v.philosophers[pi].left, true)])
}

// Philosopher with index pi releases both chopsticks
predicate ReleaseBoth(c:Constants, v:Variables, v':Variables, pi:nat) {
    && WellFormed(c, v)
    && pi < c.tableSize
    && (v.philosophers[pi].left)
    && (v.philosophers[pi].right)
    && v' == v.(philosophers := v.philosophers[pi := Pair(false, false)])
}

predicate Next(c:Constants, v:Variables, v':Variables) {
    exists pi:nat ::
    (|| AcquireLeft(c, v, v', pi)
     || AcquireRight(c, v, v', pi)
     || ReleaseBoth(c, v, v', pi))
}

// ND Tests
lemma testNextSteps(c:Constants, v:Variables, pi:nat) returns (v':Variables,v'':Variables)
     ensures !(AcquireLeft(c,v,v',pi) && v' != v'' && AcquireLeft(c,v,v'',pi))
     ensures !(AcquireRight(c,v,v',pi) && v' != v'' && AcquireRight(c,v,v'',pi))
     ensures !(ReleaseBoth(c,v,v',pi) && v' != v'' && ReleaseBoth(c,v,v'',pi))
    {

    }

function PhilosopherToTheLeftOf(c:Constants, philosopher:nat) : nat
    requires WellFormedConstants(c)
{
    (philosopher+1) % c.tableSize
}

function PhilosopherToTheRightOf(c:Constants, philosopher:nat) : nat
    requires WellFormedConstants(c)
{
    (philosopher-1) % c.tableSize
}

// here is the safety property
predicate ForkConsistency(c:Constants, v:Variables)
{
    && WellFormed(c, v)
    && (forall i | 0 <= i < c.tableSize :: !(
        && v.philosophers[i].right
        && v.philosophers[PhilosopherToTheRightOf(c,i)].left
        ))
}

// here is a proof of the safety property. This lemma should verify
// without adding a body
lemma ForkConsistencyLemma()
    ensures forall c, v | Init(c,v) :: ForkConsistency(c, v)
    ensures forall c, v, v' | ForkConsistency(c, v) && Next(c, v, v') :: ForkConsistency(c, v')
{
}

// this predicate and the following lemma are a way to prevent trivial
// specifications of the problem that would prevent a philosopher from
// having both forks
predicate PhilosopherHasBothForks(c:Constants, v:Variables, pi:nat)
    requires pi < c.tableSize
    requires WellFormed(c, v)
{
    && v.philosophers[pi].left
    && v.philosophers[pi].right
}

// lemma CounterPseudoLiveness(c:Constants, pi:nat) returns (behavior:seq<Variables>)
//     requires c.tableSize == 3
//     requires pi == 1
//     ensures 0 < |behavior|
//     ensures Init(c, behavior[0])
//     ensures forall i | 0 <= i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1])
//     ensures WellFormed(c, behavior[|behavior|-1])
//     // ensures PhilosopherHasBothForks(c, behavior[|behavior|-1], pi)
// {
//     var state0 := Variables([Pair(false,false), Pair(false, false), Pair(false, false)]);
//     var state1 := Variables([Pair(false,false), Pair(true, false), Pair(false, false)]);
//     var state2 := Variables([Pair(false,false), Pair(true, false), Pair(false, false)]);
//     var state3 := Variables([Pair(false,false), Pair(true, false), Pair(false, false)]);

//     assert AcquireLeft(c, state0, state1, 1); // witness
//     assert AcquireLeft(c, state1, state2, 1); // witness
//     assert AcquireLeft(c, state2, state3, 1); // witness

//     behavior := [state0, state1, state2,state3];
// }

lemma PseudoLiveness(c:Constants, pi:nat) returns (behavior:seq<Variables>)
    requires c.tableSize == 3
    requires pi == 1
    ensures 0 < |behavior|
    ensures Init(c, behavior[0])
    ensures forall i | 0 <= i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1])
    ensures WellFormed(c, behavior[|behavior|-1])
    ensures PhilosopherHasBothForks(c, behavior[|behavior|-1], pi)
{
    var state0 := Variables([Pair(false,false), Pair(false, false), Pair(false, false)]);
    var state1 := Variables([Pair(false,false), Pair(true, false), Pair(false, false)]);
    var state2 := Variables([Pair(false,false), Pair(true, true), Pair(false, false)]);
    assert AcquireLeft(c, state0, state1, 1); // witness
    assert AcquireRight(c, state1, state2, 1); // witness
    behavior := [state0, state1, state2];
}


// reachability Test

predicate ValidReachableBehavior(c:Constants, b:seq<Variables>,len:int)
    requires len > 0
{
    && |b| == len
    && Init(c,b[0])
    && (forall i :: 0 <= i < |b|-1 ==> Next(c,b[i],b[i+1]))
    // && (forall i :: 0 <= i < |b| ==> ForkConsistency(c,b[i]))
}

lemma WitnessReachableBehavior(c:Constants,b:seq<Variables>) returns (b':seq<Variables>)
    requires |b| > 1
    requires (forall i :: 0 <= i < |b|-1 ==> Next(c,b[i],b[i+1]))
    // requires (forall i :: 0 <= i < |b| ==> ForkConsistency(c,b[i]))
    ensures |b'| > 0
    ensures b' == b[1..]
    ensures Next(c,b[0],b'[0])
{
    var remainder := b[1..];
    assert |remainder| > 0;
    return remainder;
}

lemma PurchaseReachableInNSteps(c:Constants, b:seq<Variables>) returns (v':Variables)
    requires ValidReachableBehavior(c,b,3); 
    // ensures !(Next(c,b[|b|-1],v') && exists pi:nat :: AcquireLeft(c,b[|b|-1],v',pi))
{
    //  var a := WitnessReachableBehavior(c,b);
    //  a := WitnessReachableBehavior(c,a);
    // a := WitnessReachableBehavior(c,a);
}


// limit is 32
lemma AquireLeftReachableInNSteps(c:Constants, b:seq<Variables>,pi:nat)
    requires ValidReachableBehavior(c,b,1); 
    
    requires c.tableSize == 3
    requires pi == 1
    requires WellFormed(c, b[|b|-1])
    requires pi < c.tableSize

    ensures exists v' :: (Next(c,b[|b|-1],v') && exists pi:nat :: AcquireLeft(c,b[|b|-1],v',pi));
{
    //  var a := WitnessReachableBehavior(c,b);
    assert Init(c,b[0]);
    assert !b[0].philosophers[1].left;
    var temp := b[0].(philosophers := b[0].philosophers[1 := Pair(true, b[0].philosophers[1].right)]);
    assert AcquireLeft(c, b[0], temp, 1);
    assert b[0] == b[|b| -1];
    assert Next(c,b[|b|-1],temp);
    // assert exists aa :: Next(c,b[|b|-1],aa);
    //  a := WitnessReachableBehavior(c,a);
    assert exists v' :: (Next(c,b[|b|-1],v') && exists pi:nat :: AcquireLeft(c,b[|b|-1],v',pi));
}
// triviality test


predicate TrivialSequence(c:Constants,b:seq<Variables>)
{
    || forall i :: 0 <= i < |b|-1 ==> b[i] == b[i+1]
}

lemma witnessTrivialBehavior(c:Constants,b:seq<Variables>) returns (b':seq<Variables>)
    requires |b| > 1
    requires (forall i :: 0 <= i < |b|-1 ==> Next(c,b[i],b[i+1]))
    // requires TrivialSequence(c,b)
    ensures |b'| > 0
    ensures b' == b[1..]
    ensures Next(c,b[0],b'[0])
{
    var remainder := b[1..];
    assert |remainder| > 0;
    return remainder;
}

lemma IsTrivial(c:Constants,b:seq<Variables>) returns (b':seq<Variables>)
    // requires |b| > 0
    requires ValidReachableBehavior(c,b,5); 
    ensures !(TrivialSequence(c,b[1..]))
{
    var a := witnessTrivialBehavior(c,b);
     a := witnessTrivialBehavior(c,a);
     a := witnessTrivialBehavior(c,a);
     a := witnessTrivialBehavior(c,a);

} 
 