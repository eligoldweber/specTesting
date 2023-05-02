//#title Single-Server Lock Service Model
//#desc A complex state machine
//#desc including a Safety predicate on the state type.

// Model a lock service that consists of a single server and an
// arbitrary number of clients.
// 
// The state of the system includes the server's state (whether the server
// knows that some client holds the lock, and if so which one)
// and the clients' states (for each client, whether that client knows
// it holds the lock).
// 
// The system should begin with the server holding the lock.
// An acquire step atomically transfers the lock from the server to some client.
// (Note that we're not modeling the network yet -- the lock disappears from
// the server and appears at a client in a single atomic transition.)
// A release step atomically transfers the lock from the client back to the server.
// 
// The safety property is that no two clients ever hold the lock
// simultaneously.

datatype Constants = Constants(
/*{*/ // You define this ...
    numClient : nat
/*}*/
) {
  predicate WellFormed() { true }
/*{*/
/*}*/
}

/*{*/
datatype ServerState = Server | Client(index: nat)
/*}*/

datatype Variables = Variables(
/*{*/ // You define this ...
    server : ServerState,
    client : seq<bool>
/*}*/
) {
  predicate WellFormed(c: Constants) {
/*{*/
    && c.WellFormed()
    && |client| == c.numClient
    && (server.Client? ==> server.index < c.numClient)
/*}*/
  }
}

predicate Init(c:Constants, v:Variables) {
  && v.WellFormed(c)
/*{*/
  && v.server.Server?
  && forall i:nat | i < |v.client| :: !v.client[i]
/*}*/
}

/*{*/
predicate Acquire(c: Constants, v: Variables, v': Variables, index: nat) {
  && v.WellFormed(c)
  && v'.WellFormed(c)
  && index < c.numClient
  && v.server.Server?
  && v'.server.Client?
  && v'.server.index == index
  && v'.client == v.client[index := true]
}

predicate Release(c: Constants, v: Variables, v': Variables, index: nat) {
  && v.WellFormed(c)
  && v'.WellFormed(c)
  && index < c.numClient
  && v.server.Client?
  && v.server.index == index
  // && v.client[index]
  && v'.server.Server?
  && v'.client == v.client[index := false]
}
/*}*/
// Jay-Normal-Form: pack all the nondeterminism into a single object
// that gets there-exist-ed once.
datatype Step =
/*{*/
  | AcquireStep(client: nat)
  | ReleaseStep(client: nat)
/*}*/

ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
/*{*/
  case AcquireStep(client: nat) => Acquire(c, v, v', client)
  case ReleaseStep(client: nat) => Release(c, v, v', client)
/*}*/
}

ghost predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
}

// A good definition of safety for the lock server is that no two clients
// may hold the lock simultaneously. This predicate should capture that
// idea in terms of the Variables you have defined.
predicate Safety(c:Constants, v:Variables) {
/*{*/
  && v.WellFormed(c)
  && forall i:nat, j:nat | 0 <= i < j < c.numClient :: !v.client[i] || !v.client[j]
/*}*/
}


// This predicate should be true if and only if the client with index `clientIndex`
// has the lock acquired.
// Since you defined the Variables state, you must define this predicate in
// those terms.
predicate ClientHoldsLock(c: Constants, v: Variables, clientIndex: nat)
  requires v.WellFormed(c)
{
/*{*/
  && clientIndex < c.numClient
  && v.client[clientIndex]
/*}*/
}

// Show a behavior that the system can release a lock from clientA and deliver
// it to clientB.
lemma PseudoLiveness(clientA:nat, clientB:nat) returns (c: Constants, behavior:seq<Variables>)
    requires clientA == 2
    requires clientB == 0
    ensures 0 < |behavior|  // precondition for index operators below
    ensures forall i | 0 <= i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1]) // Behavior satisfies your state machine
    ensures forall i | 0 <= i < |behavior| :: Safety(c, behavior[i]) // Behavior always satisfies the Safety predicate
    ensures behavior[0].WellFormed(c) // precondition for calling ClientHoldsLock
    ensures ClientHoldsLock(c, behavior[0], clientA)
    ensures behavior[|behavior|-1].WellFormed(c) // precondition for calling ClientHoldsLock
    ensures ClientHoldsLock(c, behavior[|behavior|-1], clientB)
{
/*{*/
  c := Constants(3);
  var variable0 := Variables(ServerState.Client(clientA), [false, false, true]);
  var variable1 := Variables(ServerState.Server, [false, false, false]);
  var variable2 := Variables(ServerState.Client(clientB), [true, false, false]);
  assert NextStep(c, variable0, variable1, ReleaseStep(2));
  assert NextStep(c, variable1, variable2, AcquireStep(0));
  behavior := [variable0, variable1, variable2];
/*}*/
}

