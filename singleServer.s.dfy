//#title Single-Server Lock Service Model
//#desc A complex state machine
//#desc including a Safety predicate on the state type.

/*
Model a lock service that consists of a single server and an
arbitrary number of clients.
The state of the system includes the server's state (whether the server
knows that some client holds the lock, and if so which one)
and the clients' states (for each client, whether that client knows
it holds the lock).
The system should begin with the server holding the lock.
An acquire step atomically transfers the lock from the server to some client.
(Note that we're not modeling the network yet -- the lock disappears from
the server and appears at a client in a single atomic transition.)
A release step atomically transfers the lock from the client back to the server.
The safety property is that no two clients ever hold the lock
simultaneously.
*/

datatype ServerGrant = Unlocked | Client(id: nat)
datatype ClientRecord = Released | Acquired

datatype Constants = Constants(clientCount: nat) {
  predicate WF() { true }
  predicate ValidIdx(idx: int) {
    0 <= idx < clientCount
  }
}
datatype Variables = Variables(server: ServerGrant, clients: seq<ClientRecord>) {
  predicate WF(c: Constants) {
    |clients| == c.clientCount
  }
}

predicate Init(c:Constants, v:Variables) {
  && v.WF(c)
  && v.server.Unlocked?
  && |v.clients| == c.clientCount
  && forall i | 0 <= i < |v.clients| :: v.clients[i].Released?
}

predicate Acquire(c:Constants, v:Variables, v':Variables, id:int) {
  && v.WF(c)
  && v'.WF(c)
  && c.ValidIdx(id)

  && v.server.Unlocked?

  && v'.server == Client(id)
  && v'.clients == v.clients[id := Acquired]
}

predicate Release(c:Constants, v:Variables, v':Variables, id:int) {
  && v.WF(c)
  && v'.WF(c)
  && c.ValidIdx(id)

  && v.clients[id].Acquired?

  && v'.server.Unlocked?
  && v'.clients == v.clients[id := Released]
}

datatype Step =
  | AcquireStep(id: int)
  | ReleaseStep(id: int)

predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
    case AcquireStep(id) => Acquire(c, v, v', id)
    case ReleaseStep(id) => Release(c, v, v', id)
}

predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
}

predicate Safety(c:Constants, v:Variables) {
  // What's a good definition of safety for the lock server? No two clients
  // have the lock simultaneously. Write that here.
  forall i,j ::
    (&& 0 <= i < |v.clients|
    && 0 <= j < |v.clients|
    && v.clients[i].Acquired?
    && v.clients[j].Acquired?) ==> i == j
}


lemma TestNextAcquireStep(c:Constants, v:Variables, v':Variables, id: int, v'':Variables)
     requires Acquire(c, v, v', id) && Acquire(c, v, v'', id)
     ensures v' == v''
    {
        assert v'' == v';
    }

lemma TestNextReleaseStep(c:Constants, v:Variables, v':Variables, id: int, v'':Variables)
     requires Release(c, v, v', id) && Release(c, v, v'', id)
     ensures v' == v''
    {
        assert v'' == v';
    }

// reachability Test

predicate ValidReachableBehavior(c:Constants, b:seq<Variables>,len:int)
    requires len > 0
{
    && |b| == len
    && Init(c,b[0])
    && (forall i :: 0 <= i < |b|-1 ==> Next(c,b[i],b[i+1]))
    && (forall i :: 0 <= i < |b| ==> Safety(c,b[i]))
    && (forall i :: 0 <= i < |b| ==> b[i].WF(c))
}

lemma WitnessReachableBehavior(c:Constants,b:seq<Variables>) returns (b':seq<Variables>)
    requires |b| > 1
    requires (forall i :: 0 <= i < |b|-1 ==> Next(c,b[i],b[i+1]))
    requires (forall i :: 0 <= i < |b| ==> Safety(c,b[i]))
    ensures |b'| > 0
    ensures b' == b[1..]
    ensures Next(c,b[0],b'[0])
{
    var remainder := b[1..];
    assert |remainder| > 0;
    return remainder;
}

lemma AcquireReachableInNSteps(c:Constants, b:seq<Variables>,id:int)
    requires ValidReachableBehavior(c,b,1); 
    requires c.ValidIdx(id)
    // requires id == 0
    ensures exists v' :: (Next(c,b[|b|-1],v') && Acquire(c,b[|b|-1],v',id));
{
    assert Init(c,b[0]);
    var s := b[0].(server := Client(id), clients := b[0].clients[id := Acquired]);
    assert Acquire(c,b[0],s,id);
    assert NextStep(c, b[0], s, AcquireStep(id));
    assert Next(c,b[0],s);
    assert b[0] == b[|b|-1];
}


lemma AcquireReachableInNSteps_odd(c:Constants, b:seq<Variables>,id:int)
    requires ValidReachableBehavior(c,b,5); 
    requires c.ValidIdx(id)
    ensures exists v' :: (Next(c,b[|b|-1],v') && Acquire(c,b[|b|-1],v',id));
{
    var a := WitnessReachableBehavior(c,b);
    a := WitnessReachableBehavior(c,a);
    a := WitnessReachableBehavior(c,a);

    assert Init(c,b[0]);
    var s := b[4].(server := Client(id), clients := b[4].clients[id := Acquired]);
    assert Acquire(c,b[4],s,id);
    assert NextStep(c, b[4], s, AcquireStep(id));
    assert s.clients[id].Acquired?;
}

lemma AcquireReachableInNSteps_13(c:Constants, b:seq<Variables>,id:int)
    requires ValidReachableBehavior(c,b,13); 
    requires c.ValidIdx(id)
    ensures exists v' :: (Next(c,b[|b|-1],v') && Acquire(c,b[|b|-1],v',id));
{
    var a := WitnessReachableBehavior(c,b);
    a := WitnessReachableBehavior(c,a);
    a := WitnessReachableBehavior(c,a);
    a := WitnessReachableBehavior(c,a);
    a := WitnessReachableBehavior(c,a);
    a := WitnessReachableBehavior(c,a);
    a := WitnessReachableBehavior(c,a);
    a := WitnessReachableBehavior(c,a);
    a := WitnessReachableBehavior(c,a);
    a := WitnessReachableBehavior(c,a);
    a := WitnessReachableBehavior(c,a);        
    
    assert Init(c,b[0]);
    var s := b[12].(server := Client(id), clients := b[12].clients[id := Acquired]);
    assert Acquire(c,b[12],s,id);
    assert NextStep(c, b[12], s, AcquireStep(id));
    assert s.clients[id].Acquired?;
}

lemma AcquireReachableInNSteps_3(c:Constants, b:seq<Variables>,id:int)
    requires ValidReachableBehavior(c,b,3); 
    requires c.ValidIdx(id)
    ensures exists v' :: (Next(c,b[|b|-1],v') && Acquire(c,b[|b|-1],v',id));
{
    var a := WitnessReachableBehavior(c,b);
    a := WitnessReachableBehavior(c,a);

    assert Init(c,b[0]);
    var s := b[2].(server := Client(id), clients := b[2].clients[id := Acquired]);
    assert Acquire(c,b[2],s,id);
    assert NextStep(c, b[2], s, AcquireStep(id));
    assert s.clients[id].Acquired?;
}

lemma ReleaseReachableInNSteps_4(c:Constants, b:seq<Variables>,id:int)
    requires ValidReachableBehavior(c,b,4); 
    requires c.ValidIdx(id)
    requires b[3].clients[id].Acquired?
    ensures exists v' :: (Next(c,b[|b|-1],v') && Release(c,b[|b|-1],v',id));
{
    var a := WitnessReachableBehavior(c,b);
     a := WitnessReachableBehavior(c,a);
      
    assert Init(c,b[0]);
    
    var s := b[3].(server := Unlocked, clients := b[3].clients[id := Released]);
    assert Release(c,b[3],s,id);
    assert NextStep(c, b[3], s, ReleaseStep(id));
}