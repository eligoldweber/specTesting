module leader 
{

datatype agent = Ldr | Acc

datatype Id = Id(agt:agent, idx:nat)

datatype Value = V(val:int) | Nil
datatype Ballot = Ballot(seqNo:nat, idx:nat) | Bottom
datatype ValBal = VB(v:Value, b:Ballot)

datatype Message = Prepare(bal:Ballot)
                | Promise(bal:Ballot, vb:ValBal)  //valbal is the value-ballot pair with which the value was accepted
                | Propose(bal:Ballot, val:Value)
                | Accept(bal:Ballot, val:Value)
                | Preempt(bal:Ballot)

datatype Packet = Packet(src:Id, dst:Id, msg:Message)

datatype EnvStep = 
    IoStep(actor:Id, recvIos:seq<Packet>, sendIos:seq<Packet>)

datatype Environment = Env(
        sentPackets:set<Packet>,
        nextStep:EnvStep
    )

predicate EnvironmentInit(e:Environment) {
    e.sentPackets == {}
}

predicate ValidIoStep(iostep:EnvStep) 
    requires iostep.IoStep?
{
    && (forall r | r in iostep.recvIos :: r.dst == iostep.actor)
    && (forall s | s in iostep.sendIos :: s.src == iostep.actor)
}


predicate EnvironmentNext(e:Environment, e':Environment)
{
    match e.nextStep {
        case IoStep(actor, recvIos, sendIos) => 
            && ValidIoStep(e.nextStep)
            && e'.sentPackets == e.sentPackets + (set s | s in sendIos)
            && e'.nextStep == e.nextStep
            && (forall r | r in recvIos :: r in e.sentPackets)
    }
}

lemma testN(a:Environment) returns (a':Environment,b:Environment)
    ensures !(EnvironmentNext(a,a') 
              && a' != b
              && EnvironmentNext(a,b))
{

}

// Each node's identifier (address)
datatype Constants = Constants(ids: seq<nat>) {
    predicate ValidIdx(i: nat) {
        0<=i<|ids|
    }
    predicate UniqueIds() {
        (forall i:nat, j:nat | ValidIdx(i) && ValidIdx(j) && ids[i]==ids[j] :: i == j)
    } 
    predicate WF() {
        0 < |ids|
    }
}


// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<nat>) {
    predicate WF(c: Constants)
        requires c.WF()
    {
        && |highest_heard| == |c.ids|
    }
}

function NextIdx(c:Constants, idx:nat) : (n:nat)
  requires c.WF()
  requires c.ValidIdx(idx)
  ensures n == 0 || n == idx + 1
  ensures idx == |c.ids| - 1 <==> n == 0 
  ensures idx < |c.ids| - 1 <==> n == idx + 1
{
    (idx + 1) % |c.ids|
}

function max(a:nat, b:nat) : nat {
    if a > b then a else b
}

predicate Transmission(c: Constants, v: Variables, v': Variables, src: nat)
{
    && c.WF()
    && v.WF(c)
    && v'.WF(c)
    && c.ValidIdx(src)
    // Neighbor address in ring.
    && var dst := NextIdx(c, src);
    // src sends the max of its highest_heard value and its own id.
    && var message := max(v.highest_heard[src], c.ids[src]);
    // dst only overwrites its highest_heard if the message is higher.
    && var dst_new_max := max(v.highest_heard[dst], message);
    // && v' == v.(highest_heard := v.highest_heard[dst := message])  // BUG: dst := dst_new_max
    && v' == v.(highest_heard := v.highest_heard[dst := dst_new_max])
}

lemma test(c: Constants, v: Variables, src: nat) returns (v': Variables,w:Variables)
    // ensures !(LReplicaNextProcess2a(s, s', received_packet, sent_packets))
// ensures !(Transmission(c,v,v',src))
    // ensures !(Transmission(c,v,v',src) 
    //           && v' != w
    //           && Transmission(c,v,w,src))
{

}

}