module l
{
    type OperationNumber = int
    newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100

    datatype EndPoint = EndPoint(public_key:seq<byte>)
    type Bytes = seq<byte>

    type AppRequest = Bytes

// type Key(==, !new) = uint64
// type Value = seq<byte>

// datatype OptionalValue = ValuePresent(v:Value) | ValueAbsent()
// 
    // datatype AppRequest = AppGetRequest(g_seqno:int, g_k:Key) | AppSetRequest(s_seqno:int, s_k:Key, ov:OptionalValue)


    type NodeIdentity = EndPoint

    datatype Ballot = Ballot(seqno:int, proposer_id:int)
    datatype Request = Request(client:NodeIdentity, seqno:int, request:AppRequest)

    type RequestBatch = seq<Request>

    datatype LearnerTuple = LearnerTuple(received_2b_message_senders:set<NodeIdentity>, candidate_learned_value:RequestBatch)

    type LearnerState = map<OperationNumber, LearnerTuple>
    datatype UpperBound = UpperBoundFinite(n:int) | UpperBoundInfinite()

    datatype LParameters = LParameters(
     max_log_length:int,
    baseline_view_timeout_period:int,
    heartbeat_period:int,
    max_integer_val:UpperBound,
    max_batch_size:int,
    max_batch_delay:int
    )

    datatype LConfiguration = LConfiguration(
    clientIds:set<NodeIdentity>,
    replica_ids:seq<NodeIdentity>
    )
    datatype LConstants = LConstants(
    config:LConfiguration,
    params:LParameters
    )

    datatype LReplicaConstants = LReplicaConstants(
    my_index:int,
    all:LConstants
    )

datatype RslMessage =
    RslMessage_Invalid()
  | RslMessage_Request(seqno_req:int, val:AppRequest)
  | RslMessage_1a(bal_1a:Ballot)
  | RslMessage_2a(bal_2a:Ballot, opn_2a:OperationNumber, val_2a:RequestBatch)
  | RslMessage_2b(bal_2b:Ballot, opn_2b:OperationNumber, val_2b:RequestBatch)
  | RslMessage_Heartbeat(bal_heartbeat:Ballot, suspicious:bool, opn_ckpt:OperationNumber)
  | RslMessage_AppStateRequest(bal_state_req:Ballot, opn_state_req:OperationNumber)
  | RslMessage_StartingPhase2(bal_2:Ballot, logTruncationPoint_2:OperationNumber)

datatype LPacket<IdType, MessageType(==)> = LPacket(dst:IdType, src:IdType, msg:MessageType)

type RslPacket = LPacket<NodeIdentity, RslMessage>

datatype LLearner = LLearner(
  constants:LReplicaConstants,
  max_ballot_seen:Ballot,
  unexecuted_learner_state:LearnerState
  )

  predicate BalLt(ba:Ballot, bb:Ballot)
{
  || ba.seqno < bb.seqno
  || (ba.seqno==bb.seqno && ba.proposer_id < bb.proposer_id)
}


predicate LLearnerProcess2b(s:LLearner, s':LLearner, packet:RslPacket)
  requires packet.msg.RslMessage_2b?
{
  var m := packet.msg;
  var opn := m.opn_2b;
  if packet.src !in s.constants.all.config.replica_ids || BalLt(m.bal_2b, s.max_ballot_seen) then
    s' == s
  else if BalLt(s.max_ballot_seen, m.bal_2b) then
    var tup' := LearnerTuple({packet.src}, m.val_2b);
    s' == s.(max_ballot_seen := m.bal_2b,
             unexecuted_learner_state := map[opn := tup'])
  else if opn !in s.unexecuted_learner_state then
    var tup' := LearnerTuple({packet.src}, m.val_2b);
    s' == s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup'])
  else if packet.src in s.unexecuted_learner_state[opn].received_2b_message_senders then
    s' == s
  else
    var tup := s.unexecuted_learner_state[opn];
    var tup' := tup.(received_2b_message_senders := tup.received_2b_message_senders + {packet.src});
    s' == s.(unexecuted_learner_state := s.unexecuted_learner_state[opn := tup'])
}

lemma test(s:LLearner,packet:RslPacket) returns (s':LLearner,v:LLearner)
    requires packet.msg.RslMessage_2b?

    // ensures !(LReplicaNextProcess2a(s, s', received_packet, sent_packets))

    ensures !(LLearnerProcess2b(s, s',packet) 
              && s' != v
              && LLearnerProcess2b(s, v,packet))
{
}


}