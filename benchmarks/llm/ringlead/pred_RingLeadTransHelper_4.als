/*
 * Model of leader election on a ring
 * Fault: needsToSend always 0, so no messages are sent.
 */
open util/boolean as bool
open examples/algorithms/messaging as msg
open util/ordering[msg/Node] as nodeOrd
open util/ordering[msg/Tick] as tickOrd

sig RingLeadNode extends msg/Node {
   rightNeighbor: msg/Node
}

fact DefineRing {
  (one msg/Node || (no n: msg/Node | n = n.rightNeighbor))
  all n: msg/Node | msg/Node in n.^rightNeighbor
}

sig RingLeadMsgState extends msg/MsgState {
  id: msg/Node
}

sig MsgViz extends msg/Msg {
  vFrom: msg/Node,
  vTo: set msg/Node,
  vId: msg/Node
}

fact {
  MsgViz = msg/Msg
  vFrom = state.from
  vTo = state.to
  vId = state.id
}

sig RingLeadNodeState extends msg/NodeState {
  leader: Bool
}

pred RingLeadFirstTrans [self: msg/Node, pre, post: msg/NodeState,
                        sees, reads, sends, needsToSend: set msg/Msg] {
   one sends
   # needsToSend = 1
   sends.state.to = self.rightNeighbor
   sends.state.id = self
   post.leader = False
}

fact InitRingLeadState {
  all n: msg/Node |
    tickOrd/first.state[n].leader = False
}

pred RingLeadRestTrans [self: msg/Node, pre, post: msg/NodeState,
                       sees, reads, sends, needsToSend: set msg/Msg] {
   RingLeadTransHelper[self, sees, reads, sends, needsToSend]
   post.leader = True iff (pre.leader = True ||
                           self in reads.state.id)
}

pred RingLeadTransHelper[self: msg/Node, sees, reads, sends, needsToSend: set msg/Msg] {
   reads = sees

   all received: reads |
     (received.state.id in nodeOrd/nexts[self]) =>
       (one weSend: sends | (weSend.state.id = received.state.id && weSend.state.to = self.rightNeighbor))

   all weSend: sends | {
     let mID = weSend.state.id | {
       mID in nodeOrd/nexts[self]
       mID in reads.state.id
       weSend.state.to = self.rightNeighbor
     }
   }

   # needsToSend = 0
}

fact RingLeadTransitions {
   all n: msg/Node {
      all t: msg/Tick - tickOrd/last | {
         t = tickOrd/first =>
           RingLeadFirstTrans[n, t.state[n], tickOrd/next[t].state[n], t.visible[n], t.read[n], t.sent[n], t.needsToSend[n]]
         else
           RingLeadRestTrans[n, t.state[n], tickOrd/next[t].state[n], t.visible[n], t.read[n], t.sent[n], t.needsToSend[n]]
      }
      RingLeadTransHelper[n, tickOrd/last.visible[n], tickOrd/last.read[n], tickOrd/last.sent[n], tickOrd/last.needsToSend[n]]
   }
}

fact CleanupViz {
  RingLeadNode = msg/Node
  RingLeadMsgState = msg/MsgState
  RingLeadNodeState = msg/NodeState
}

pred SomeLeaderAtTick[t: msg/Tick] {
  some n: msg/Node | t.state[n].leader = True
}

pred NeverFindLeader {
  msg/Loop
  all t: msg/Tick | ! SomeLeaderAtTick[t]
}

assert Liveness {
  (msg/NoLostMessages && msg/NoMessageShortage) => ! NeverFindLeader
}

pred SomeLeader { some t: msg/Tick | SomeLeaderAtTick[t] }