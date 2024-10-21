module Ex1

sig Node {
  outbox: set Msg
}

sig Member in Node { 
 nxt: one Node, 
 qnxt : Node -> lone Node 
}

one sig Leader in Member {
   lnxt: Member -> lone Member
}

sig LQueue in Member {}

sig Msg {
  sndr: Node, 
  rcvrs: set Node 
}

sig SentMsg, SendingMsg, PendingMsg in Msg {}


fun visualizeQueue[] : Node -> lone Node {
    Member.qnxt
}

fun visualizeLeader[] : Node -> lone Node {
    Leader.lnxt
}

// members form a ring with each member pointing to another member (or itself)
fact {
    all m: Member | m.^nxt=Member // all members are reachable from each other
}

// each member queue consists of a (possibly empty) list of non-member nodes ending in the member in charge of that queue
fact {
    all m: Member | 
    (
        no (Member.(m.qnxt)) // Non-members
        && (some (m.qnxt) implies one (m.qnxt).m) // if list is not empty, it ends in the member
        && (all n : Node - Member | (some n.(m.qnxt)) implies (m in n.(^(m.qnxt)))) // all non-members can reach the member
        && (no (^(m.qnxt) & iden)) // no cycles
    )
}

// non-member nodes are not allowed to queue in more than one member queue at a time
fact {
    all n: (Node - Member) | lone (n.(Member.qnxt)) // each non-member node is in at most one queue
    all n: (Node - Member) | lone ((Member.qnxt).n) // each non-member is pointed to by at most one member
    all m: Member | lone (Member.qnxt).m // each member is only pointed to by at most one non-member
}


// the leader queue consists of a list of member nodes ending in the leader
fact {
    LQueue = (Leader.lnxt).Member // the leader queue is the leader's queue
    no ((Node - Member) & LQueue) // only members are in the leader queueLQueue
    some  LQueue implies (one (Leader.lnxt).Leader and no Leader.(Leader.lnxt)) // the leader queue ends in the leader
    all m : LQueue | lone (Leader.lnxt).m // each member is only pointed to by at most one non-member
    all m : Member | (some m.(Leader.lnxt)) implies (Leader in m.(^(Leader.lnxt))) // all members can reach the leader
}

// Pending message if broadcast hasn't started
fact {
    all msg : PendingMsg | 
    (
        // message is in the sender's outbox
        msg in msg.sndr.outbox
        and
        // message was not received by anyone
        no msg.rcvrs
    )
}

// Sending messages if broadcast started but not finished
fact {
    all m : SendingMsg | 
    (
        // m is in the outbox of a member that is not the sender
        m.sndr not in m.rcvrs
        and
        // m is in someone's outbox
        m in Node.outbox
    )
}

// Sent messages if broadcast finished
fact {
    all m : SentMsg | 
        // Sent messages are not in anyone's outbox
        m not in Member.outbox
}

// A message can only be sent, sending or pending
fact {
    no (SendingMsg & SentMsg)
    no (SendingMsg & PendingMsg)
    no (SentMsg & PendingMsg)
}

// A message needs to be either pending, sending or sent
fact {
    all msg : Msg | msg in (PendingMsg + SendingMsg + SentMsg)
}

pred trace1 {
    #Node>=5 
    (some Leader.lnxt)
    // at least 2 members have a non-empty queue
    #(Member.qnxt.Member)>=2 
    some SendingMsg
    some SentMsg 
    some PendingMsg
}

// Run this trace to generate answers for Ex1.2.1 and Ex1.2.2
run {trace1} for 7