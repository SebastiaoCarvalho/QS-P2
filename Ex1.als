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


fun visualizeMemberQueue[] : Node -> lone Node {
    Member.qnxt
}

fun visualizeLeaderQueue[] : Node -> lone Node {
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
        // m was received by some members
        some m.rcvrs
        and
        // m is in someone's outbox
        m in Node.outbox
    )
}

// Sent messages if broadcast finished
fact {
    all m : SentMsg | 
    (   
        // m was received by some members
        some m.rcvrs
        and
        // Sent messages are not in anyone's outbox
        m not in Member.outbox
    )
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

// A message can only be in one outbox at the same time
fact {
    all m : Msg | lone n : Node | m in n.outbox
}

// the outbox of a node can only contain pending messages belonging
// to that node and sending messages belonging to the current leader
fact {
    all n : Node |
    (
        all m : n.outbox |
        (
            // message is pending and belongs to the node
            (m in PendingMsg and m.sndr = n) 
            or
            // message is sending and belongs to the leader
            (m in SendingMsg and m.sndr in Leader)
        )
    )
}

// if a node has a message in its outbox that belongs to the leader 
// then: that node is a member and it has received that message
fact {
    all n : Node |
    (
        all m : n.outbox |
        (
            (m in SendingMsg and m.sndr in Leader) implies
            (
                // the node received the message
                n in m.rcvrs
                and
                // the node is a member
                n in Member
            )
        )
    )
}

// nodes cannot receive their own message
fact {
    no (rcvrs & sndr)
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
run {trace1} for 8