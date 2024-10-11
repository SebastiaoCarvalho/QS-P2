sig Node {}

sig Member in Node {
    nxt: lone Member,
    qnxt : Node -> lone Node,
    outbox: set Msg
}

one sig Leader in Member {
    lnxt: Node -> lone Node
}

sig LQueue in Member {}

abstract sig Msg {
    sndr: Node,
    rcvrs: set Node
}

sig SentMsg, SendingMsg, PendingMsg extends Msg {}


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
    no (Node - Member).(Leader.lnxt) // only members are in the leader queueLQueue
    some (Leader.lnxt) implies (one (Leader.lnxt).Leader and no Leader.(Leader.lnxt)) // the leader queue ends in the leader
    all m : Member | (some m.(Leader.lnxt)) implies (Leader in m.(^(Leader.lnxt))) // all members can reach the leader
}

run {#Member=4 #Msg=0 #Node=7 #Member.qnxt=2 #LQueue=0 #Leader.lnxt=2} for 8