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
    all m: Member | m.^nxt=Member
}

// each member queue consists of a (possibly empty) list of non-member nodes ending in the member in charge of that queue
fact {
    all m: Member | no (Member.(m.qnxt)) && (some (m.qnxt) implies one (m.qnxt).m) && (no ^(m.qnxt & iden))
}

// non-member nodes are not allowed to queue in more than one member queue at a time
fact {
    all n: (Node - Member) | lone (n.(Member.qnxt))
}


run {#Member=5 #Msg=0 #Node=11 #Member.qnxt=5} for 11