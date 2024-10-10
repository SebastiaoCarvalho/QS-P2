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


fun visualizeQueue[m: Member] : Node -> lone Node {
    m.qnxt
}

// members form a ring with each member pointing to another member (or itself)
fact {
    all m: Member | m.^nxt=Member
}

// each member queue consists of a (possibly empty) list of non-member nodes ending in the member in charge of that queue
fact {
    all m: Member | no m.(m.qnxt) && some (m.qnxt).m && no (Member.(m.qnxt))
}


run {#Member=5 #Msg=0 #Node=7} for 7