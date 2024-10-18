module Ex3

open Ex2

pred valid {
    // all members are reachable from each other)
    always (
        (all m: Member | m.^nxt=Member)
        and
        validMemberQueue1[]
        and
        validMemberQueue2[]
        and
        // pending messages weren't received by any node
        no PendingMsg.rcvrs
        and
    )
}

pred validMemberQueue1 {
    all m: Member | 
        (
            // Non-members
            no (Member.(m.qnxt)) 
            // if list is not empty, it ends in the member
            && (some (m.qnxt) implies one (m.qnxt).m) 
            // all non-members can reach the member
            && (all n : Node - Member | (some n.(m.qnxt)) implies (m in n.(^(m.qnxt)))) 
            // no cycles
            && (no (^(m.qnxt) & iden)) 
        )
}

pred validMemberQueue2 {
    // each non-member node is in at most one queue
    all n: (Node - Member) | lone (n.(Member.qnxt)) 
    // each non-member is pointed to by at most one member
    all n: (Node - Member) | lone ((Member.qnxt).n) 
    // each member is only pointed to by at most one non-member
    all m: Member | lone (Member.qnxt).m 
}

pred validLeaderQueue {
    // only members are in the leader queueLQueue
    no (Node - Member).(Leader.lnxt) 
    // the leader queue ends in the leader
    some (Leader.lnxt) implies (one (Leader.lnxt).Leader and no Leader.(Leader.lnxt)) 
    // all members can reach the leader
    all m : Member | (some m.(Leader.lnxt)) implies (Leader in m.(^(Leader.lnxt))) 
    // the leader queue is the leader's queue
    LQueue = (Leader.lnxt).Member 
}

pred validSendingMsg {
    all m : SendingMsg | 
    (
        some m.rcvrs // received by some
        and m.rcvrs != Member // not received by all
    )
}

assert validCheck {
    valid
}

check validCheck for 3