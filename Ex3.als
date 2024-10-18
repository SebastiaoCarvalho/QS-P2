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
        validSendingMsg[]
        and validSentMsg[]
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
        // m is in the outbox of a member that is not the sender
        Leader not in m.rcvrs
    )
}

pred validSentMsg {
    all m : SentMsg | 
        // not in any member's outbox
        m not in Member.outbox
}

assert validCheck {
    valid
}

fun visualizeQueue[] : Node -> lone Node {
    Member.qnxt
}

fun visualizeLeader[] : Node -> lone Node {
    Leader.lnxt
}

pred fairness {
    fairnessMemberQueue[]
    and
    fairnessBecomeMember[]
    and 
    fairnessLeaderQueue[]
    and
    fairnessBecomeLeader[]
    and
    fairnessBroadcastInitialisation[]
    and
    fairnessMessageRedirect[]
    and
    fairnessTerminateBroadcast[]
    
}

pred fairnessMemberQueue {
    all n : Node |
        (
            (eventually (always (
                // n is not a member
                n not in Member
                and
                // n is not in any other member's queue
                n !in (Member.qnxt).Node
            )))
            implies 
            (always (eventually (
                some m : Member |
                memberApplication[n, m]
            )))
        )
}

pred fairnessBecomeMember {
    all n : Node |
        (
            (eventually (always (
                some m : Member |
                    // m's queue is not empty
                    some m.qnxt
                    and
                    // n is the first node in m's queue
                    n = firstNodeInQueue[m]
            )))
            implies
            (always (eventually (
                some m : Member |
                memberApplication[n, m]
            )))
        )
}

pred fairnessLeaderQueue {
    all n : Node |
        (
            (eventually (always (
                // m is not the Leader
                n != Leader
                and
                // m is not already in the leader queue
                n not in (Leader.lnxt).Member
            )))
            implies
            (always (eventually (
                leaderApplication[n]
            )))
        )
}

pred fairnessBecomeLeader {
    all n : Node |
        (
            (eventually (always (
                // leader queue is not empty
                some Leader.lnxt
                and
                // m is the first member in the leader queue
                n = (Leader.lnxt).Leader
                and
                // no broadcast in progress
                no SendingMsg
                and
                // the Leader already broadcasted all of their messages
                no Leader.outbox
            )))
            implies
            (always (eventually (
                leaderPromotion[n]
            )))
        )
}

pred fairnessBroadcastInitialisation {
    all msg : Msg |
        (
            (eventually (always (
                
            // message is pending
            msg in PendingMsg
            and
            // only leader can start broadcast
            msg.sndr = Leader 
            and
            // only start broadcast if more than one member
            some Member - Leader
            )))
            implies
            (always (eventually (
                broadcastInitialisation[msg]
            )))
        )
}

pred fairnessMessageRedirect {
    all msg : Msg, m : Node |
        (
            ant[msg, m]
            implies
            post[msg, m]
        )
}

pred ant[msg : Msg, m : Node] {
    eventually always (
        // message is in the middle of broadcast
        msg in SendingMsg
        and
        // message is in m's outbox
        msg in m.outbox
        and
        // can't allow redirect from Leader (sender)
        m != Leader
    )
}

pred post[msg : Msg, m : Node] {
    always eventually messageRedirect[msg, m]
}

pred fairnessTerminateBroadcast {
    all msg : Msg {
        (
            (eventually (always (
                // message is in the middle of broadcast
                msg in SendingMsg
                and
                // message is back in Leader's outbox
                msg in Leader.outbox
            )))
            implies
            (always (eventually (
                broadcastTermination[msg]
            )))
        )
    }
}

check validCheck for 3

run {#Node=2 fairness} for 3 but 1 Msg