module Ex3

open Ex2

pred valid {
    validTopology[]
    validMessages[]
}

pred validTopology {
    // all members are reachable from each other)
    (all m: Member | m.^nxt=Member)
    validMemberQueue1[]
    validMemberQueue2[]
}

pred validMessages {
    // pending messages weren't received by any node
    no PendingMsg.rcvrs
    and
    validSendingMsg[]
    and 
    validSentMsg[]
    and
    validMsgDisjunction[]
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
    // the leader queue is the leader's queue
    LQueue = (Leader.lnxt).Member 
    // only members are in the leader queueLQueue
    no ((Node - Member) & LQueue) 
    // the leader queue ends in the leader (if it exists)
    some  LQueue implies (one (Leader.lnxt).Leader and no Leader.(Leader.lnxt)) 
    // each member is only pointed to by at most one non-member
    all m : LQueue | lone (Leader.lnxt).m 
    // all members can reach the leader
    all m : Member | (some m.(Leader.lnxt)) implies (Leader in m.(^(Leader.lnxt))) 
}

pred validSendingMsg {
    all m : SendingMsg | 
    (
        // m was received by some members
        some m.rcvrs
        and
        // m is in someone's outbox
        m in Node.outbox
    )
}

pred validSentMsg {
    all m : SentMsg | 
        // not in any member's outbox
        m not in Member.outbox
}

pred validMsgDisjunction {
    no (SendingMsg & SentMsg)
    no (SendingMsg & PendingMsg)
    no (SentMsg & PendingMsg)
}

fun visualizeMemberQueue[] : Node -> lone Node {
    Member.qnxt
}

fun visualizeLeaderQueue[] : Node -> lone Node {
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
                ! inAnyQueue[n]
            )))
            implies 
            (always (eventually (
                some m : Member |
                memberApplication[n, m]
            )))
        )
}

pred fairnessBecomeMember {
    all n, m : Node|
        (
            (eventually (always (
                // n is a member
                m in Member
                and
                // m's queue is not empty
                some m.qnxt
                and
                // n is the first node in m's queue
                n = firstNodeInQueue[m]
            )))
            implies
            (always (eventually (
                memberPrommotion[m]
            )))
        )
}

pred fairnessLeaderQueue {
    all n : Node |
        (
            (eventually (always (
                // n is a member
                n in Member
                and
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
                /// leader queue is not empty
                some Leader.lnxt
                and
                // m is the first member in the leader queue
                n = (Leader.lnxt).Leader
                and
                // no broadcast in progress
                no SendingMsg
                and
                // the Leader already broadcasted all of their messages
                no (sndr.Leader & (SendingMsg + PendingMsg))
            )))
            implies
            (always (eventually (
                leaderPrommotion[]
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
            (eventually (always (
                // message is in the middle of broadcast
                msg in SendingMsg
                and
                // message is in m's outbox
                msg in m.outbox
                and
                // can't allow redirect from Leader (sender)
                m != Leader
            )))
            implies
            (always (eventually (messageRedirect[msg])))
        )
}

pred fairnessTerminateBroadcast {
    all msg : Msg |
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

pred noExits {
    noMemberExit[]
    and
    noMemberQueueExit[]
}

pred noMemberExit {
    (all n : Node | (! eventually memberExit[n]))
}

pred noMemberQueueExit {
    (all n : Node | (! eventually nonMemberExit[n]))
}

pred allBroadcastsTerminated {
    no SendingMsg
    no PendingMsg
    SentMsg = Msg
}

assert liveness {
    (#Node>=2  and fairness[] and noExits[]) implies (eventually allBroadcastsTerminated[])
}

assert wrongLiveness {
    (#Node>=2  and fairness[]) implies (eventually allBroadcastsTerminated[])
}

assert validCheck {
    always valid
}

check validCheck for 3

check liveness for 3 but 1 Msg

check wrongLiveness for 3 but 15 steps