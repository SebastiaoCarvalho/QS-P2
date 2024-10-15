module Ex2

open Ex1

fun visualizeQueue[] : Node -> lone Node {
    Member.qnxt
}

fun visualizeLeader[] : Node -> lone Node {
    Leader.lnxt
}

pred init[] {
    Member = Leader
    Msg = PendingMsg
    all m : Member | m.outbox = sndr.m
    no LQueue
    no qnxt
    no lnxt
    no rcvrs
}

pred stutter[] {
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
}

pred memberApplication[n : Node, m: Member] {
    // Pre-Conditions

    // n is not a member
    n not in Member
    // n is not in any other member's queue
    n !in (Member.qnxt).Node

    // Post-Conditions

    // add n to m's queue
    addToEmptyQueue[n, m]
    or
    addToNonEmptyQueue[n, m]
    
    // Frame Conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    nxt' = nxt
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
    // all other members queues are unchanged
    (all m1 : (Member - m) | m1.qnxt' = m1.qnxt)
}

pred addToEmptyQueue[n : Node, m : Member] {
    // Pre-Conditions

    // queue is empty
    no m.qnxt

    // Post-Conditions

    // add n to m's queue
    m.qnxt' = (n -> m) 
}    

pred addToNonEmptyQueue[n : Node, m : Member] {
    // Pre-Condtions

    // queue is not empty
    some m.qnxt

    // Post-Conditions

    // add n to m's queue and point to last node
    m.qnxt' = m.qnxt + (n -> lastNodeInQueue[m.qnxt])
}

fun firstNodeInQueue[m : Member] : Node {
    (m.qnxt).m
}

fun lastNodeInQueue[queue : Node -> Node] : Node {
    // last node is in domain but not in counter domain
    queue.Node - Node.queue
}

pred memberPrommotion[n : Node, m : Member] {
    // Pre-Conditions

    // m's queue is not empty
    some m.qnxt

    // n is the first node in m's queue
    n = firstNodeInQueue[m]

    // Post-Conditions

    // remove n from m's queue and 2nd node becomes first
    m.qnxt' = m.qnxt - (n -> m) - (previousInQueue[n, m.qnxt]-> n) + (previousInQueue[n, m.qnxt] -> m)

    // n becomes a member
    Member' = Member + n

    // n's queue is empty
    no n.qnxt'

    // m now points to n
    m.nxt' = n

    // n now points to what m pointed to
    n.nxt' = m.nxt

    // Frame Conditions
    Leader' = Leader
    LQueue' = LQueue
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
    // all other members queues are unchanged
    (all m1 : (Member - m) | m1.qnxt' = m1.qnxt)
    // all other members next pointers are unchanged
    (all m1 : (Member - m) | m1.nxt' = m1.nxt)

}

fun previousInQueue[n : Node, queue : Node -> lone Node] : Node {
    queue.n
}

fun nextInQueue[n : Node, queue : Node -> lone Node] : Node {
    n.queue
}

pred memberExit[m : Member] {
    // Pre-Conditions

    // Leader cannot exit
    m != Leader

    // Post-Conditions

    // remove m from Member
    Member' = Member - m

    // change node that pointed to m to point to what m pointed to
    nxt' = nxt - (m -> m.nxt) - (nxt.m -> m) + (nxt.m -> m.nxt)

    // append m's queue to the node that m pointed to
    m.nxt.qnxt' = m.nxt.qnxt + m.qnxt
    
    // remove m from Leader queue if present
    m in (Leader.lnxt).Member
    implies
    memberExitLeaderQueue[m]

    // Frame Conditions
    Leader' = Leader
    outbox' = outbox
    rcvrs' = rcvrs
    // if m not in Leader queue, Leader queue is unchanged
    m not in (Leader.lnxt).Member implies (lnxt' = lnxt and LQueue' = LQueue)
    // all other members queues are unchanged
    (all m1 : (Member - m - m.nxt) | m1.qnxt' = m1.qnxt) 
}

fun previousInLeaderQueue[m : Member] : Member {
    (Leader.lnxt).m
}

fun nextInLeaderQueue[m : Member] : Member {
    m.(Leader.lnxt)
}

pred memberExitLeaderQueue[m : Member] {
    // Remove m from Leader's queue, making member that pointed to m point to the member m pointed to
    Leader.lnxt' = Leader.lnxt - (previousInLeaderQueue[m]-> m) 
        - (m -> nextInLeaderQueue[m])
        + (previousInLeaderQueue[m] -> nextInLeaderQueue[m])

    // Remove m from LQueue
    LQueue' = LQueue - m
}

pred nonMemberExit[n : Node] {
    some m : Member | nonMemberExitAux[n, m]
}

pred nonMemberExitAux[n : Node, m : Member] {
    // Pre-Conditions

    // n is not a Member
    n in Node - Member
    // n is in m's queue
    n in (m.qnxt).Node

    // Post-Conditions
    m.qnxt' = m.qnxt - (n -> nextInQueue[n, m.qnxt]) - (previousInQueue[n, m.qnxt] -> n) + (previousInQueue[n, m.qnxt] -> nextInQueue[n, m.qnxt])

    // Frame Conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    nxt' = nxt
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
    // all other members queues are unchanged
    (all m1 : (Member - m) | m1.qnxt' = m1.qnxt) 
}

pred leaderApplication[m : Member] {
    // Pre-Conditions
    m != Leader
    m not in (Leader.lnxt).Member

    // Post-Conditions
    no Leader.lnxt implies lnxt' = (Leader -> m -> Leader)
    (some Leader.lnxt implies 
        one m1 : Member - Leader | (m1 in (Leader.lnxt).Member and m1 not in Member.(Leader.lnxt))
        and
        (lnxt' = lnxt + (Leader -> m -> m1)) 
    )
    LQueue' = LQueue + m

    // Frame Conditions
    Leader' = Leader
    Member' = Member
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    rcvrs' = rcvrs
}

pred leaderPromotion[m : Member] {
    // Pre-Conditions
    some Leader.lnxt
    m = (Leader.lnxt).Leader
    no SendingMsg

    // Post-Conditions
    no Leader.lnxt'
    m.lnxt' = Leader.lnxt - (m -> Leader)
    LQueue' = LQueue - m // remove m from leader queue
    Leader' = m

    // Frame Conditions
    Member' = Member
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    rcvrs' = rcvrs
}

pred broadcastInitialisation[msg : Msg] {
    // Pre-Conditions

    // message is pending
    msg in PendingMsg
    // only leader can start broadcast
    msg.sndr = Leader 

    // Post-Conditions
    outbox' = outbox - (Leader -> msg) + (Leader.nxt -> msg)
    //PendingMsg' = PendingMsg - msg
    //SendingMsg' = SendingMsg + msg

    // Frame Conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    nxt' = nxt
    qnxt' = qnxt
    lnxt' = lnxt
}

pred messageRedirect[msg : Msg, m : Member] {
    // Pre-Conditions
    msg in SendingMsg
    msg in m.outbox

    // Post-Conditions
    outbox' = outbox - (m -> msg) + (m.nxt -> msg)
    rcvrs' = rcvrs + (msg -> m)

    // Frame Conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    nxt' = nxt
    qnxt' = qnxt
    lnxt' = lnxt
}

pred broadcastTermination[msg : Msg] {
    // Pre-Conditions
    msg in SendingMsg
    msg in Leader.outbox

    // Post-Conditions
    rcvrs' = rcvrs + (msg -> Leader)
    outbox' = outbox - (Leader -> msg)

    // Frame Conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    nxt' = nxt
    qnxt' = qnxt
    lnxt' = lnxt
    rcvrs' = rcvrs
}


pred trans[] {
    stutter[]
    or
    (some n : (Node - Member) | some m : Member | memberApplication[n, m])
    or
    (some n : Node | some m : Member | memberPrommotion[n, m])
    or
    (some m : Member | memberExit[m])
    or
    (some n : Node | nonMemberExit[n])
    or
    (some m : Member | leaderApplication[m])
    or
    (some m : Member | leaderPromotion[m])
    or
    (some msg : Msg | broadcastInitialisation[msg])
    
}

pred system[] {
    init[]
    and 
    always trans[]
}

fact {
    system[]
}


run {#Node=3 #Msg=1 and eventually (#Member=3 and some msg : Msg | broadcastInitialisation[msg])} for 10 steps