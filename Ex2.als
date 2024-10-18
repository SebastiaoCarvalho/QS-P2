module Ex2

sig Node {}

var sig Member in Node {
    var nxt: lone Member,
    var qnxt : Node -> lone Node,
    var outbox: set Msg
}

var one sig Leader in Member {
    var lnxt: Node -> lone Node
}

var sig LQueue in Member {}

sig Msg {
    sndr: Node,
    var rcvrs: set Node
}

var sig SentMsg, SendingMsg, PendingMsg in Msg {}

fun visualizeQueue[] : Node -> lone Node {
    Member.qnxt
}

fun visualizeLeader[] : Node -> lone Node {
    Leader.lnxt
}

pred init[] {
    Member = Leader
    Leader.nxt = Leader
    Msg = PendingMsg
    no SendingMsg
    no SentMsg
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
    messageStutter[]
}

pred messageStutter[] {
    PendingMsg' = PendingMsg
    SendingMsg' = SendingMsg
    SentMsg' = SentMsg
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
    messageStutter[]
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

    // m now points to n and n points to what m pointed to
    nxt' = nxt - (m -> m.nxt) + (m -> n) + (n -> m.nxt)

    // put n's messages in n's outbox
    n.outbox' = sndr.n

    // Frame Conditions
    Leader' = Leader
    LQueue' = LQueue
    lnxt' = lnxt
    rcvrs' = rcvrs
    // all other members outboxes are unchanged
    (all m1 : (Member - n) | m1.outbox' = m1.outbox)
    // all other members queues are unchanged
    (all m1 : (Member - m) | m1.qnxt' = m1.qnxt)
    messageStutter[]

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

    // m is not in the leader queue
    m not in (Leader.lnxt).Member

    // m's member queue is empty
    no m.qnxt

    // all of m's messages have been sent
    (sndr.m & SentMsg) = sndr.m

    // Post-Conditions

    // remove m from Member
    Member' = Member - m

    // change node that pointed to m to point to what m pointed to
    nxt' = nxt - (m -> m.nxt) - (nxt.m -> m) + (nxt.m -> m.nxt)

    // Frame Conditions
    Leader' = Leader
    outbox' = outbox
    rcvrs' = rcvrs
    lnxt' = lnxt
    qnxt' = qnxt
    messageStutter[]
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
    messageStutter[]
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
    messageStutter[]
}

pred leaderPromotion[m : Member] {
    // Pre-Conditions
    some Leader.lnxt
    m = (Leader.lnxt).Leader
    no SendingMsg
    no Leader.outbox

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
    messageStutter[]
}

pred broadcastInitialisation[msg : Msg] {
    // Pre-Conditions

    // message is pending
    msg in PendingMsg
    // only leader can start broadcast
    msg.sndr = Leader 
    // only start broadcast if more than one member
    some Member - Leader

    // Post-Conditions
    outbox' = outbox - (Leader -> msg) + (Leader.nxt -> msg)
    PendingMsg' = PendingMsg - msg
    SendingMsg' = SendingMsg + msg

    // Frame Conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    nxt' = nxt
    qnxt' = qnxt
    lnxt' = lnxt
    SentMsg' = SentMsg
    rcvrs' = rcvrs

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
    messageStutter[]
}

pred broadcastTermination[msg : Msg] {
    // Pre-Conditions
    msg in SendingMsg
    msg in Leader.outbox

    // Post-Conditions
    outbox' = outbox - (Leader -> msg)
    SendingMsg' = SendingMsg - msg
    SentMsg' = SentMsg + msg

    // Frame Conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    nxt' = nxt
    qnxt' = qnxt
    lnxt' = lnxt
    rcvrs' = rcvrs
    PendingMsg' = PendingMsg
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
    or
    (some msg : Msg, m : Member | messageRedirect[msg, m])
    or
    (some msg : Msg | broadcastTermination[msg])
    
}

pred system[] {
    init[]
    and 
    always trans[]
}

pred trace1[] {
    #Node>=5
    eventually (some m : Member | leaderPromotion[m])
    eventually (some n : Node | some m : Member | memberPrommotion[n, m])
    eventually (some m : Member | memberExit[m])
    eventually (some n : Node | nonMemberExit[n])
    eventually (some m: Msg | broadcastTermination[m])
}

fact {
    system[]
}

run {trace1[]} for 6 but 10 steps