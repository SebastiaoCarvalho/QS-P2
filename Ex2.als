module Ex2

sig Node {
  var outbox: set Msg
}

var sig Member in Node { 
 var nxt: one Node, 
 var qnxt : Node -> lone Node 
}

var one sig Leader in Member {
   var lnxt: Member -> lone Member
}

var sig LQueue in Member {}

sig Msg {
  sndr: Node, 
  var rcvrs: set Node 
}

var sig SentMsg, SendingMsg, PendingMsg in Msg {}

fun visualizeMemberQueue[] : Node -> lone Node {
    Member.qnxt
}

fun visualizeLeaderQueue[] : Node -> lone Node {
    Leader.lnxt
}

pred init[] {
    // only 1 Member which is the Leader
    Member = Leader
    // Leader points to themselves
    Leader.nxt = Leader

    // Messages are all pending
    Msg = PendingMsg
    no SendingMsg
    no SentMsg

    // load messages in the sender's outbox
    (all n : Node | n.outbox = sndr.n)

    // all queues are empty
    no LQueue
    no qnxt
    no lnxt

    // no messages received
    no rcvrs
}

// Stutter predicates

pred stutter {
    topologicStutter[]
    broadcastStutter[]
}

pred broadcastStutter {
    messageStutter[]
    rcvrs' = rcvrs
    outbox' = outbox
}

pred messageStutter {
    PendingMsg' = PendingMsg
    SendingMsg' = SendingMsg
    SentMsg' = SentMsg
}

pred topologicStutter {
    leaderStutter[]
    memberStutter[]
}

pred leaderStutter {
    Leader' = Leader
    LQueue' = LQueue
    lnxt' = lnxt
}

pred memberStutter {
    Member' = Member
    nxt' = nxt
    qnxt' = qnxt
}

// Utility functions for state transformers

fun firstNodeInQueue[m : Member] : Node {
    (m.qnxt).m
}

fun lastNodeInQueue[queue : Node -> Node] : Node {
    // last node is in domain but not in counter domain
    queue.Node - Node.queue
}

pred isNodeInQueue[n : Node, queue : Node -> lone Node] {
    n in queue.Node
}

pred inAnyQueue[n : Node] {
    n in (Member.qnxt).Node
}

pred isInLeaderQueue[m : Member] {
    m in (Leader.lnxt).Member
}

fun previousInQueue[n : Node, queue : Node -> lone Node] : Node {
    queue.n
}

fun nextInQueue[n : Node, queue : Node -> lone Node] : Node {
    n.queue
}

fun previousInLeaderQueue[m : Member] : Member {
    (Leader.lnxt).m
}

fun nextInLeaderQueue[m : Member] : Member {
    m.(Leader.lnxt)
}

fun lastMemberInLeaderQueue : Member {
    // last member is in domain but not in counter domain
    (Leader.lnxt).Member - Member.(Leader.lnxt)
}

// State transformers

pred memberApplication[n : Node, m: Member] {
    // Pre-Conditions

    // n is not a member
    n not in Member
    // n is not in any other member's queue
    ! inAnyQueue[n]

    // Post-Conditions

    // add n to m's queue
    addToEmptyQueue[n, m]
    or
    addToNonEmptyQueue[n, m]
    
    // Frame Conditions
    Member' = Member
    nxt' = nxt
    // all other members queues are unchanged
    (all m1 : (Member - m) | m1.qnxt' = m1.qnxt)
    leaderStutter[]
    broadcastStutter[]
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

pred memberPrommotion[m : Member] {
    some n : Node | memberPrommotionAux[n, m]
}

pred memberPrommotionAux[n : Node, m : Member] {
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


    // Frame Conditions
    leaderStutter[]
    // all other members outboxes are unchanged
    (all m1 : (Member - n) | m1.outbox' = m1.outbox)
    // all other members queues are unchanged
    (all m1 : (Member - m) | m1.qnxt' = m1.qnxt)
    broadcastStutter[]

}

pred memberExit[m : Member] {
    // Pre-Conditions

    // Leader cannot exit
    m != Leader

    // m is not in the leader queue
    ! isInLeaderQueue[m]

    // m's member queue is empty
    no m.qnxt

    // all of m's messages have been sent
    no (m.outbox)

    // Post-Conditions

    // remove m from Member
    Member' = Member - m

    // change node that pointed to m to point to what m pointed to
    nxt' = nxt - (m -> m.nxt) - (nxt.m -> m) + (nxt.m -> m.nxt)

    // Frame Conditions
    leaderStutter[]
    qnxt' = qnxt
    broadcastStutter[]
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

    // update m's queue to have node that pointed to n point to what n pointed to
    m.qnxt' = m.qnxt - (n -> nextInQueue[n, m.qnxt]) - (previousInQueue[n, m.qnxt] -> n) + (previousInQueue[n, m.qnxt] -> nextInQueue[n, m.qnxt])

    // Frame Conditions
    Member' = Member
    nxt' = nxt
    // all other members queues are unchanged
    (all m1 : (Member - m) | m1.qnxt' = m1.qnxt)
    leaderStutter[]
    broadcastStutter[]
}

pred leaderApplication[m : Member] {
    // Pre-Conditions

    // m is not the Leader
    m != Leader
    // m is not already in the leader queue
    m not in (Leader.lnxt).Member

    // Post-Conditions

    // if queue was empty, crete it and make m point to Leader
    no Leader.lnxt implies lnxt' = (Leader -> m -> Leader)

    // else, m points to last member in the queue
    else lnxt' = lnxt  + (Leader -> m -> lastMemberInLeaderQueue[])

    // add m to the leader queue
    LQueue' = LQueue + m

    // Frame Conditions
    Leader' = Leader
    memberStutter[]
    broadcastStutter[]
}

pred leaderPrommotion {
    some m : Member - Leader | leaderPrommotionAux[m]
}

pred leaderPrommotionAux[m : Member] {
    // Pre-Conditions

    // leader queue is not empty
    some Leader.lnxt
    // m is the first member in the leader queue
    m = (Leader.lnxt).Leader
    // no broadcast in progress
    no SendingMsg
    // the Leader already broadcasted all of their messages
    no (sndr.Leader & (SendingMsg + PendingMsg))

    // Post-Conditions
    no Leader.lnxt'
    m.lnxt' = Leader.lnxt - (m -> Leader)
    LQueue' = LQueue - m // remove m from leader queue
    Leader' = m

    // Frame Conditions
    memberStutter[]
    broadcastStutter[]
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

    // remove msg from Leader's outbox and add to next node's outbox
    outbox' = outbox - (Leader -> msg) + (Leader.nxt -> msg)

    // next node receives the message
    rcvrs' = rcvrs + (msg -> Leader.nxt)

    // move message from Pending to Sending
    PendingMsg' = PendingMsg - msg
    SendingMsg' = SendingMsg + msg

    // Frame Conditions
    topologicStutter[]
    SentMsg' = SentMsg
}

pred messageRedirect[msg : Msg] {
    some m : Member | messageRedirectAux[msg, m]
}

pred messageRedirectAux[msg : Msg, m : Member] {
    // Pre-Conditions

    // message is in the middle of broadcast
    msg in SendingMsg

    // message is in m's outbox
    msg in m.outbox
    // can't allow redirect from Leader (sender)
    m != Leader

    // Post-Conditions

    // remove msg from m's outbox and add to next node's outbox
    outbox' = outbox - (m -> msg) + (m.nxt -> msg)

    // next node receives the message if it's not the Leader (sender)
    m.nxt != Leader implies rcvrs' = rcvrs + (msg -> m.nxt) 
    else rcvrs' = rcvrs 

    // Frame Conditions
    topologicStutter[]
    messageStutter[]
}

pred broadcastTermination[msg : Msg] {
    // Pre-Conditions

    // msg is in the middle of broadcast
    msg in SendingMsg
    // msg is back in Leader's outbox (sender)
    msg in Leader.outbox

    // Post-Conditions

    // remove msg from the Leader's outbox
    outbox' = outbox - (Leader -> msg)

    // remove from Sending since broadcast is done
    SendingMsg' = SendingMsg - msg

    // add to SentMsg since broadcast is done
    SentMsg' = SentMsg + msg

    // Frame Conditions
    topologicStutter[]
    rcvrs' = rcvrs
    PendingMsg' = PendingMsg
}


pred trans[] {
    stutter[]
    or
    (some n : (Node - Member) | some m : Member | memberApplication[n, m])
    or
    (some m : Member | memberPrommotion[m])
    or
    (some m : Member | memberExit[m])
    or
    (some n : Node | nonMemberExit[n])
    or
    (some m : Member | leaderApplication[m])
    or
    (leaderPrommotion[])
    or
    (some msg : Msg | broadcastInitialisation[msg])
    or
    (some msg : Msg | messageRedirect[msg])
    or
    (some msg : Msg | broadcastTermination[msg])
    
}

pred system[] {
    init[]
    and 
    always trans[]
}

pred trace2[] {
    #Node>=5
    eventually (leaderPrommotion[])
    eventually (some m : Member | memberPrommotion[m])
    eventually (some m : Member | memberExit[m])
    eventually (some n : Node | nonMemberExit[n])
    eventually (some m: Msg | broadcastTermination[m])
}

fact {
    system[]
}

run {trace2[]} for 6 but 1 Msg