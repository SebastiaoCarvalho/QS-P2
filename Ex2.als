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
    no qnxt
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
    n not in Member
    n !in (Member.qnxt).Node

    // Post-Conditions
    no m.qnxt implies m.qnxt' = (n -> m)
    (some m.qnxt implies 
        one n1 : Node - Member | (n1 in (m.qnxt).Node and n1 not in Node.(m.qnxt)) // n1 is the last node
        and
        (m.qnxt' = m.qnxt + (n -> n1)) // now n is the last node and points to n1
    )

    // Frame Conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    nxt' = nxt
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
    (all m1 : (Member - m) | m1.qnxt' = m1.qnxt) // all other members queues are unchanged
}

pred memberPrommotion[n : Node, m : Member] {
    // Pre-Conditions
    some m.qnxt
    n = (m.qnxt).m

    // Post-Conditions
    m.qnxt' = m.qnxt - (n -> m) // remove n from m's queue
        - ((m.qnxt).n-> n) + ((m.qnxt).n -> m) // change node that pointed to first entry to point to m

    Member' = Member + n
    no n.qnxt'
    m.nxt' = n // m now points to n
    n.nxt' = m.nxt // n now points to what m pointed to

    // Frame Conditions
    Leader' = Leader
    LQueue' = LQueue
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
    (all m1 : (Member - m) | m1.qnxt' = m1.qnxt) // all other members queues are unchanged
    (all m1 : (Member - m) | m1.nxt' = m1.nxt) // all other members next pointers are unchanged

}

pred memberExit[m : Member] {
    // Pre-Conditions
    m != Leader

    // Post-Conditions
    Member' = Member - m
    nxt' = nxt - (m -> m.nxt) - (nxt.m -> m) + (nxt.m -> m.nxt) // change node that pointed to m to point to what m pointed to
    m.nxt.qnxt' = m.nxt.qnxt + m.qnxt // append m's queue to the node that m pointed to
    m in (Leader.lnxt).Member implies (
        Leader.lnxt' = Leader.lnxt 
            -((Leader.lnxt).m -> m) // change node that pointed to m to point to what m pointed to
            - (m -> m.(Leader.lnxt))
            + ((Leader.lnxt).m -> m.(Leader.lnxt))
        and
        LQueue' = LQueue - m
    )

    // Frame Conditions
    Leader' = Leader
    outbox' = outbox
    rcvrs' = rcvrs
    m not in (Leader.lnxt).Member implies (
        lnxt' = lnxt
        and
        LQueue' = LQueue
    )
    (all m1 : (Member - m - m.nxt) | m1.qnxt' = m1.qnxt) // all other members queues are unchanged
}

pred nonMemberExit[n : Node] {
    some m : Member | nonMemberExitAux[n, m]
}

pred nonMemberExitAux[n : Node, m : Member] {
    // Pre-Conditions
    n in Node - Member
    n in (m.qnxt).Node

    // Post-Conditions
    // Post-Conditions
    m.qnxt' = m.qnxt - (n -> n.(m.qnxt)) // remove n from m's queue
        - ((m.qnxt).n-> n) + ((m.qnxt).n -> n.(m.qnxt))

    // Frame Conditions
    Member' = Member
    Leader' = Leader
    LQueue' = LQueue
    nxt' = nxt
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
    (all m1 : (Member - m) | m1.qnxt' = m1.qnxt) // all other members queues are unchanged
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
    no PendingMsg

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

pred broadcastInitialisation {
    
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
}

pred system[] {
    init[]
    and 
    always trans[]
}

fact {
    system[]
}

pred removal {
    #Member' < #Member
}

pred queueExit {
    #qnxt' < #qnxt and #Member' = #Member
}

pred leaderPromotion {
    #lnxt' < #lnxt and #lnxt=2 and #Member'=3 and Leader'!=Leader
}

run {#Node=3 #Msg=0 (eventually leaderPromotion)} for 10 steps