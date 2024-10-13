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
    m.qnxt' = m.qnxt - (n -> m) // remove first entry
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

pred trans[] {
    stutter[]
    or
    (some n : (Node - Member) | some m : Member | memberApplication[n, m])
    or
    (some n : Node | some m : Member | memberPrommotion[n, m])
}

pred system[] {
    init[]
    and 
    always trans[]
}

fact {
    system[]
}

run {#Node=3 #Msg=0 eventually (#Member=2 and #qnxt=1)} for 7