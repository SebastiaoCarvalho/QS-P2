module Ex2

open Ex1

pred init[] {
    Member = Leader
    Msg = PendingMsg
    no qnxt
}

pred stutter[] {
    nxt' = nxt
    qnxt' = qnxt
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
}

pred memberApplication[n : Node, m: Member] {
    // Pre-Conditions
    n in (Node - Member)
    n !in (Member.qnxt).Node

    // Post-Conditions
    m.qnxt' = m.qnxt + (n -> ((m.qnxt).m))

    // Frame Conditions
    nxt' = nxt
    outbox' = outbox
    lnxt' = lnxt
    rcvrs' = rcvrs
    all m1 : (Member - m) | m1.qnxt' = m1.qnxt // all other members queues are unchanged
}

pred trans[] {
    stutter[]
    or
    some n : (Node - Member) | some m : Member | memberApplication[n, m]
}

pred system[] {
    init[]
    and 
    always trans[]
}

fact {
    system[]
}

run {#Node=2 eventually some qnxt} for 7