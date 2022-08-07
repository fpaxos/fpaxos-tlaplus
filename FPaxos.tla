-------------------------------- MODULE FPaxos -------------------------------

EXTENDS Integers
CONSTANT Value, Acceptor, Quorum1, Quorum2

ASSUME QuorumAssumption ==
    /\ \A Q \in Quorum1 : Q \subseteq Acceptor
    /\ \A Q \in Quorum2 : Q \subseteq Acceptor
    /\ \A Q1 \in Quorum1 : \A Q2 \in Quorum2 : Q1 \cap Q2 # {}

Ballot ==  Nat

None == CHOOSE v : v \notin Ballot

Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

VARIABLE maxBal,
         maxVBal,
         maxVal,
         msgs

vars == <<maxBal, maxVBal, maxVal, msgs>>
Send(m) == msgs' = msgs \cup {m}

TypeOK ==
    /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVal \in [Acceptor -> Value \cup {None}]
    /\ msgs \subseteq Message

Init ==
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> -1]
    /\ maxVal = [a \in Acceptor |-> None]
    /\ msgs = {}

Phase1a(b) ==
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase1b(a) ==
    /\ \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                            mbal |-> maxVBal[a], mval |-> maxVal[a]])
    /\ UNCHANGED <<maxVBal, maxVal>>

Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorum1 :
        LET Q1b == {m \in msgs : /\ m.type = "1b"
                                 /\ m.acc \in Q
                                 /\ m.bal = b}
            Q1bv == {m \in Q1b : m.mbal \geq 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal \geq mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) ==
    \E m \in msgs : /\ m.type = "2a"
        /\ m.bal \geq maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
        /\ Send([type |-> "2b", acc |-> a,
                bal |-> m.bal, val |-> m.val])

Next ==
    \/ \E b \in Ballot : \/ Phase1a(b)
                         \/ \E v \in Value : Phase2a(b, v)
    \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

Sent2b(a,v,b) ==
    \E m \in msgs: /\ m.type = "2b"
                   /\ m.acc = a
                   /\ m.val = v
                   /\ m.bal = b

Sent2a(v,b) ==
    \E m \in msgs: /\ m.type = "2a"
                   /\ m.val = v
                   /\ m.bal = b

Agreed(v,b) ==
    \E Q \in Quorum2:
        \A a \in Q: Sent2b(a,v,b)

NoFutureProposal(v,b) ==
    \A v2 \in Value:
        \A b2 \in Ballot: (b2 > b /\ Sent2a(v2,b2)) => v=v2

SafeValue ==
    \A v \in Value:
        \A b \in Ballot: Agreed(v,b) => NoFutureProposal(v,b)

=============================================================================