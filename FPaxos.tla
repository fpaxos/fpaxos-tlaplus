-------------------------------- MODULE FPaxos -------------------------------

EXTENDS Integers, FiniteSets

CONSTANT
    \* @type: Set(Int);
    Value,
    \* @type: Set(Str);
    Acceptor,
    \* @type: Set(Set(Str));
    Quorum1,
    \* @type: Set(Set(Str));
    Quorum2,
    \* @type: Set(Int);
    Ballot

ASSUME QuorumAssumption ==
    /\ \A Q \in Quorum1 : Q \subseteq Acceptor
    /\ \A Q \in Quorum2 : Q \subseteq Acceptor
    /\ \A Q1 \in Quorum1 : \A Q2 \in Quorum2 : Q1 \cap Q2 # {}

Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
                 mbal : Ballot \cup {-1}, mval : Value \cup {-1}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

VARIABLE
    \* @type: Str -> Int;
    maxBal,
    \* @type: Str -> Int;
    maxVBal,
    \* @type: Str -> Int;
    maxVal,
    \* @type: Set([type: Str, bal: Int, mbal: Int, acc: Str, val: Int, mval: Int]);
    msgs

vars == <<maxBal, maxVBal, maxVal, msgs>>
Send(m) == msgs' = msgs \cup {m}

TypeOK ==
    /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVal \in [Acceptor -> Value \cup {-1}]
    /\ msgs \in SUBSET Message

Init ==
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> -1]
    /\ maxVal = [a \in Acceptor |-> -1]
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

Decided(v) ==
    \A b \in Ballot: Agreed(v,b)

NoFutureProposal(v,b) ==
    \A v2 \in Value:
        \A b2 \in Ballot: (b2 > b /\ Sent2a(v2,b2)) => v=v2

SafeValue ==
    \A v \in Value:
        \A b \in Ballot: Agreed(v,b) => NoFutureProposal(v,b)

Safety == Cardinality({ v \in Value: Decided(v) }) \leq 1

\* Below is my first attempt at a inductive invariant. Not currently working

OneValueAgreedPerBallot ==
    \A b \in Ballot: Cardinality({ v \in Value: Agreed(v,b) }) \leq 1

OneVotePerAcceptorPerBallot ==
    \A a \in Acceptor:
        \A b \in Ballot: Cardinality({ v \in Value: Sent2b(a,v,b) }) \leq 1

SafeStates ==
    \A a \in Acceptor:
        /\ \/ maxBal[a] = -1
           \/ \E m \in msgs: m.bal = maxBal[a]
        /\ \/ (maxVBal[a] = -1 /\ maxVal[a] = -1)
           \/ \E m \in msgs:
                /\ m.type = "2a"
                /\ m.bal = maxVBal[a]
                /\ m.val = maxVal[a]

SafeMessage ==
    \A m \in msgs:
        /\ m.type = "1a"
        \/ /\ m.type = "2b"
           /\ \E a \in Acceptor:
                /\ m.acc = a
                /\ \/ /\ maxBal[a] \geq m.bal
                      /\ maxVBal[a] = m.bal
                      /\ maxVal[a] = m.val
                   \/ /\ m.bal < maxBal[a]
                      /\ \E m2 \in msgs:
                        /\ m2.type = "2a"
                        /\ m2.bal > m.mbal
                        /\ m.mbal = m2.bal
                        /\ m.mval = m2.val
            /\ \E m2 \in msgs:
                /\ m2.type = "2a"
                /\ m2.bal = m.bal
                /\ m2.val = m.val
        \/ /\ m.type = "1b"
           /\ \E a \in Acceptor:
                /\ m.acc = a
                /\ \/ /\ m.bal = maxBal[a]
                      /\ m.mbal = maxVBal[a]
                      /\ m.mval = maxVal[a]
                   \/ /\ m.bal < maxBal[a]
                      /\ \E m2 \in msgs:
                        /\ m2.type = "2a"
                        /\ m2.bal > m.mbal
                        /\ m.mbal = m2.bal
                        /\ m.mval = m2.val
           /\ \E m2 \in Message:
                /\ m2.type = "2a"
                /\ m2.bal = m.mbal
                /\ m2.val = m.mval
        \/ /\ m.type = "2a"
           /\ \E Q \in Quorum1:
                /\ \A a2 \in Q:
                    \E m2 \in Message:
                        /\ m2.type = "1b"
                        /\ m2.acc = a2
                        /\ m2.bal = m.bal
                /\ \E a_max \in Q:
                    \E bal_max \in Ballot:
                        \E m_max \in Message:
                            /\ m_max.type = "1b"
                            /\ m_max.acc = a_max
                            /\ m_max.bal = m.bal
                            /\ m_max.mbal = bal_max
                            /\ m_max.mval = m.mval
                    /\ \A a2 \in Q:
                        \E m2 \in Message:
                            /\ m2.type = "1b"
                            /\ m2.acc = a2
                            /\ m2.bal = m.bal
                            /\ bal_max \geq m2.mbal


Inv ==
    /\ TypeOK
    /\ SafeStates
    /\ SafeMessage
    /\ SafeValue
    /\ Safety

=============================================================================