---- MODULE FPaxos ----

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

VARIABLE
    \* @type: Str -> Int;
    maxBal,
    \* @type: Str -> Int;
    maxVBal,
    \* @type: Str -> Int;
    maxVal,
    \* @type: Set({bal: Int});
    1aMsgs,
    \* @type: Set({bal: Int, mbal: Int, acc: Str, mval: Int});
    1bMsgs,
    \* @type: Set({bal: Int, val: Int});
    2aMsgs,
    \* @type: Set({bal: Int, acc: Str, val: Int});
    2bMsgs

msgs == <<1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs>>
vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK ==
    /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVal \in [Acceptor -> Value \cup {-1}]
    /\ 1aMsgs \in SUBSET [bal : Ballot]
    /\ 1bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value \cup {-1}]
    /\ 2aMsgs \in SUBSET [bal : Ballot, val : Value]
    /\ 2bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, val : Value]

Init ==
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> -1]
    /\ maxVal = [a \in Acceptor |-> -1]
    /\ 1aMsgs = {}
    /\ 1bMsgs = {}
    /\ 2aMsgs = {}
    /\ 2bMsgs = {}

Phase1a(b) ==
    /\ 1aMsgs' = 1aMsgs \union {[bal |-> b]}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, 1bMsgs, 2aMsgs, 2bMsgs>>

Phase1b(a) ==
    /\ \E m \in 1aMsgs :
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ 1bMsgs' = 1bMsgs \union {[acc |-> a, bal |-> m.bal, mbal |-> maxVBal[a], mval |-> maxVal[a]]}
    /\ UNCHANGED <<maxVBal, maxVal, 1aMsgs, 2aMsgs, 2bMsgs>>

Phase2a(b, v) ==
  /\ ~ \E m \in 2aMsgs : m.bal = b
  /\ \E Q \in Quorum1 :
        LET Q1b == {m \in 1bMsgs : /\ m.acc \in Q
                                   /\ m.bal = b}
            Q1bv == {m \in Q1b : m.mbal \geq 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal \geq mm.mbal
  /\ 2aMsgs' = 2aMsgs \union {[bal |-> b, val |-> v]}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, 1aMsgs, 1bMsgs, 2bMsgs>>

Phase2b(a) ==
    /\ \E m \in 2aMsgs :
        /\ m.bal \geq maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
        /\ 2bMsgs' = 2bMsgs \union {[acc |-> a, bal |-> m.bal, val |-> m.val]}
    /\ UNCHANGED <<1aMsgs, 1bMsgs, 2aMsgs>>

Next ==
    \/ \E b \in Ballot : \/ Phase1a(b)
                         \/ \E v \in Value : Phase2a(b, v)
    \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars

Sent2b(a,v,b) ==
    \E m \in 2bMsgs:
        /\ m.acc = a
        /\ m.val = v
        /\ m.bal = b

Sent2a(v,b) ==
    \E m \in 2aMsgs:
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

====