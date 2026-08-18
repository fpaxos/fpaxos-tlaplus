import Veil

/-!
A relational Veil translation of `FPaxos.tla`.

TLA+ sets of messages are represented by Boolean relations. The TLA+ `-1`
sentinel is represented by `hasPromised` and `hasVoted`, so ballots and values
remain well-typed.
-/

veil module FPaxos

type acceptor
type ballot
type value
type quorum1
type quorum2

instantiate ballotOrder : TotalOrder ballot

immutable relation quorum1Member (q : quorum1) (a : acceptor)
immutable relation quorum2Member (q : quorum2) (a : acceptor)

relation hasPromised (a : acceptor)
function maxBal (a : acceptor) : ballot
relation hasVoted (a : acceptor)
function maxVBal (a : acceptor) : ballot
function maxVal (a : acceptor) : value

relation oneAMsg (b : ballot)
relation oneBNoVote (a : acceptor) (b : ballot)
relation oneBVote (a : acceptor) (b : ballot) (votedBallot : ballot) (v : value)
relation twoAMsg (b : ballot) (v : value)
relation twoBMsg (a : acceptor) (b : ballot) (v : value)

#gen_state

theory ghost relation ballotLt (x y : ballot) :=
  ballotOrder.le x y ∧ x ≠ y

assumption [quorum_intersection]
  ∀ (q1 : quorum1) (q2 : quorum2),
    ∃ (a : acceptor), quorum1Member q1 a ∧ quorum2Member q2 a

after_init {
  hasPromised A := false
  maxBal A := *
  hasVoted A := false
  maxVBal A := *
  maxVal A := *
  oneAMsg B := false
  oneBNoVote A B := false
  oneBVote A B P V := false
  twoAMsg B V := false
  twoBMsg A B V := false
}

action phase1a (b : ballot) {
  oneAMsg b := true
}

action phase1b (a : acceptor) (b : ballot) {
  require oneAMsg b
  require ¬hasPromised a ∨ ballotLt (maxBal a) b
  if hasVoted a then
    oneBVote a b (maxVBal a) (maxVal a) := true
  else
    oneBNoVote a b := true
  hasPromised a := true
  maxBal a := b
}

action phase2a (b : ballot) (v : value) (q : quorum1) {
  require ∀ V, ¬twoAMsg b V
  require ∀ A, quorum1Member q A →
    (oneBNoVote A b ∨ ∃ Previous V, oneBVote A b Previous V)
  require
    (∀ A Previous V, quorum1Member q A →
      ¬oneBVote A b Previous V) ∨
    (∃ A Previous, quorum1Member q A ∧
      oneBVote A b Previous v ∧
      ∀ A2 Previous2 V2, quorum1Member q A2 →
        oneBVote A2 b Previous2 V2 →
        ballotOrder.le Previous2 Previous)
  twoAMsg b v := true
}

action phase2b (a : acceptor) (b : ballot) (v : value) {
  require twoAMsg b v
  require ¬hasPromised a ∨ ballotOrder.le (maxBal a) b
  hasPromised a := true
  maxBal a := b
  hasVoted a := true
  maxVBal a := b
  maxVal a := v
  twoBMsg a b v := true
}

invariant [proposal_unique]
  twoAMsg B V1 ∧ twoAMsg B V2 → V1 = V2

invariant [vote_has_proposal]
  twoBMsg A B V → twoAMsg B V

safety [one_value_agreed_per_ballot]
  (∃ Q1, ∀ A, quorum2Member Q1 A → twoBMsg A B V1) ∧
  (∃ Q2, ∀ A, quorum2Member Q2 A → twoBMsg A B V2) →
  V1 = V2

#gen_spec

end FPaxos
