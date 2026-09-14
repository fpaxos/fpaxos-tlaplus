import Std

/-!
A pure Lean translation of the state machine and safety properties in
`FPaxos.tla`.

TLA+ sets are represented by predicates. The `-1` sentinel used for an
acceptor with no promise or vote is represented by `Option.none`, keeping
ballots and values intrinsically well-typed.
-/

namespace FPaxos

universe uA uV uQ1 uQ2

/-- Ballot numbers are the integers used by the TLA+ specification. -/
abbrev Ballot := Int

/-- The append-only message sets from `FPaxos.tla`, as characteristic predicates. -/
structure Messages (Acceptor : Type uA) (Value : Type uV) where
  oneA : Ballot → Prop
  oneB : Acceptor → Ballot → Option (Ballot × Value) → Prop
  twoA : Ballot → Value → Prop
  twoB : Acceptor → Ballot → Value → Prop

/--
The mutable variables from `FPaxos.tla`.

`maxBal = none` represents no promise, while `accepted = none` represents the
paired `maxVBal = maxVal = -1` case. Pairing an accepted ballot with its value
rules out unreachable states where only one of the two TLA+ fields is `-1`.
-/
structure State (Acceptor : Type uA) (Value : Type uV) where
  maxBal : Acceptor → Option Ballot
  accepted : Acceptor → Option (Ballot × Value)
  messages : Messages Acceptor Value

variable {Acceptor : Type uA} {Value : Type uV}
variable {Quorum1 : Type uQ1} {Quorum2 : Type uQ2}
variable [DecidableEq Acceptor]

def update (f : Acceptor → α) (key : Acceptor) (value : α) : Acceptor → α :=
  fun a => if a = key then value else f a

/-- The TLA+ `Init` predicate: no acceptor state and no messages. -/
def Init (s : State Acceptor Value) : Prop :=
  (∀ a, s.maxBal a = none) ∧
  (∀ a, s.accepted a = none) ∧
  (∀ b, ¬s.messages.oneA b) ∧
  (∀ a b prior, ¬s.messages.oneB a b prior) ∧
  (∀ b v, ¬s.messages.twoA b v) ∧
  (∀ a b v, ¬s.messages.twoB a b v)

/-- A proposer broadcasts a phase-one request for `b`. -/
def Phase1a (b : Ballot) (s s' : State Acceptor Value) : Prop :=
  s' = { s with messages := {
    s.messages with oneA := fun b' => s.messages.oneA b' ∨ b' = b } }

/-- An acceptor promises a higher ballot and reports its previous vote. -/
def Phase1b (a : Acceptor) (b : Ballot)
    (s s' : State Acceptor Value) : Prop :=
  s.messages.oneA b ∧
  (∀ old, s.maxBal a = some old → old < b) ∧
  s' =
    { s with
      maxBal := update s.maxBal a (some b)
      messages := { s.messages with
        oneB := fun a' b' prior =>
          s.messages.oneB a' b' prior ∨
            (a' = a ∧ b' = b ∧ prior = s.accepted a) } }

/--
A proposer chooses a value after collecting a phase-one quorum. If any
response contains a vote, the value must come from a highest such ballot.
-/
def Phase2a (quorum1Member : Quorum1 → Acceptor → Prop)
    (b : Ballot) (v : Value) (q : Quorum1)
    (s s' : State Acceptor Value) : Prop :=
  (∀ old, ¬s.messages.twoA b old) ∧
  (∀ a, quorum1Member q a → ∃ prior, s.messages.oneB a b prior) ∧
  ((∀ a prior, quorum1Member q a → ¬s.messages.oneB a b (some prior)) ∨
    (∃ a previous, quorum1Member q a ∧
      s.messages.oneB a b (some (previous, v)) ∧
      ∀ a' previous' v', quorum1Member q a' →
        s.messages.oneB a' b (some (previous', v')) →
          previous' ≤ previous)) ∧
  s' = { s with messages := { s.messages with
    twoA := fun b' v' => s.messages.twoA b' v' ∨ (b' = b ∧ v' = v) } }

/-- An acceptor votes for a proposal that is not below its current promise. -/
def Phase2b (a : Acceptor) (b : Ballot) (v : Value)
    (s s' : State Acceptor Value) : Prop :=
  s.messages.twoA b v ∧
  (∀ old, s.maxBal a = some old → old ≤ b) ∧
  s' =
    { s with
      maxBal := update s.maxBal a (some b)
      accepted := update s.accepted a (some (b, v))
      messages := { s.messages with
        twoB := fun a' b' v' =>
          s.messages.twoB a' b' v' ∨
            (a' = a ∧ b' = b ∧ v' = v) } }

/-- The TLA+ `Next` relation: one of the four protocol actions occurs. -/
inductive Step
    (quorum1Member : Quorum1 → Acceptor → Prop) :
    State Acceptor Value → State Acceptor Value → Prop
  | phase1a (b : Ballot) : Phase1a b s s' → Step quorum1Member s s'
  | phase1b (a : Acceptor) (b : Ballot) :
      Phase1b a b s s' → Step quorum1Member s s'
  | phase2a (b : Ballot) (v : Value) (q : Quorum1) :
      Phase2a quorum1Member b v q s s' → Step quorum1Member s s'
  | phase2b (a : Acceptor) (b : Ballot) (v : Value) :
      Phase2b a b v s s' → Step quorum1Member s s'

/-- States obtained from `Init` by finitely many `Step`s. -/
inductive Reachable
    (quorum1Member : Quorum1 → Acceptor → Prop) :
    State Acceptor Value → Prop
  | init {s} : Init s → Reachable quorum1Member s
  | step {s s'} :
      Reachable quorum1Member s →
      Step quorum1Member s s' →
      Reachable quorum1Member s'

def Agreed
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Value) (v : Value) (b : Ballot) : Prop :=
  ∃ q, ∀ a, quorum2Member q a → s.messages.twoB a b v

/-- The literal TLA+ `NoFutureProposal` predicate (lines 118--120). -/
def NoFutureProposal
    (s : State Acceptor Value) (v : Value) (b : Ballot) : Prop :=
  ∀ v₂ b₂, b < b₂ → s.messages.twoA b₂ v₂ → v = v₂

/-- The literal TLA+ `SafeValue` predicate (lines 122--124). -/
def SafeValue
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Value) : Prop :=
  ∀ v b, Agreed quorum2Member s v b → NoFutureProposal s v b

def Decided
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Value) (v : Value) : Prop :=
  ∀ b, Agreed quorum2Member s v b

def Safety
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Value) : Prop :=
  ∀ v₁ v₂,
    Decided quorum2Member s v₁ →
    Decided quorum2Member s v₂ →
    v₁ = v₂

end FPaxos
