import Std

/-!
A pure Lean translation of `FPaxos.tla`. Type parameters and membership
predicates represent the TLA+ constants (lines 5--15); quorum intersection
(lines 17--20) is defined below. Lean types enforce `TypeOK` (lines 41--48),
predicates represent sets, and `none` replaces `-1`.
-/

namespace FPaxos

universe uA uV uQ1 uQ2

/-- TLA+ ballot numbers (lines 14--15). -/
abbrev Ballot := Int

/--
The `1aMsgs`, `1bMsgs`, `2aMsgs`, and `2bMsgs` sets (lines 29--36), grouped
as in the TLA+ `msgs` tuple (line 38).
-/
structure Messages (Acceptor : Type uA) (Value : Type uV) where
  oneA : Ballot → Prop
  oneB : Acceptor → Ballot → Option (Ballot × Value) → Prop
  twoA : Ballot → Value → Prop
  twoB : Acceptor → Ballot → Value → Prop

/--
The TLA+ `vars` tuple (lines 22--39). `accepted` combines `maxVBal` and
`maxVal`, preserving their reachable-state pairing by construction.
-/
structure State (Acceptor : Type uA) (Value : Type uV) where
  maxBal : Acceptor → Option Ballot
  accepted : Acceptor → Option (Ballot × Value)
  messages : Messages Acceptor Value

variable {Acceptor : Type uA} {Value : Type uV}
variable {Quorum1 : Type uQ1} {Quorum2 : Type uQ2}
variable [DecidableEq Acceptor]

/--
TLA+ `QuorumAssumption` (lines 17--20). Acceptor-typed membership enforces
the two subset clauses, leaving the intersection clause explicit.
-/
def QuorumAssumption
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (quorum2Member : Quorum2 → Acceptor → Prop) : Prop :=
  ∀ q₁ q₂, ∃ a, quorum1Member q₁ a ∧ quorum2Member q₂ a

/--
Functional form of TLA+ `[f EXCEPT ![key] = value]` (for example, line 67).
-/
def update (f : Acceptor → α) (key : Acceptor) (value : α) : Acceptor → α :=
  fun a => if a = key then value else f a

/--
The TLA+ `Init` predicate (lines 50--57), with `none` for `-1` and false
membership predicates for empty sets.
-/
def Init (s : State Acceptor Value) : Prop :=
  (∀ a, s.maxBal a = none) ∧
  (∀ a, s.accepted a = none) ∧
  (∀ b, ¬s.messages.oneA b) ∧
  (∀ a b prior, ¬s.messages.oneB a b prior) ∧
  (∀ b v, ¬s.messages.twoA b v) ∧
  (∀ a b v, ¬s.messages.twoB a b v)

/--
TLA+ `Phase1a(b)` (lines 59--61); predicate disjunction implements set union.
-/
def Phase1a (b : Ballot) (s s' : State Acceptor Value) : Prop :=
  s' = { s with messages := {
    s.messages with oneA := fun b' => s.messages.oneA b' ∨ b' = b } }

/--
TLA+ `Phase1b(a)` (lines 63--68), with the selected request ballot explicit
as `b` and its `mbal`/`mval` fields paired in `accepted`.
-/
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
TLA+ `Phase2a(b, v)` (lines 70--82), with the selected phase-one quorum
explicit as `q`.
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

/--
TLA+ `Phase2b(a)` (lines 84--91), with the selected proposal explicit as
`b` and `v`.
-/
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

/--
The non-stuttering part of TLA+ `Next` (lines 93--96); constructor parameters
make its existential choices explicit.
-/
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

/--
Finite reachability for TLA+ `Spec` (line 98). Stuttering is omitted because
it adds no reachable states.
-/
inductive Reachable
    (quorum1Member : Quorum1 → Acceptor → Prop) :
    State Acceptor Value → Prop
  | init {s} : Init s → Reachable quorum1Member s
  | step {s s'} :
      Reachable quorum1Member s →
      Step quorum1Member s s' →
      Reachable quorum1Member s'

/--
TLA+ `Agreed(v, b)` (lines 111--113), with `Sent2b` (lines 100--104) inlined.
-/
def Agreed
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Value) (v : Value) (b : Ballot) : Prop :=
  ∃ q, ∀ a, quorum2Member q a → s.messages.twoB a b v

/--
TLA+ `NoFutureProposal(v, b)` (lines 118--120), with `Sent2a`
(lines 106--109) inlined.
-/
def NoFutureProposal
    (s : State Acceptor Value) (v : Value) (b : Ballot) : Prop :=
  ∀ v₂ b₂, b < b₂ → s.messages.twoA b₂ v₂ → v = v₂

/-- TLA+ `SafeValue` (lines 122--124), stated as a property of one state. -/
def SafeValue
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Value) : Prop :=
  ∀ v b, Agreed quorum2Member s v b → NoFutureProposal s v b

/-- TLA+ `Decided(v)` (lines 115--116). -/
def Decided
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Value) (v : Value) : Prop :=
  ∀ b, Agreed quorum2Member s v b

/--
TLA+ `Safety` (line 126), with cardinality at most one expressed as pairwise
equality.
-/
def Safety
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Value) : Prop :=
  ∀ v₁ v₂,
    Decided quorum2Member s v₁ →
    Decided quorum2Member s v₂ →
    v₁ = v₂

end FPaxos
