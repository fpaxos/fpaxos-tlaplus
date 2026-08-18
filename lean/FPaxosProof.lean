import Veil

/-!
Direct Lean proofs for the safety-supporting invariants of `FPaxos.lean`.
These proofs use no SMT tactics and do not invoke Veil's `#check_invariants`.
-/

namespace FPaxosProof

universe uA uB uV uQ1 uQ2

structure State (Acceptor : Type uA) (Ballot : Type uB) (Value : Type uV) where
  maxBal : Acceptor → Option Ballot
  accepted : Acceptor → Option (Ballot × Value)
  oneA : Ballot → Prop
  oneB : Acceptor → Ballot → Option (Ballot × Value) → Prop
  twoA : Ballot → Value → Prop
  twoB : Acceptor → Ballot → Value → Prop

variable {Acceptor : Type uA} {Ballot : Type uB} {Value : Type uV}
variable {Quorum1 : Type uQ1} {Quorum2 : Type uQ2}
variable [DecidableEq Acceptor]

def Init (s : State Acceptor Ballot Value) : Prop :=
  (∀ a, s.maxBal a = none) ∧
  (∀ a, s.accepted a = none) ∧
  (∀ b, ¬s.oneA b) ∧
  (∀ a b prior, ¬s.oneB a b prior) ∧
  (∀ b v, ¬s.twoA b v) ∧
  (∀ a b v, ¬s.twoB a b v)

inductive Step
    (le : Ballot → Ballot → Prop)
    (quorum1Member : Quorum1 → Acceptor → Prop) :
    State Acceptor Ballot Value → State Acceptor Ballot Value → Prop
  | phase1a (s) (b : Ballot) :
      Step le quorum1Member s
        { s with oneA := fun b' => s.oneA b' ∨ b' = b }
  | phase1b (s) (a : Acceptor) (b : Ballot)
      (message : s.oneA b)
      (higher : ∀ old, s.maxBal a = some old → le old b ∧ old ≠ b) :
      Step le quorum1Member s
        { s with
          maxBal := Function.update s.maxBal a (some b)
          oneB := fun a' b' prior =>
            s.oneB a' b' prior ∨
              (a' = a ∧ b' = b ∧ prior = s.accepted a) }
  | phase2a (s) (b : Ballot) (v : Value) (q : Quorum1)
      (fresh : ∀ old, ¬s.twoA b old)
      (responses : ∀ a, quorum1Member q a → ∃ prior, s.oneB a b prior)
      (safeChoice :
        (∀ a prior, quorum1Member q a → ¬s.oneB a b (some prior)) ∨
        (∃ a previous, quorum1Member q a ∧
          s.oneB a b (some (previous, v)) ∧
          ∀ a' previous' v', quorum1Member q a' →
            s.oneB a' b (some (previous', v')) → le previous' previous)) :
      Step le quorum1Member s
        { s with twoA := fun b' v' => s.twoA b' v' ∨ (b' = b ∧ v' = v) }
  | phase2b (s) (a : Acceptor) (b : Ballot) (v : Value)
      (proposal : s.twoA b v)
      (notBelowPromise : ∀ old, s.maxBal a = some old → le old b) :
      Step le quorum1Member s
        { s with
          maxBal := Function.update s.maxBal a (some b)
          accepted := Function.update s.accepted a (some (b, v))
          twoB := fun a' b' v' =>
            s.twoB a' b' v' ∨ (a' = a ∧ b' = b ∧ v' = v) }

def ProposalUnique (s : State Acceptor Ballot Value) : Prop :=
  ∀ b v₁ v₂, s.twoA b v₁ → s.twoA b v₂ → v₁ = v₂

def VoteHasProposal (s : State Acceptor Ballot Value) : Prop :=
  ∀ a b v, s.twoB a b v → s.twoA b v

structure Invariants (s : State Acceptor Ballot Value) : Prop where
  proposalUnique : ProposalUnique s
  voteHasProposal : VoteHasProposal s

inductive Reachable
    (le : Ballot → Ballot → Prop)
    (quorum1Member : Quorum1 → Acceptor → Prop) :
    State Acceptor Ballot Value → Prop
  | init {s} : Init s → Reachable le quorum1Member s
  | step {s s'} :
      Reachable le quorum1Member s →
      Step le quorum1Member s s' →
      Reachable le quorum1Member s'

def OneVotePerAcceptorPerBallot (s : State Acceptor Ballot Value) : Prop :=
  ∀ a b v₁ v₂, s.twoB a b v₁ → s.twoB a b v₂ → v₁ = v₂

def Agreed
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Ballot Value) (v : Value) (b : Ballot) : Prop :=
  ∃ q, ∀ a, quorum2Member q a → s.twoB a b v

def OneValueAgreedPerBallot
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Ballot Value) : Prop :=
  ∀ b v₁ v₂,
    Agreed quorum2Member s v₁ b →
    Agreed quorum2Member s v₂ b →
    v₁ = v₂

def Decided
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Ballot Value) (v : Value) : Prop :=
  ∀ b, Agreed quorum2Member s v b

def Safety
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Ballot Value) : Prop :=
  ∀ v₁ v₂,
    Decided quorum2Member s v₁ →
    Decided quorum2Member s v₂ →
    v₁ = v₂

theorem init_proposalUnique (h : Init s) : ProposalUnique s := by
  intro b v₁ v₂ h₁
  exact False.elim (h.2.2.2.2.1 b v₁ h₁)

theorem init_voteHasProposal (h : Init s) : VoteHasProposal s := by
  intro a b v hv
  exact False.elim (h.2.2.2.2.2 a b v hv)

theorem proposalUnique_preserved
    (le : Ballot → Ballot → Prop)
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s s' : State Acceptor Ballot Value)
    (hinv : ProposalUnique s)
    (step : Step le quorum1Member s s') :
    ProposalUnique s' := by
  cases step with
  | phase1a => exact hinv
  | phase1b => exact hinv
  | phase2a b v q fresh responses safeChoice =>
      intro b' v₁ v₂ h₁ h₂
      rcases h₁ with h₁ | ⟨rfl, rfl⟩
      · rcases h₂ with h₂ | ⟨hb, rfl⟩
        · exact hinv b' v₁ v₂ h₁ h₂
        · subst hb
          exact False.elim (fresh v₁ h₁)
      · rcases h₂ with h₂ | ⟨_, rfl⟩
        · exact False.elim (fresh v₂ h₂)
        · rfl
  | phase2b => exact hinv

theorem voteHasProposal_preserved
    (le : Ballot → Ballot → Prop)
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s s' : State Acceptor Ballot Value)
    (hinv : VoteHasProposal s)
    (step : Step le quorum1Member s s') :
    VoteHasProposal s' := by
  cases step with
  | phase1a =>
      intro a b v hv
      exact hinv a b v hv
  | phase1b =>
      intro a b v hv
      exact hinv a b v hv
  | phase2a =>
      intro a b v hv
      exact Or.inl (hinv a b v hv)
  | phase2b a b v proposal notBelowPromise =>
      intro a' b' v' hv
      rcases hv with hv | ⟨rfl, rfl, rfl⟩
      · exact hinv a' b' v' hv
      · exact proposal

theorem init_invariants (h : Init s) : Invariants s where
  proposalUnique := init_proposalUnique h
  voteHasProposal := init_voteHasProposal h

theorem invariants_preserved
    (le : Ballot → Ballot → Prop)
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s s' : State Acceptor Ballot Value)
    (hinv : Invariants s)
    (step : Step le quorum1Member s s') :
    Invariants s' where
  proposalUnique :=
    proposalUnique_preserved le quorum1Member s s' hinv.proposalUnique step
  voteHasProposal :=
    voteHasProposal_preserved le quorum1Member s s' hinv.voteHasProposal step

theorem reachable_invariants
    (le : Ballot → Ballot → Prop)
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s : State Acceptor Ballot Value)
    (reachable : Reachable le quorum1Member s) :
    Invariants s := by
  induction reachable with
  | init h => exact init_invariants h
  | step reachable step ih =>
      exact invariants_preserved le quorum1Member _ _ ih step

theorem oneVotePerAcceptorPerBallot
    (hunique : ProposalUnique s)
    (hproposed : VoteHasProposal s) :
    OneVotePerAcceptorPerBallot s := by
  intro a b v₁ v₂ h₁ h₂
  exact hunique b v₁ v₂ (hproposed a b v₁ h₁) (hproposed a b v₂ h₂)

omit [DecidableEq Acceptor] in
theorem oneValueAgreedPerBallot
    [Nonempty Quorum1]
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (intersects : ∀ q₁ q₂, ∃ a, quorum1Member q₁ a ∧ quorum2Member q₂ a)
    (hunique : ProposalUnique s)
    (hproposed : VoteHasProposal s) :
    OneValueAgreedPerBallot quorum2Member s := by
  intro b v₁ v₂ ⟨q₂₁, hagreed₁⟩ ⟨q₂₂, hagreed₂⟩
  let q₁ : Quorum1 := Classical.choice inferInstance
  obtain ⟨a₁, _, ha₁⟩ := intersects q₁ q₂₁
  obtain ⟨a₂, _, ha₂⟩ := intersects q₁ q₂₂
  exact hunique b v₁ v₂
    (hproposed a₁ b v₁ (hagreed₁ a₁ ha₁))
    (hproposed a₂ b v₂ (hagreed₂ a₂ ha₂))

omit [DecidableEq Acceptor] in
theorem safety
    [Nonempty Ballot]
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Ballot Value)
    (hone : OneValueAgreedPerBallot quorum2Member s) :
    Safety quorum2Member s := by
  intro v₁ v₂ hdecided₁ hdecided₂
  let b : Ballot := Classical.choice inferInstance
  exact hone b v₁ v₂ (hdecided₁ b) (hdecided₂ b)

theorem reachable_safety
    [Nonempty Ballot] [Nonempty Quorum1]
    (le : Ballot → Ballot → Prop)
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (intersects : ∀ q₁ q₂, ∃ a, quorum1Member q₁ a ∧ quorum2Member q₂ a)
    (s : State Acceptor Ballot Value)
    (reachable : Reachable le quorum1Member s) :
    Safety quorum2Member s := by
  have hinv := reachable_invariants le quorum1Member s reachable
  apply safety quorum2Member s
  exact oneValueAgreedPerBallot
    quorum1Member quorum2Member intersects
    hinv.proposalUnique hinv.voteHasProposal

end FPaxosProof
