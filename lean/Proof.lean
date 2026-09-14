import FPaxos

namespace FPaxos

universe uA uV uQ1 uQ2

variable {Acceptor : Type uA} {Value : Type uV}
variable {Quorum1 : Type uQ1} {Quorum2 : Type uQ2}
variable [DecidableEq Acceptor]

def ProposalUnique (s : State Acceptor Value) : Prop :=
  ∀ b v₁ v₂, s.twoA b v₁ → s.twoA b v₂ → v₁ = v₂

def VoteHasProposal (s : State Acceptor Value) : Prop :=
  ∀ a b v, s.twoB a b v → s.twoA b v

def MaxBalCoversOneB (s : State Acceptor Value) : Prop :=
  ∀ a b prior, s.oneB a b prior →
    ∃ current, s.maxBal a = some current ∧ b ≤ current

def AcceptedCoversVotes (s : State Acceptor Value) : Prop :=
  ∀ a b v, s.twoB a b v →
    ∃ current value, s.accepted a = some (current, value) ∧ b ≤ current

def AcceptedHasVote (s : State Acceptor Value) : Prop :=
  ∀ a b v, s.accepted a = some (b, v) → s.twoB a b v

def AcceptedBelowMaxBal (s : State Acceptor Value) : Prop :=
  ∀ a b v, s.accepted a = some (b, v) →
    ∃ current, s.maxBal a = some current ∧ b ≤ current

def OneBHasVote (s : State Acceptor Value) : Prop :=
  ∀ a b previous v, s.oneB a b (some (previous, v)) →
    s.twoB a previous v

def OneBPreviousBelow (s : State Acceptor Value) : Prop :=
  ∀ a b previous v, s.oneB a b (some (previous, v)) →
    previous < b

/--
A phase-one response remembers enough of the acceptor's history to account for
every lower vote, including votes inspected after the response was sent.
-/
def OneBCoversLowerVotes (s : State Acceptor Value) : Prop :=
  ∀ a b prior voted value, s.oneB a b prior → s.twoB a voted value →
    voted < b →
    ∃ previous previousValue,
      prior = some (previous, previousValue) ∧ voted ≤ previous

/--
A finite phase-one certificate for a proposal. The recursive parent records
why the highest reported value was itself safe; this avoids assuming that the
ballot order is well-founded.
-/
inductive ProposalCertificate
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s : State Acceptor Value) : Ballot → Value → Prop
  | noPrevious (b v : _) (q : Quorum1)
      (responses : ∀ a, quorum1Member q a → s.oneB a b none) :
      ProposalCertificate quorum1Member s b v
  | selected (b v previous : _) (q : Quorum1)
      (report : Acceptor → Option (Ballot × Value) → Prop)
      (responses : ∀ a, quorum1Member q a →
        ∃ prior, report a prior ∧ s.oneB a b prior)
      (chosen : ∃ a, quorum1Member q a ∧
        report a (some (previous, v)) ∧
        s.oneB a b (some (previous, v)))
      (greatest : ∀ a previous' v', quorum1Member q a →
        report a (some (previous', v')) → previous' ≤ previous)
      (previousBelow : previous < b)
      (parent : ProposalCertificate quorum1Member s previous v) :
      ProposalCertificate quorum1Member s b v

/-- The inductive protocol and history facts used by the safety proofs. -/
structure Invariants
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s : State Acceptor Value) : Prop where
  proposalUnique : ProposalUnique s
  voteHasProposal : VoteHasProposal s
  maxBalCoversOneB : MaxBalCoversOneB s
  acceptedCoversVotes : AcceptedCoversVotes s
  acceptedHasVote : AcceptedHasVote s
  acceptedBelowMaxBal : AcceptedBelowMaxBal s
  oneBHasVote : OneBHasVote s
  oneBPreviousBelow : OneBPreviousBelow s
  oneBCoversLowerVotes : OneBCoversLowerVotes s
  proposalCertified : ∀ b v, s.twoA b v →
    ProposalCertificate quorum1Member s b v

def OneVotePerAcceptorPerBallot (s : State Acceptor Value) : Prop :=
  ∀ a b v₁ v₂, s.twoB a b v₁ → s.twoB a b v₂ → v₁ = v₂

def OneValueAgreedPerBallot
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Value) : Prop :=
  ∀ b v₁ v₂,
    Agreed quorum2Member s v₁ b →
    Agreed quorum2Member s v₂ b →
    v₁ = v₂

theorem init_proposalUnique (h : Init s) : ProposalUnique s := by
  intro b v₁ v₂ h₁
  exact False.elim (h.2.2.2.2.1 b v₁ h₁)

theorem init_voteHasProposal (h : Init s) : VoteHasProposal s := by
  intro a b v hv
  exact False.elim (h.2.2.2.2.2 a b v hv)

theorem proposalUnique_preserved
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s s' : State Acceptor Value)
    (hinv : ProposalUnique s)
    (step : Step quorum1Member s s') :
    ProposalUnique s' := by
  cases step with
  | phase1a b action =>
      rcases action with rfl
      exact hinv
  | phase1b a b action =>
      rcases action with ⟨_, _, rfl⟩
      exact hinv
  | phase2a b v q action =>
      rcases action with ⟨fresh, _, _, rfl⟩
      intro b' v₁ v₂ h₁ h₂
      rcases h₁ with h₁ | ⟨rfl, rfl⟩
      · rcases h₂ with h₂ | ⟨hb, rfl⟩
        · exact hinv b' v₁ v₂ h₁ h₂
        · subst hb
          exact False.elim (fresh v₁ h₁)
      · rcases h₂ with h₂ | ⟨_, rfl⟩
        · exact False.elim (fresh v₂ h₂)
        · rfl
  | phase2b a b v action =>
      rcases action with ⟨_, _, rfl⟩
      exact hinv

theorem voteHasProposal_preserved
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s s' : State Acceptor Value)
    (hinv : VoteHasProposal s)
    (step : Step quorum1Member s s') :
    VoteHasProposal s' := by
  cases step with
  | phase1a b action =>
      rcases action with rfl
      exact hinv
  | phase1b a b action =>
      rcases action with ⟨_, _, rfl⟩
      exact hinv
  | phase2a b v q action =>
      rcases action with ⟨_, _, _, rfl⟩
      intro a b v hv
      exact Or.inl (hinv a b v hv)
  | phase2b a b v action =>
      rcases action with ⟨proposal, _, rfl⟩
      intro a' b' v' hv
      rcases hv with hv | ⟨rfl, rfl, rfl⟩
      · exact hinv a' b' v' hv
      · exact proposal

omit [DecidableEq Acceptor] in
theorem init_invariants
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s : State Acceptor Value) (h : Init s) :
    Invariants quorum1Member s where
  proposalUnique := init_proposalUnique h
  voteHasProposal := init_voteHasProposal h
  maxBalCoversOneB := by
    intro a b prior hb
    exact False.elim (h.2.2.2.1 a b prior hb)
  acceptedCoversVotes := by
    intro a b v hv
    exact False.elim (h.2.2.2.2.2 a b v hv)
  acceptedHasVote := by
    intro a b v ha
    have impossible : (none : Option (Ballot × Value)) = some (b, v) :=
      (h.2.1 a).symm.trans ha
    contradiction
  acceptedBelowMaxBal := by
    intro a b v ha
    have impossible : (none : Option (Ballot × Value)) = some (b, v) :=
      (h.2.1 a).symm.trans ha
    contradiction
  oneBHasVote := by
    intro a b previous v hb
    exact False.elim (h.2.2.2.1 a b _ hb)
  oneBPreviousBelow := by
    intro a b previous v hb
    exact False.elim (h.2.2.2.1 a b _ hb)
  oneBCoversLowerVotes := by
    intro a b prior voted value hb
    exact False.elim (h.2.2.2.1 a b prior hb)
  proposalCertified := by
    intro b v hp
    exact False.elim (h.2.2.2.2.1 b v hp)

omit [DecidableEq Acceptor] in
private theorem certificate_mono
    (quorum1Member : Quorum1 → Acceptor → Prop)
    {s t : State Acceptor Value}
    (honeB : ∀ a b prior, s.oneB a b prior → t.oneB a b prior)
    {b v} (certificate : ProposalCertificate quorum1Member s b v) :
    ProposalCertificate quorum1Member t b v := by
  induction certificate with
  | noPrevious b v q responses =>
      exact .noPrevious b v q (fun a ha => honeB a b none (responses a ha))
  | selected b v previous q report responses chosen greatest below parent ih =>
      exact .selected b v previous q report
        (fun a ha =>
          let ⟨prior, frozen, response⟩ := responses a ha
          ⟨prior, frozen, honeB a b prior response⟩)
        (let ⟨a, member, frozen, response⟩ := chosen
         ⟨a, member, frozen, honeB a b _ response⟩)
        greatest below ih

theorem invariants_preserved
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s s' : State Acceptor Value)
    (inv : Invariants quorum1Member s)
    (step : Step quorum1Member s s') :
    Invariants quorum1Member s' := by
  cases step with
  | phase1a b action =>
      rcases action with rfl
      refine { inv with proposalCertified := ?_ }
      intro ballot value hp
      exact certificate_mono quorum1Member
        (s := s)
        (t := { s with oneA := fun b' => s.oneA b' ∨ b' = b })
        (fun _ _ _ h => h) (inv.proposalCertified ballot value hp)
  | phase1b actor newBallot action =>
      rcases action with ⟨request, higher, rfl⟩
      let t : State Acceptor Value :=
        { s with
          maxBal := update s.maxBal actor (some newBallot)
          oneB := fun a' b' prior =>
            s.oneB a' b' prior ∨
              (a' = actor ∧ b' = newBallot ∧ prior = s.accepted actor) }
      have oldToNew : ∀ x ballot prior, s.oneB x ballot prior →
          t.oneB x ballot prior := fun _ _ _ h => Or.inl h
      have accepted_lt :
          ∀ previous value, s.accepted actor = some (previous, value) →
            previous < newBallot := by
        intro previous value haccepted
        obtain ⟨current, hcurrent, hpc⟩ :=
          inv.acceptedBelowMaxBal actor previous value haccepted
        have hc := higher current hcurrent
        exact Int.lt_of_le_of_lt hpc hc
      refine {
        proposalUnique := inv.proposalUnique
        voteHasProposal := inv.voteHasProposal
        maxBalCoversOneB := ?_
        acceptedCoversVotes := inv.acceptedCoversVotes
        acceptedHasVote := inv.acceptedHasVote
        acceptedBelowMaxBal := ?_
        oneBHasVote := ?_
        oneBPreviousBelow := ?_
        oneBCoversLowerVotes := ?_
        proposalCertified := ?_ }
      · intro x ballot prior hb
        rcases hb with hb | ⟨rfl, rfl, rfl⟩
        · obtain ⟨current, hc, hle⟩ :=
            inv.maxBalCoversOneB x ballot prior hb
          by_cases hxa : x = actor
          · subst x
            have hlt := higher current hc
            exact ⟨newBallot, by simp [update],
              Int.le_trans hle (Int.le_of_lt hlt)⟩
          · exact ⟨current, by simpa [update, hxa] using hc, hle⟩
        · exact ⟨ballot, by simp [update],
            Int.le_refl ballot⟩
      · intro x previous value haccepted
        obtain ⟨current, hc, hle⟩ :=
          inv.acceptedBelowMaxBal x previous value haccepted
        by_cases hxa : x = actor
        · subst x
          have hlt := higher current hc
          exact ⟨newBallot, by simp [update],
            Int.le_trans hle (Int.le_of_lt hlt)⟩
        · exact ⟨current, by simpa [update, hxa] using hc, hle⟩
      · intro x ballot previous value hb
        rcases hb with hb | ⟨rfl, rfl, hp⟩
        · exact inv.oneBHasVote x ballot previous value hb
        · exact inv.acceptedHasVote x previous value hp.symm
      · intro x ballot previous value hb
        rcases hb with hb | ⟨rfl, rfl, hp⟩
        · exact inv.oneBPreviousBelow x ballot previous value hb
        · exact accepted_lt previous value hp.symm
      · intro x ballot prior voted value hb hv hlt
        rcases hb with hb | ⟨rfl, rfl, rfl⟩
        · exact inv.oneBCoversLowerVotes x ballot prior voted value hb hv hlt
        · obtain ⟨previous, previousValue, haccepted, hle⟩ :=
            inv.acceptedCoversVotes x voted value hv
          exact ⟨previous, previousValue, haccepted, hle⟩
      · intro ballot value hp
        exact certificate_mono quorum1Member oldToNew
          (s := s)
          (inv.proposalCertified ballot value hp)
  | phase2a newBallot newValue q action =>
      rcases action with ⟨fresh, responses, safeChoice, rfl⟩
      refine {
        proposalUnique := ?_
        voteHasProposal := ?_
        maxBalCoversOneB := inv.maxBalCoversOneB
        acceptedCoversVotes := inv.acceptedCoversVotes
        acceptedHasVote := inv.acceptedHasVote
        acceptedBelowMaxBal := inv.acceptedBelowMaxBal
        oneBHasVote := inv.oneBHasVote
        oneBPreviousBelow := inv.oneBPreviousBelow
        oneBCoversLowerVotes := inv.oneBCoversLowerVotes
        proposalCertified := ?_ }
      · intro b' v₁ v₂ h₁ h₂
        rcases h₁ with h₁ | ⟨rfl, rfl⟩
        · rcases h₂ with h₂ | ⟨hb, rfl⟩
          · exact inv.proposalUnique b' v₁ v₂ h₁ h₂
          · subst hb
            exact False.elim (fresh v₁ h₁)
        · rcases h₂ with h₂ | ⟨_, rfl⟩
          · exact False.elim (fresh v₂ h₂)
          · rfl
      · intro x ballot value hv
        exact Or.inl (inv.voteHasProposal x ballot value hv)
      · intro ballot value hp
        rcases hp with hp | ⟨rfl, rfl⟩
        · exact certificate_mono quorum1Member
            (s := s)
            (t := { s with
              twoA := fun b' v' =>
                s.twoA b' v' ∨ (b' = newBallot ∧ v' = newValue) })
            (fun _ _ _ h => h)
            (inv.proposalCertified ballot value hp)
        · rcases safeChoice with noPrevious | selected
          · apply ProposalCertificate.noPrevious ballot value q
            intro x hx
            obtain ⟨prior, response⟩ := responses x hx
            cases prior with
            | none => exact response
            | some pair =>
                exact False.elim (noPrevious x pair hx response)
          · obtain ⟨x, previous, hx, response, greatest⟩ := selected
            have vote :=
              inv.oneBHasVote x ballot previous value response
            have proposal :=
              inv.voteHasProposal x previous value vote
            let report :
                Acceptor → Option (Ballot × Value) → Prop :=
              fun acceptor prior => s.oneB acceptor ballot prior
            have report_response :
                ∀ acceptor, quorum1Member q acceptor →
                  ∃ prior, report acceptor prior ∧
                    s.oneB acceptor ballot prior := by
              intro acceptor member
              obtain ⟨prior, hp⟩ := responses acceptor member
              exact ⟨prior, hp, hp⟩
            have chosen_report :
                report x (some (previous, value)) := by
              exact response
            exact ProposalCertificate.selected ballot value previous q report
              report_response ⟨x, hx, chosen_report, response⟩
              (by
                intro acceptor p value member reported
                exact greatest acceptor p value member reported)
              (inv.oneBPreviousBelow x ballot previous value response)
              (certificate_mono quorum1Member
                (s := s)
                (t := { s with
                  twoA := fun b' v' =>
                    s.twoA b' v' ∨ (b' = ballot ∧ v' = value) })
                (fun _ _ _ h => h)
                (inv.proposalCertified previous value proposal))
  | phase2b actor newBallot newValue action =>
      rcases action with ⟨proposal, notBelowPromise, rfl⟩
      let t : State Acceptor Value :=
        { s with
          maxBal := update s.maxBal actor (some newBallot)
          accepted := update s.accepted actor (some (newBallot, newValue))
          twoB := fun a' b' v' =>
            s.twoB a' b' v' ∨
              (a' = actor ∧ b' = newBallot ∧ v' = newValue) }
      refine {
        proposalUnique := inv.proposalUnique
        voteHasProposal := ?_
        maxBalCoversOneB := ?_
        acceptedCoversVotes := ?_
        acceptedHasVote := ?_
        acceptedBelowMaxBal := ?_
        oneBHasVote := ?_
        oneBPreviousBelow := inv.oneBPreviousBelow
        oneBCoversLowerVotes := ?_
        proposalCertified := ?_ }
      · intro x ballot value hv
        rcases hv with hv | ⟨rfl, rfl, rfl⟩
        · exact inv.voteHasProposal x ballot value hv
        · exact proposal
      · intro x ballot prior response
        obtain ⟨current, hc, hle⟩ :=
          inv.maxBalCoversOneB x ballot prior response
        by_cases hxa : x = actor
        · subst x
          have hcb := notBelowPromise current hc
          exact ⟨newBallot, by simp [update],
            Int.le_trans hle hcb⟩
        · exact ⟨current, by simpa [update, hxa] using hc, hle⟩
      · intro x voted value hv
        rcases hv with hv | ⟨rfl, rfl, rfl⟩
        · obtain ⟨current, currentValue, haccepted, hle⟩ :=
            inv.acceptedCoversVotes x voted value hv
          by_cases hxa : x = actor
          · subst x
            obtain ⟨promised, hpromised, hcp⟩ :=
              inv.acceptedBelowMaxBal actor current currentValue haccepted
            have hpb := notBelowPromise promised hpromised
            exact ⟨newBallot, newValue, by simp [update],
              Int.le_trans hle (Int.le_trans hcp hpb)⟩
          · exact ⟨current, currentValue,
              by simpa [update, hxa] using haccepted, hle⟩
        · exact ⟨voted, value, by simp [update],
            Int.le_refl voted⟩
      · intro x voted value haccepted
        by_cases hxa : x = actor
        · subst x
          have pairEq : (newBallot, newValue) = (voted, value) := by
            simpa [update] using haccepted
          cases pairEq
          exact Or.inr ⟨rfl, rfl, rfl⟩
        · have hold : s.accepted x = some (voted, value) := by
            simpa [update, hxa] using haccepted
          exact Or.inl (inv.acceptedHasVote x voted value hold)
      · intro x voted value haccepted
        by_cases hxa : x = actor
        · subst x
          have pairEq : (newBallot, newValue) = (voted, value) := by
            simpa [update] using haccepted
          cases pairEq
          exact ⟨newBallot, by simp [update],
            Int.le_refl newBallot⟩
        · obtain ⟨current, hc, hle⟩ :=
            inv.acceptedBelowMaxBal x voted value
              (by simpa [update, hxa] using haccepted)
          exact ⟨current, by simpa [update, hxa] using hc, hle⟩
      · intro x ballot previous value response
        exact Or.inl (inv.oneBHasVote x ballot previous value response)
      · intro x promise prior voted value response hv hlt
        rcases hv with hv | ⟨rfl, rfl, rfl⟩
        · exact inv.oneBCoversLowerVotes x promise prior voted value
            response hv hlt
        · obtain ⟨current, hc, hle⟩ :=
            inv.maxBalCoversOneB x promise prior response
          have hcb := notBelowPromise current hc
          exact False.elim
            (Int.not_lt_of_ge (Int.le_trans hle hcb) hlt)
      · intro ballot value hp
        exact certificate_mono quorum1Member
          (s := s)
          (t := { s with
            maxBal := update s.maxBal actor (some newBallot)
            accepted := update s.accepted actor (some (newBallot, newValue))
            twoB := fun a' b' v' =>
              s.twoB a' b' v' ∨
                (a' = actor ∧ b' = newBallot ∧ v' = newValue) })
          (fun _ _ _ h => h) (inv.proposalCertified ballot value hp)

theorem reachable_invariants
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (s : State Acceptor Value)
    (reachable : Reachable quorum1Member s) :
    Invariants quorum1Member s := by
  induction reachable with
  | init h => exact init_invariants quorum1Member _ h
  | step reachable step ih =>
      exact invariants_preserved quorum1Member _ _ ih step

omit [DecidableEq Acceptor] in
private theorem certificate_safe
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (intersects : ∀ q₁ q₂, ∃ a,
      quorum1Member q₁ a ∧ quorum2Member q₂ a)
    (inv : Invariants quorum1Member s)
    {higher : Ballot} {value : Value}
    (certificate : ProposalCertificate quorum1Member s higher value) :
    ∀ {lower lowerValue},
      Agreed quorum2Member s lowerValue lower →
      lower < higher →
      lowerValue = value := by
  induction certificate with
  | noPrevious higher value q responses =>
      intro lower lowerValue agreed below
      obtain ⟨q₂, votes⟩ := agreed
      obtain ⟨a, hq₁, hq₂⟩ := intersects q q₂
      obtain ⟨previous, previousValue, impossible, _⟩ :=
        inv.oneBCoversLowerVotes a higher none lower lowerValue
          (responses a hq₁) (votes a hq₂) below
      contradiction
  | selected higher value previous q report responses chosen greatest
      previousBelow parent ih =>
      intro lower lowerValue hagreed below
      have agreedCopy := hagreed
      obtain ⟨q₂, votes⟩ := hagreed
      obtain ⟨a, hq₁, hq₂⟩ := intersects q q₂
      obtain ⟨prior, frozen, response⟩ := responses a hq₁
      obtain ⟨reported, reportedValue, hprior, lowerLe⟩ :=
        inv.oneBCoversLowerVotes a higher prior lower lowerValue
          response (votes a hq₂) below
      have reportedFrozen : report a (some (reported, reportedValue)) := by
        simpa [hprior] using frozen
      have reportedLe :=
        greatest a reported reportedValue hq₁ reportedFrozen
      have lowerLePrevious := Int.le_trans lowerLe reportedLe
      by_cases equal : lower = previous
      · subst previous
        obtain ⟨selectedAcceptor, _, _, selectedResponse⟩ := chosen
        exact inv.proposalUnique lower lowerValue value
          (inv.voteHasProposal a lower lowerValue (votes a hq₂))
          (inv.voteHasProposal selectedAcceptor lower value
            (inv.oneBHasVote selectedAcceptor higher lower value
              selectedResponse))
      · rcases Int.lt_or_eq_of_le lowerLePrevious with lowerLt | rfl
        · exact ih agreedCopy lowerLt
        · contradiction

omit [DecidableEq Acceptor] in
theorem safeValue
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (intersects : ∀ q₁ q₂, ∃ a,
      quorum1Member q₁ a ∧ quorum2Member q₂ a)
    (s : State Acceptor Value)
    (inv : Invariants quorum1Member s) :
    SafeValue quorum2Member s := by
  intro value ballot agreed futureValue futureBallot later proposal
  exact certificate_safe quorum1Member quorum2Member intersects inv
    (inv.proposalCertified futureBallot futureValue proposal) agreed later

theorem reachable_safeValue
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (intersects : ∀ q₁ q₂, ∃ a,
      quorum1Member q₁ a ∧ quorum2Member q₂ a)
    (s : State Acceptor Value)
    (reachable : Reachable quorum1Member s) :
    SafeValue quorum2Member s :=
  safeValue quorum1Member quorum2Member intersects s
    (reachable_invariants quorum1Member s reachable)

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
    (intersects : ∀ q₁ q₂, ∃ a,
      quorum1Member q₁ a ∧ quorum2Member q₂ a)
    (hunique : ProposalUnique s)
    (hproposed : VoteHasProposal s) :
    OneValueAgreedPerBallot quorum2Member s := by
  intro b v₁ v₂ ⟨q₂₁, hagreed₁⟩ ⟨q₂₂, hagreed₂⟩
  obtain ⟨q₁⟩ := (inferInstance : Nonempty Quorum1)
  obtain ⟨a₁, _, ha₁⟩ := intersects q₁ q₂₁
  obtain ⟨a₂, _, ha₂⟩ := intersects q₁ q₂₂
  exact hunique b v₁ v₂
    (hproposed a₁ b v₁ (hagreed₁ a₁ ha₁))
    (hproposed a₂ b v₂ (hagreed₂ a₂ ha₂))

omit [DecidableEq Acceptor] in
theorem safety
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (s : State Acceptor Value)
    (hone : OneValueAgreedPerBallot quorum2Member s) :
    Safety quorum2Member s := by
  intro v₁ v₂ hdecided₁ hdecided₂
  exact hone 0 v₁ v₂ (hdecided₁ 0) (hdecided₂ 0)

theorem reachable_safety
    [Nonempty Quorum1]
    (quorum1Member : Quorum1 → Acceptor → Prop)
    (quorum2Member : Quorum2 → Acceptor → Prop)
    (intersects : ∀ q₁ q₂, ∃ a,
      quorum1Member q₁ a ∧ quorum2Member q₂ a)
    (s : State Acceptor Value)
    (reachable : Reachable quorum1Member s) :
    Safety quorum2Member s := by
  have inv := reachable_invariants quorum1Member s reachable
  apply safety quorum2Member s
  exact oneValueAgreedPerBallot quorum1Member quorum2Member intersects
    inv.proposalUnique inv.voteHasProposal

end FPaxos
