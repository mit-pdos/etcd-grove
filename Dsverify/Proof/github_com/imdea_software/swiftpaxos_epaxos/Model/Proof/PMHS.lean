/-
`InvPM` helpers for handler steps (`HS`): the outbox of a handler step, `paSent` and `pendPA`
when the step's sends and pending broadcast carry no PreAccept at an initial ballot.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HStep

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs HStepProof

namespace PMProof

section
variable {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event} {snd : Nat → List Msg}
  {pend : Option Bcast}

theorem HS.intended_eq (hH : HS S S' i σ' E snd pend) (fr to : Nat) :
    S'.intended fr to = if fr = i then intendedOf pend to else S.intended fr to := by
  unfold Sys.intended
  rw [hH.pending]
  by_cases hf : fr = i
  · subst hf; simp only [upd_same, if_true]; rfl
  · simp only [upd_other _ _ _ _ hf, hf, if_false]

/-- A handler step of an idle replica appends its direct sends to its outbox. -/
theorem HS.outbox_eq (hH : HS S S' i σ' E snd pend) (hidle : S.pending i = none) (fr to : Nat) :
    S'.outbox fr to = S.outbox fr to ++ (if fr = i then snd to else []) := by
  have h1 := hH.msgs fr to
  have hi := HS.intended_eq hH fr to
  unfold Sys.msgs at h1
  rw [hH.sent, hi] at h1
  by_cases hf : fr = i
  · subst hf
    have h0 : S.intended fr to = [] := by unfold Sys.intended; rw [hidle]
    simp only [if_true, h0, List.append_nil] at h1 ⊢
    have h2 : S.sent fr to ++ (S'.outbox fr to ++ intendedOf pend to) =
        S.sent fr to ++ ((S.outbox fr to ++ snd to) ++ intendedOf pend to) := by
      simpa only [List.append_assoc] using h1
    exact List.append_cancel_right (List.append_cancel_left h2)
  · simp only [hf, if_false, List.append_nil] at h1 ⊢
    have h2 : S.sent fr to ++ (S'.outbox fr to ++ S.intended fr to) =
        S.sent fr to ++ (S.outbox fr to ++ S.intended fr to) := by
      simpa only [List.append_assoc] using h1
    exact List.append_cancel_right (List.append_cancel_left h2)

/-- `paSent` after a handler step of an idle replica that sends no PreAccept at an initial
ballot, leaves no tracking broadcast pending, and keeps the leaders' bookkeepings at their initial
ballots (their `lastTriedBallot` and `preAcceptsSent`). -/
theorem ps_hs (hP : InvPM S) (hH : HS S S' i σ' E snd pend) (hidle : S.pending i = none)
    (hsnd : ∀ to m, m ∈ snd to → ∀ x, m.isPAat x (initBal x) = false)
    (hpend : ∀ b, pend = some b → b.trackPA = false)
    (hlb : ∀ x w' lb', (S'.rep x.q).inst x = some w' → w'.lb = some lb' →
      lb'.lastTriedBallot = initBal x → ∃ w lb, (S.rep x.q).inst x = some w ∧ w.lb = some lb ∧
        lb.lastTriedBallot = initBal x ∧ lb'.preAcceptsSent = lb.preAcceptsSent) :
    ∀ x w lb, x.q < nR → (S'.rep x.q).inst x = some w → w.lb = some lb →
      lb.lastTriedBallot = initBal x →
      lb.preAcceptsSent.toNat ≤ 2 * fR - 1 ∧
      (∀ b, S'.pending x.q = some b → b.x = x → b.trackPA = true →
        b.m.isPAat x (initBal x) = true ∧ b.sent = lb.preAcceptsSent.toNat ∧ b.need ≤ 2 * fR - 1) ∧
      (S'.paRcpt x).length ≤ lb.preAcceptsSent.toNat := by
  intro x w' lb' hq hw' hlb' hlt
  obtain ⟨w, lb, hw, hlb, e1, e2⟩ := hlb x w' lb' hw' hlb' hlt
  obtain ⟨h1, h2, h3⟩ := hP.paSent x w lb hq hw hlb e1
  refine ⟨by rw [e2]; exact h1, fun b hb hbx ht => ?_, ?_⟩
  · rw [hH.pending] at hb
    by_cases hr : x.q = i
    · rw [hr, upd_same] at hb; rw [hpend b hb] at ht; cases ht
    · rw [upd_other _ _ _ _ hr] at hb; rw [e2]; exact h2 b hb hbx ht
  · rw [e2]
    refine Nat.le_trans (List.Sublist.length_le ?_) h3
    unfold Sys.paRcpt
    refine filter_sub (fun a ha => ?_)
    obtain ⟨m, hm, hpa⟩ := List.any_eq_true.mp ha
    rw [hH.sent, HS.outbox_eq hH hidle] at hm
    refine List.any_eq_true.mpr ⟨m, ?_, hpa⟩
    simp only [List.mem_append] at hm ⊢
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · split at h
      · rw [hsnd a m h x] at hpa; cases hpa
      · cases h

/-- `pendPA` after a handler step of an idle replica whose new pending broadcast, if it carries
a PreAccept, is that instance's tracking broadcast. -/
theorem pendPA_hs (hP : InvPM S) (hH : HS S S' i σ' E snd pend)
    (hpend : ∀ b, pend = some b → ∀ x c, b.m.isPAat x c = true → b.trackPA = true ∧ b.x = x) :
    ∀ r b, S'.pending r = some b → ∀ x c, b.m.isPAat x c = true → b.trackPA = true ∧ b.x = x := by
  intro r b hb x c hc
  rw [hH.pending] at hb
  by_cases hr : r = i
  · subst hr; rw [upd_same] at hb; exact hpend b hb x c hc
  · rw [upd_other _ _ _ _ hr] at hb; exact hP.pendPA r b hb x c hc

end

end PMProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
