/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfSteps4.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: `handlePrepareReply`'s obligations (the candidate updates `upd`, G22's commit, the
Accept of a candidate, the restart, the no-op), as unit AW's `lw_prepareReply`.
-/
module

public import Dsverify.Proof.gryff.PureA.IntfSteps3

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA
open Perennial.gryff.pureA.AW

variable {rc : RecG} {κ : Nat} {dg : DepG} {s s' : RState} {a : Fin 3} {o : List Out}

/-- A reply's value facts. -/
def RepI (rc : RecG) (κ : Nat) (m : PrepareReplyM) : Prop :=
  m.cmds ≠ [] → m.status ≠ St.NONE → ValI rc κ m.replica m.inst m.deps m.status

theorem candI_riOf {rc' : RecG} {κ' : Nat} {m : PrepareReplyM} (hs : m.status ≠ St.NONE)
    (hm : RepI rc' κ' m) (c : w64) (lr : Bool) :
    CandI rc' κ' m.replica m.inst (some (riOf m c lr)) := by
  intro r hr hc; cases hr; exact hm hc hs

theorem candI_upd {rc' : RecG} {κ' : Nat} {ri : Option RecoveryInstance} {m : PrepareReplyM}
    (h : CandI rc' κ' m.replica m.inst ri) (hm : RepI rc' κ' m) :
    CandI rc' κ' m.replica m.inst (upd ri m) := by
  have h1 : CandI rc' κ' m.replica m.inst (upd1 ri m) := by
    unfold upd1; split
    · rename_i hs; dsimp only; split
      · exact candI_riOf (by rw [hs]; decide) hm _ _
      · split
        · exact candI_riOf (by rw [hs]; decide) hm _ _
        · exact h
    · exact h
  unfold upd upd2
  split
  · rename_i hc
    have hs : m.status ≠ St.NONE := by
      rcases hc.1 with e | e <;> rw [e] <;> decide
    dsimp only
    split
    · exact candI_riOf hs hm _ _
    · rename_i r hr
      split
      · intro r' hr' hc'; cases hr'; exact h1 r hr hc'
      · split
        · exact candI_riOf hs hm _ _
        · intro r' hr' hc'; cases hr'; exact h1 r hr hc'
  · exact h1

theorem candI_setLr {rc' : RecG} {κ' : Nat} {q i : w32} {r : RecoveryInstance}
    (h : CandI rc' κ' q i (some r)) : CandI rc' κ' q i (some (setLr r)) :=
  fun r' hr' hc' => by cases hr'; exact h r rfl hc'

/-- `prMain` (the reply is OK, at the copy's ballot, not committed). -/
theorem li_prMain {m : PrepareReplyM} {c : Copy} {lb0 : LB} (C : CtxI rc κ dg s a)
    (hc : s.inst m.replica m.inst = some c) (hl : c.lb = some lb0)
    (hst : ¬ (c.status = St.COMMITTED ∨ c.status = St.EXECUTED))
    (hm : RepI (addRec rc a κ none) (κ + 1) m)
    (hb0 : c.ballot ≠ 0) (h : prMain s m c lb0 = .ok (s', o)) :
    ∃ ox, StepI rc κ dg s s' a o ox := by
  have hcw := cM (C.copies _ _ _ hc)
  have hcand := candI_upd (hcw.cand lb0 hl (not_committed_of hst)) hm
  have same : ∀ L : LB, (¬ isCommitted c.status → CandI (addRec rc a κ none) (κ + 1) m.replica m.inst
      L.recoveryInst) →
      StepI rc κ dg s (s.setInst m.replica m.inst { c with lb := some L }) a [] none := fun L hL =>
    ⟨confLe_of_eq rfl, rfl, fun _ _ h => (by cases h), cpI_setInst rfl (copyI_withLb hcw L hL),
      fun _ _ h => (sentR_nil h).elim⟩
  unfold prMain at h
  dsimp only at h
  split at h
  · split at h
    · rename_i r hr
      cases h
      refine ⟨none, same _ (fun _ => ?_)⟩
      show CandI _ _ m.replica m.inst (some (setLr r)); rw [hr] at hcand; exact candI_setLr hcand
    · cases h
  split at h
  · cases h
    exact ⟨none, same _ (fun _ => hcand)⟩
  unfold prDecide at h
  split at h
  · rename_i ir hir
    have hir' : upd lb0.recoveryInst m = some ir := hir
    rw [hir'] at hcand
    dsimp only at h
    split at h
    · rename_i hcond
      split at h
      · rename_i outs hbc
        cases h
        have hv : ir.cmds ≠ [] → SameRow m.replica m.inst ir.deps ∧
            Wp2 (addRec rc a κ none) (κ + 1) m.replica m.inst ir.deps := fun hn => by
          obtain ⟨k1, -, k3⟩ := hcand ir rfl hn
          refine ⟨k1, k3 ?_⟩
          rcases hcond with e | ⟨-, -, e⟩
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
        refine ⟨none, confLe_of_eq rfl, rfl, fun _ _ h => (by cases h), cpI_setInst rfl
          (copyI_strong strong_acc ne_pre_acc hv (fun lb hl' _ => by
            cases hl'; show CandI _ _ m.replica m.inst (upd lb0.recoveryInst m); rw [hir']; exact hcand)),
          fun d y hy => ?_⟩
        rw [sentR_bcast hbc hy]; exact hv
      · cases h
    · split at h
      · cases h
      · refine ⟨_, li_restart (D := ir.deps) C (fun hn => ?_) hb0 h⟩
        obtain ⟨-, ⟨w, hw⟩, -⟩ := hcand ir rfl hn
        exact ⟨w, hw⟩
  · rename_i hir
    dsimp only at h
    split at h
    · rename_i outs hbc
      cases h
      refine ⟨none, confLe_of_eq rfl, rfl, fun _ _ h => (by cases h), cpI_setInst rfl
        ⟨fun hn _ => absurd rfl hn, fun hn => absurd rfl hn, fun lb hl' _ => ?_⟩, fun d y hy => ?_⟩
      · cases hl'; show CandI _ _ m.replica m.inst (upd lb0.recoveryInst m)
        intro r hr; rw [hr] at hir; cases hir
      · rw [sentR_bcast hbc hy]; intro hn; exact absurd rfl hn
    · cases h

theorem li_prepareReply {m : PrepareReplyM} (C : CtxI rc κ dg s a)
    (hm : MsgI rc κ dg a (.prepareReply m)) (hb0 : m.ok ≠ FALSE → m.ballot ≠ 0)
    (h : stepPrepareReply s m = .ok (s', o)) : ∃ ox, StepI rc κ dg s s' a o ox := by
  have hmM : RepI (addRec rc a κ none) (κ + 1) m := fun h1 h2 =>
    valI_mono (addRec_ext rc a κ none) (Nat.le_succ _) (hm h1 h2)
  rcases stepPrepareReply_cases h with ⟨rfl, rfl⟩ | ⟨c, lb0, hc, hl, rfl, rfl⟩ |
      ⟨c, lb0, hc, hl, -, -, -, -, hms, rfl, hbc⟩ | ⟨c, lb0, hc, hl, -, hst, hok, hb, -, -, -, hpm⟩
  · exact ⟨none, stepI_same⟩
  · exact ⟨none, confLe_of_eq rfl, rfl, fun _ _ h => (by cases h),
      cpI_setInst rfl (copyI_lb (cM (C.copies _ _ _ hc)) hl rfl), fun _ _ h => (sentR_nil h).elim⟩
  · have hv : m.cmds ≠ [] → SameRow m.replica m.inst m.deps ∧
        Wp2 (addRec rc a κ none) (κ + 1) m.replica m.inst m.deps := fun hn => by
      have hs : Strong m.status := by
        rcases hms with e | e
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inr (Or.inr (Or.inr e))
      obtain ⟨k1, -, k3⟩ := hmM hn (fun e => by rw [e] at hs; exact absurd hs (by unfold Strong; decide))
      exact ⟨k1, k3 hs⟩
    exact ⟨none, confLe_of_eq rfl, rfl, fun _ _ h => (by cases h),
      cpI_setInst rfl (copyI_strong strong_com ne_pre_com hv
        (fun _ _ hn => absurd com_isC hn)),
      fun d y hy => by rw [sentR_bcast hbc hy]; exact hv⟩
  · exact li_prMain C hc hl hst hmM (by rw [← hb]; exact hb0 hok) hpm

end Perennial.gryff.pureA.AI
