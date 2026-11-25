/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfSteps2.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: the local obligations (`StepI`) of the commit paths and phase 2: `leaderCommit`,
`handleAccept`, `handleCommit`, `handleAcceptReply`, the leader's merge `handlePreAcceptReply`
(the merger `a` and the replier, the replier excepting row `a`), the fast path
`handlePreAcceptOK` (the leader and the replier `X` of the creation deps), `handlePrepare`.
None records an instance (`ox = none`).
-/
module

public import Dsverify.Proof.gryff.PureA.IntfConf

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA
open Perennial.gryff.pureA.AW

variable {rc : RecG} {κ : Nat} {dg : DepG} {s s' : RState} {a : Fin 3} {o : List Out}

/-! ## Helpers -/

theorem copyI_strong {rc' : RecG} {κ' : Nat} {q i : w32} {cp : Copy} (hs : Strong cp.status)
    (hnp : cp.status ≠ St.PREACCEPTED)
    (hv : cp.cmds ≠ [] → SameRow q i cp.deps ∧ Wp2 rc' κ' q i cp.deps)
    (hc : ∀ lb, cp.lb = some lb → ¬ isCommitted cp.status → CandI rc' κ' q i lb.recoveryInst) :
    CopyI rc' κ' dg q i a cp where
  val h1 _ := ⟨⟨(hv h1).1, let ⟨w1, _, _, _, c1, _⟩ := (hv h1).2; ⟨w1, c1⟩, fun _ => (hv h1).2⟩,
    fun he => absurd he hnp⟩
  own0 _ _ _ he := absurd he hnp
  cand := hc

theorem copyI_withLb {rc' : RecG} {κ' : Nat} {q i : w32} {c : Copy} (h : CopyI rc' κ' dg q i a c)
    (L : LB) (hL : ¬ isCommitted c.status → CandI rc' κ' q i L.recoveryInst) :
    CopyI rc' κ' dg q i a { c with lb := some L } :=
  ⟨h.val, h.own0, fun lb hl hn => by cases hl; exact hL hn⟩

theorem copyI_lb {rc' : RecG} {κ' : Nat} {q i : w32} {c : Copy} {lb L : LB}
    (h : CopyI rc' κ' dg q i a c) (hl : c.lb = some lb) (e : L.recoveryInst = lb.recoveryInst) :
    CopyI rc' κ' dg q i a { c with lb := some L } :=
  copyI_withLb h L (fun hn => by rw [e]; exact h.cand lb hl hn)

/-- An old copy's facts under the new ghost (no record). -/
theorem cM {q i : w32} {c : Copy} (h : CopyI rc κ dg q i a c) :
    CopyI (addRec rc a κ none) (κ + 1) dg q i a c :=
  copyI_mono (addRec_ext rc a κ none) (Nat.le_succ _) (DgLe.refl dg) h

theorem wM {q i : w32} {D : Deps} (h : Wp2 rc κ q i D) : Wp2 (addRec rc a κ none) (κ + 1) q i D :=
  wp2_mono (addRec_ext rc a κ none) (Nat.le_succ _) h

theorem vM {q i : w32} {D : Deps} {w : Fin 3} {e : Option (Fin 3)} (h : Cov rc κ q i D w e) :
    Cov (addRec rc a κ none) (κ + 1) q i D w e :=
  cov_mono (addRec_ext rc a κ none) (Nat.le_succ _) h

theorem strong_acc : Strong St.ACCEPTED := Or.inl rfl
theorem strong_com : Strong St.COMMITTED := Or.inr (Or.inr (Or.inl rfl))
theorem ne_pre_acc : St.ACCEPTED ≠ St.PREACCEPTED := by decide
theorem ne_pre_com : St.COMMITTED ≠ St.PREACCEPTED := by decide
theorem com_isC : isCommitted St.COMMITTED := Or.inl rfl
theorem ne_none_pre : St.PREACCEPTED ≠ St.NONE := by decide
theorem ne_none_acc : St.ACCEPTED ≠ St.NONE := by decide

theorem crtB_crtOwn {t : RState} {q j : w32} (h : A1d.CrtB s t q j)
    (hb : q = s.id → sint.Z j < sint.Z (s.crt q)) : t.crt s.id = s.crt s.id := by
  rcases h with rfl | ⟨hge, rfl⟩
  · rfl
  · by_cases e : q = s.id
    · have := hb e
      simp only [sge, sle, decide_eq_true_eq] at hge
      omega
    · exact crt_setCrt_ne (Ne.symm e)

/-! ## The commit at the proposer -/

theorem li_leaderCommit {q i : w32} {c : Copy} {lb : LB}
    (hv : c.cmds ≠ [] → SameRow q i c.deps ∧ Wp2 (addRec rc a κ none) (κ + 1) q i c.deps)
    (h : leaderCommit s q i c lb = .ok (s', o)) : StepI rc κ dg s s' a o none := by
  obtain ⟨cp, e1, -, ecrt, h1, h2, -, -, hout⟩ := A1d.leaderCommit_shape h
  simp only [Copy.valA, Prod.mk.injEq] at h2
  obtain ⟨ec, -, ed, -⟩ := h2
  refine ⟨leaderCommit_conf h, by simp only [RState.crt, ecrt], fun _ _ h => (by cases h), ?_, ?_⟩
  · intro q' i' cp' hc; rw [e1] at hc
    refine cpI_setInst rfl ?_ q' i' cp' hc
    refine copyI_strong (by rw [h1]; exact strong_com) (by rw [h1]; exact ne_pre_com)
      (fun hn => ?_) (fun _ _ hn => absurd (by rw [h1]; exact com_isC) hn)
    rw [ec] at hn; rw [ed]; exact hv hn
  · intro d y hy; rw [hout d y (A1b.mem_sentR hy)]; exact hv

/-! ## handleAccept, handleCommit, handleAcceptReply -/

theorem li_accept {m : EAcceptM} (C : CtxI rc κ dg s a) (hm : MsgI rc κ dg a (.accept m))
    (hb : m.replica = s.id → sint.Z m.inst < sint.Z (s.crt m.replica))
    (h : stepAccept s m = .ok (s', o)) : StepI rc κ dg s s' a o none := by
  have hconf := stepAccept_conf h
  rcases A1d.stepAccept_shape h with ⟨-, -, -, rfl, rfl⟩ | ⟨t, ht, hx⟩
  · exact stepI_same
  have et := crtB_inst ht
  rcases hx with ⟨c, x, -, -, -, rfl, rfl, hx⟩ | ⟨cp, x, rfl, rfl, h1, -, -, h2, hold, hx⟩
  · exact ⟨hconf, crtB_crtOwn ht hb, fun _ _ h => (by cases h),
      fun q i cp hc => Or.inl (by rw [← et]; exact hc),
      fun d y hy => by rw [sentR_sendPeer hx hy]; trivial⟩
  · refine ⟨hconf, (by show t.crt s.id = s.crt s.id; exact crtB_crtOwn ht hb),
      fun _ _ h => (by cases h), cpI_setInst et ?_,
      fun d y hy => by rw [sentR_sendPeer hx hy]; trivial⟩
    simp only [Copy.valA, Prod.mk.injEq] at h2
    obtain ⟨ec, -, ed, -⟩ := h2
    refine copyI_strong (by rw [h1]; exact strong_acc) (by rw [h1]; exact ne_pre_acc) (fun hn => ?_) ?_
    · rw [ec] at hn; rw [ed]; exact ⟨(hm hn).1, wM (hm hn).2⟩
    · intro lb hl hn
      rcases hold with hn0 | ⟨c, hc, hnc, -, el⟩
      · rw [accept_lb_none h hn0 cp (by rw [setInst_inst, if_pos ⟨rfl, rfl⟩])] at hl; cases hl
      · rw [el] at hl
        exact (cM (C.copies _ _ _ hc)).cand lb hl hnc

theorem li_commit {m : ECommitM} (C : CtxI rc κ dg s a) (hm : MsgI rc κ dg a (.commit m))
    (hb : m.replica = s.id → sint.Z m.inst < sint.Z (s.crt m.replica))
    (h : stepCommit s m = .ok (s', o)) : StepI rc κ dg s s' a o none := by
  have hconf := stepCommit_conf h
  obtain ⟨rfl, t, ht, hx⟩ := A1d.stepCommit_shape h
  have et := crtB_inst ht
  rcases hx with ⟨-, -, -, rfl⟩ | ⟨cp, e1, -, ecrt, h1, h2, -⟩
  · exact ⟨hconf, crtB_crtOwn ht hb, fun _ _ h => (by cases h),
      fun q i cp hc => Or.inl (by rw [← et]; exact hc), fun _ _ h => (sentR_nil h).elim⟩
  refine ⟨hconf, (by rw [show s'.crt s.id = t.crt s.id by simp only [RState.crt, ecrt]];
                     exact crtB_crtOwn ht hb), fun _ _ h => (by cases h), fun q i cp' hc => ?_,
    fun _ _ h => (sentR_nil h).elim⟩
  rw [e1] at hc
  refine cpI_setInst et ?_ q i cp' hc
  simp only [Copy.valA, ECommitM.valA, Prod.mk.injEq] at h2
  obtain ⟨ec, -, ed, -⟩ := h2
  refine copyI_strong (by rw [h1]; exact strong_com) (by rw [h1]; exact ne_pre_com) (fun hn => ?_)
    (fun _ _ hn => absurd (by rw [h1]; exact com_isC) hn)
  rw [ec] at hn; rw [ed]; exact ⟨(hm hn).1, wM (hm hn).2⟩

theorem li_acceptReply {m : AcceptReplyM} (C : CtxI rc κ dg s a)
    (h : stepAcceptReply s m = .ok (s', o)) : StepI rc κ dg s s' a o none := by
  rcases A1d.stepAcceptReply_shape h with ⟨rfl, rfl⟩ | ⟨c, lb, hc, -, hl, hx⟩
  · exact stepI_same
  have hcw := cM (C.copies _ _ _ hc)
  rcases hx with ⟨rfl, lb', rfl, -, -, e, -⟩ | ⟨-, hs, lb'', hlc⟩
  · exact ⟨confLe_of_eq rfl, rfl, fun _ _ h => (by cases h),
      cpI_setInst rfl (copyI_lb hcw hl e), fun _ _ h => (sentR_nil h).elim⟩
  · refine li_leaderCommit (fun hn => ?_) hlc
    obtain ⟨⟨k1, -, k3⟩, -⟩ := hcw.val hn (by rw [hs]; exact ne_none_acc)
    exact ⟨k1, k3 (by rw [hs]; exact strong_acc)⟩

/-! ## handlePreAcceptReply (the merge) -/

theorem li_preAcceptReply {m : PreAcceptReplyM} (C : CtxI rc κ dg s a)
    (hm : MsgI rc κ dg a (.preAcceptReply m)) (h : stepPreAcceptReply s m = .ok (s', o)) :
    StepI rc κ dg s s' a o none := by
  obtain ⟨-, hc⟩ := SPA.stepPreAcceptReply_cases h
  rcases hc with ⟨rfl, rfl⟩ | ⟨c, lb, hc, hpre, -, hl, hx⟩
  · exact stepI_same
  have hcw := cM (C.copies _ _ _ hc)
  rcases hx with ⟨-, rfl, lb', rfl, LS⟩ | ⟨hok, c2, lb2, hx, M, LO⟩
  · exact ⟨confLe_of_eq rfl, rfl, fun _ _ h => (by cases h),
      cpI_setInst rfl (copyI_lb hcw hl LS.recoveryInst), fun _ _ h => (sentR_nil h).elim⟩
  have hnc : ¬ isCommitted c.status := by
    rw [hpre]; unfold isCommitted; decide
  have hcand : CandI (addRec rc a κ none) (κ + 1) m.replica m.inst lb2.recoveryInst := by
    rw [LO.recoveryInst]; exact hcw.cand lb hl hnc
  -- the merged value
  have hv : c2.cmds ≠ [] → SameRow m.replica m.inst c2.deps ∧
      Wp2 (addRec rc a κ none) (κ + 1) m.replica m.inst c2.deps ∧
      Cov (addRec rc a κ none) (κ + 1) m.replica m.inst c2.deps a none ∧ 3 ≤ c2.deps.length ∧
      DLe c.deps c2.deps := by
    intro hn
    rw [M.cmds] at hn
    obtain ⟨⟨hsr, -, -⟩, k⟩ := hcw.val hn (by rw [hpre]; exact ne_none_pre)
    obtain ⟨hcovA, hlen⟩ := k hpre
    obtain ⟨-, w, hw, hcovW⟩ := hm hok
    obtain ⟨hdle, hlen2, hcov⟩ := merge_facts (s := s) (seq1 := c.seq) (seq2 := m.seq)
      (deps2 := m.deps) hlen
    rw [M.deps]
    refine ⟨sameRow_dle hdle hsr, ⟨a, w, some a, hw.symm, cov_dle hdle hcovA, ?_, Or.inr rfl⟩,
      cov_dle hdle hcovA, by rw [hlen2]; exact hlen, hdle⟩
    refine cov_weaken (fun _ _ => by simp) (fun r hr => ?_) (vM hcovW)
    have hra : r ≠ a := fun e => hr (by rw [e])
    refine hcov r.val r.isLt (fun e => hra (rid32_inj ?_))
    rw [C.id] at e; exact e
  rcases hx with ⟨-, -, -, hlc⟩ | ⟨rfl, hbc⟩ | ⟨-, rfl, rfl⟩
  · exact li_leaderCommit (fun hn => ⟨(hv hn).1, (hv hn).2.1⟩) hlc
  · refine ⟨confLe_of_eq rfl, rfl, fun _ _ h => (by cases h), cpI_setInst rfl ?_, fun d y hy => ?_⟩
    · exact copyI_strong strong_acc ne_pre_acc (fun hn => ⟨(hv hn).1, (hv hn).2.1⟩)
        (fun lb' hl' _ => by cases hl'; exact hcand)
    · rw [sentR_bcast hbc hy]; intro hn; exact ⟨(hv hn).1, (hv hn).2.1⟩
  · refine ⟨confLe_of_eq rfl, rfl, fun _ _ h => (by cases h), cpI_setInst rfl ⟨?_, ?_, ?_⟩,
      fun _ _ h => (sentR_nil h).elim⟩
    · intro hn hst
      obtain ⟨k1, k2, k3, k4, -⟩ := hv hn
      exact ⟨⟨k1, ⟨a, k3⟩, fun _ => k2⟩, fun _ => ⟨k3, k4⟩⟩
    · intro hn hq hb0 hst
      have hn' : c.cmds ≠ [] := by rw [← M.cmds]; exact hn
      obtain ⟨D, hD, hle⟩ := hcw.own0 hn' hq (by rw [← M.ballot]; exact hb0) hpre
      exact ⟨D, hD, hle.trans (hv hn).2.2.2.2⟩
    · intro lb' hl' _; cases hl'; exact hcand

/-! ## handlePreAcceptOK (the fast path) -/

theorem li_preAcceptOK {m : PreAcceptOKM} (C : CtxI rc κ dg s a)
    (hm : MsgI rc κ dg a (.preAcceptOK m))
    (hB : ∀ cp, s.inst s.id m.inst = some cp → isInitialBallot cp.ballot = true → cp.ballot = 0)
    (h : stepPreAcceptOK s m = .ok (s', o)) : StepI rc κ dg s s' a o none := by
  obtain ⟨-, hc⟩ := SPA.stepPreAcceptOK_cases h
  rcases hc with ⟨rfl, rfl⟩ | ⟨c, lb, hc, hpre, hinit, hl, hx⟩
  · exact stepI_same
  obtain ⟨D, hD, X, hX, hcovX⟩ := hm
  have hb0 := hB c hc hinit
  have hid := C.id
  rw [hid] at hc hx
  have hcw := cM (C.copies _ _ _ hc)
  have hv : c.cmds ≠ [] → SameRow (rid32 a) m.inst c.deps ∧
      Wp2 (addRec rc a κ none) (κ + 1) (rid32 a) m.inst c.deps := fun hn => by
    obtain ⟨⟨hsr, -, -⟩, k⟩ := hcw.val hn (by rw [hpre]; exact ne_none_pre)
    obtain ⟨D', hD', hle⟩ := hcw.own0 hn rfl hb0 hpre
    rw [hD] at hD'; cases hD'
    exact ⟨hsr, a, X, none, hX.symm, (k hpre).1, cov_dle hle (vM hcovX), Or.inl rfl⟩
  have hnc : ¬ isCommitted c.status := by rw [hpre]; unfold isCommitted; decide
  rcases hx with ⟨-, hlc⟩ | ⟨rfl, hbc⟩ | ⟨-, rfl, rfl⟩
  · exact li_leaderCommit hv hlc
  · refine ⟨confLe_of_eq rfl, rfl, fun _ _ h => (by cases h), cpI_setInst rfl ?_, fun d y hy => ?_⟩
    · exact copyI_strong strong_acc ne_pre_acc hv (fun lb' hl' _ => by
        cases hl'; exact hcw.cand lb hl hnc)
    · rw [sentR_bcast hbc hy]; exact hv
  · exact ⟨confLe_of_eq rfl, rfl, fun _ _ h => (by cases h), cpI_setInst rfl (copyI_lb hcw hl rfl),
      fun _ _ h => (sentR_nil h).elim⟩

/-! ## handlePrepare -/

theorem li_prepare {m : PrepareM} (C : CtxI rc κ dg s a) (hb0 : m.ballot ≠ 0)
    (h : stepPrepare s m = .ok (s', o)) : StepI rc κ dg s s' a o none := by
  obtain ⟨-, cp', r, x, rfl, hx, rfl, -, er, ei, hc⟩ := A1b.stepPrepare_cases h
  have hmsg : (r.cmds ≠ [] → r.status ≠ St.NONE →
      ValI (addRec rc a κ none) (κ + 1) r.replica r.inst r.deps r.status) →
      ∀ d y, y ∈ A1b.sentR d [x] → MsgI (addRec rc a κ none) (κ + 1) dg d y := fun hr d y hy => by
    rw [sentR_sendPeer hx hy]; exact hr
  refine ⟨confLe_of_eq rfl, rfl, fun _ _ h => (by cases h), ?_⟩
  rcases hc with ⟨-, rfl, -, -, hst, -⟩ | ⟨c, hc, -, rfl, -, hst, hcm, -, hd, -⟩ |
      ⟨c, hc, -, rfl, -, -, hst, -, hcm, -, hd, -⟩
  · refine ⟨cpI_setInst rfl ⟨fun _ hn => absurd rfl hn, fun hn => absurd rfl hn,
      fun _ hl => by cases hl⟩, hmsg ?_⟩
    intro _ hn; exact absurd hst hn
  · have hcw := cM (C.copies _ _ _ hc)
    refine ⟨cpI_setInst rfl hcw, hmsg ?_⟩
    intro h1 h2; rw [hcm] at h1; rw [hst] at h2 ⊢; rw [hd, er, ei]
    exact (hcw.val h1 h2).1
  · have hcw := cM (C.copies _ _ _ hc)
    refine ⟨cpI_setInst rfl ⟨hcw.val, fun _ _ hb _ => absurd hb hb0, hcw.cand⟩, hmsg ?_⟩
    intro h1 h2; rw [hcm] at h1; rw [hst] at h2 ⊢; rw [hd, er, ei]
    exact (hcw.val h1 h2).1

end Perennial.gryff.pureA.AI
