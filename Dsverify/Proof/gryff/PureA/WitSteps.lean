/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/WitSteps.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AW, internal: the local obligations (`LocalW`) of each EPaxos handler for the witness
invariant (`WitDefs.lean`), over the stepping replica's state `s` (`Ctx`: its id, its copies'
`CopyW`, the ghost's stores at most its store).
-/
module

public import Dsverify.Proof.gryff.PureA.WitShapes

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AW

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

/-- What a step of replica `a` from state `s` may use. -/
structure Ctx (S : CSG) (s : RState) (a : Fin 3) : Prop where
  id : s.id = rid32 a
  copies : ∀ q i cp, s.inst q i = some cp → CopyW S q i a cp
  store : ∀ q i f, S q i = some f → TLe (f a) s.tag

variable {S : CSG} {s s' : RState} {a : Fin 3} {o : List Out}

/-! ## Helpers -/

theorem S_fun {q i : w32} {f g : Fin 3 → model.Tag} (h1 : S q i = some f) (h2 : S q i = some g) :
    f = g := by rw [h1] at h2; cases h2; rfl

theorem copyW_withLb {q i : w32} {c : Copy} (h : CopyW S q i a c) (L : LB)
    (hL : ¬ isCommitted c.status → CandOK S q i L.recoveryInst) :
    CopyW S q i a { c with lb := some L } :=
  ⟨h.val, fun lb hl hn => by cases hl; exact hL hn⟩

theorem copyW_lb {q i : w32} {c : Copy} {lb L : LB} (h : CopyW S q i a c) (hl : c.lb = some lb)
    (e : L.recoveryInst = lb.recoveryInst) : CopyW S q i a { c with lb := some L } :=
  copyW_withLb h L (fun hn => by rw [e]; exact h.cand lb hl hn)

theorem copyW_ballot {q i : w32} {c : Copy} (h : CopyW S q i a c) (b : w32) :
    CopyW S q i a { c with ballot := b } := ⟨h.val, h.cand⟩

theorem sentR_send2 {d d' : Fin 3} {msg y : Msg} (h : y ∈ A1b.sentR d' [.send d msg]) :
    y = msg ∧ d = d' := by
  rw [A1b.sentR_single] at h; split at h
  · exact ⟨by simpa using h, by assumption⟩
  · cases h

theorem sentR_send {d d' : Fin 3} {msg y : Msg} (h : y ∈ A1b.sentR d' [.send d msg]) : y = msg :=
  (sentR_send2 h).1

theorem sentR_sendPeer {t : RState} {q : w32} {msg y : Msg} {x : Out} {d' : Fin 3}
    (hx : sendPeer t q msg = some x) (h : y ∈ A1b.sentR d' [x]) : y = msg := by
  obtain ⟨d, rfl⟩ := sendPeer_send hx
  exact sentR_send h

theorem sentR_bcast {t : RState} {msg y : Msg} {o : List Out} {d : Fin 3} (hb : bcast t msg = some o)
    (h : y ∈ A1b.sentR d o) : y = msg := (A1b.bcast_sent' hb d y h).1

theorem sentR_nil {d : Fin 3} {y : Msg} (h : y ∈ A1b.sentR d []) : False := by
  simp [A1b.sentR] at h

theorem localW_same {s : RState} : LocalW S s s a [] :=
  ⟨fun _ _ _ h => Or.inl h, fun _ _ h => (sentR_nil h).elim⟩

theorem crtB_inst {t : RState} {q j : w32} (h : A1d.CrtB s t q j) : t.inst = s.inst := by
  rcases h with rfl | ⟨-, rfl⟩ <;> rfl

theorem bump_facts {s1 : RState} {m : PreAcceptM} (h : SPA.Bump s m s1) :
    s1.inst = s.inst ∧ s1.tag = s.tag ∧ s1.id = s.id := by
  rcases h with rfl | ⟨-, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩

theorem not_committed_of {st : w8} (h : ¬ (st = St.COMMITTED ∨ st = St.EXECUTED)) :
    ¬ isCommitted st := h

/-! ## The proposer's commit -/

/-- `leaderCommit` of a value with two witnesses. -/
theorem lw_leaderCommit {q i : w32} {c : Copy} {lb : LB} (C : Ctx S s a)
    (hv : c.cmds ≠ [] → ∃ f, S q i = some f ∧ Wit2 f c.base)
    (h : leaderCommit s q i c lb = .ok (s', o)) : LocalW S s s' a o := by
  obtain ⟨cp, e1, -, -, h1, h2, -, -, hout⟩ := A1d.leaderCommit_shape h
  simp only [Copy.valA, Prod.mk.injEq] at h2
  obtain ⟨ec, -, -, eb⟩ := h2
  refine ⟨fun q' i' cp' hc => ?_, fun d y hy => ?_⟩
  · rw [e1] at hc
    refine cp_setInst rfl ?_ q' i' cp' hc
    refine copyW_strong (by rw [h1]; exact st_dec.2.2.2.2.2.2.2.2.2.1) (fun hn => ?_)
      (fun _ _ hn => absurd (by rw [h1]; exact st_dec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) hn)
    rw [ec] at hn; rw [eb]; exact hv hn
  · rw [hout d y (A1b.mem_sentR hy)]
    exact hv

/-! ## handleAccept, handleCommit, handleAcceptReply -/

theorem lw_accept {m : EAcceptM} (C : Ctx S s a) (hm : WMsg S a (.accept m))
    (h : stepAccept s m = .ok (s', o)) : LocalW S s s' a o := by
  rcases A1d.stepAccept_shape h with ⟨-, -, -, rfl, rfl⟩ | ⟨t, ht, hx⟩
  · exact localW_same
  have et := crtB_inst ht
  rcases hx with ⟨c, x, -, -, -, rfl, rfl, hx⟩ | ⟨cp, x, rfl, rfl, h1, -, -, h2, hold, hx⟩
  · exact ⟨fun q i cp hc => Or.inl (by rw [← et]; exact hc),
      fun d y hy => by rw [sentR_sendPeer hx hy]; trivial⟩
  · refine ⟨cp_setInst et ?_, fun d y hy => by rw [sentR_sendPeer hx hy]; trivial⟩
    simp only [Copy.valA, Prod.mk.injEq] at h2
    obtain ⟨ec, -, -, eb⟩ := h2
    refine copyW_strong (by rw [h1]; exact st_dec.2.2.2.2.2.2.2.2.1) (fun hn => ?_) ?_
    · rw [ec] at hn; rw [eb]; exact hm hn
    · intro lb hl hn
      rcases hold with hn0 | ⟨c, hc, hnc, -, el⟩
      · rw [accept_lb_none h hn0 cp (by rw [setInst_inst, if_pos ⟨rfl, rfl⟩])] at hl; cases hl
      · rw [el] at hl
        exact (C.copies _ _ _ hc).cand lb hl hnc

theorem lw_commit {m : ECommitM} (hm : WMsg S a (.commit m))
    (h : stepCommit s m = .ok (s', o)) : LocalW S s s' a o := by
  obtain ⟨rfl, t, ht, hx⟩ := A1d.stepCommit_shape h
  have et := crtB_inst ht
  rcases hx with ⟨-, -, -, rfl⟩ | ⟨cp, e1, -, -, h1, h2, -⟩
  · exact ⟨fun q i cp hc => Or.inl (by rw [← et]; exact hc), fun _ _ h => (sentR_nil h).elim⟩
  refine ⟨fun q i cp' hc => ?_, fun _ _ h => (sentR_nil h).elim⟩
  rw [e1] at hc
  refine cp_setInst et ?_ q i cp' hc
  simp only [Copy.valA, ECommitM.valA, Prod.mk.injEq] at h2
  obtain ⟨ec, -, -, eb⟩ := h2
  refine copyW_strong (by rw [h1]; exact st_dec.2.2.2.2.2.2.2.2.2.1) (fun hn => ?_)
    (fun _ _ hn => absurd (by rw [h1]; exact st_dec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) hn)
  rw [ec] at hn; rw [eb]; exact hm hn

theorem lw_acceptReply {m : AcceptReplyM} (C : Ctx S s a)
    (h : stepAcceptReply s m = .ok (s', o)) : LocalW S s s' a o := by
  rcases A1d.stepAcceptReply_shape h with ⟨rfl, rfl⟩ | ⟨c, lb, hc, -, hl, hx⟩
  · exact localW_same
  have hcw := C.copies _ _ _ hc
  rcases hx with ⟨rfl, lb', rfl, -, -, e, -⟩ | ⟨-, hs, lb'', hlc⟩
  · exact ⟨cp_setInst rfl (copyW_lb hcw hl e), fun _ _ h => (sentR_nil h).elim⟩
  · refine lw_leaderCommit C (fun hn => ?_) hlc
    obtain ⟨f, hf, k, -⟩ := hcw.val hn (by rw [hs]; exact st_dec.2.2.1)
    exact ⟨f, hf, k (by rw [hs]; exact st_dec.2.2.2.2.2.2.2.2.1)⟩

theorem not_cae {c : Copy} (h : ¬ SPA.isCAE c) : ¬ isCommitted c.status :=
  fun hh => h (hh.elim Or.inl (fun e => Or.inr (Or.inr e)))

/-! ## handlePreAccept -/

theorem lw_preAccept {m : PreAcceptM} (C : Ctx S s a) (hm : WMsg S a (.preAccept m))
    (hP0 : isInitialBallot m.ballot = true → m.ballot = 0)
    (h : stepPreAccept s m = .ok (s', o)) : LocalW S s s' a o := by
  obtain ⟨-, hc⟩ := SPA.stepPreAccept_cases h
  obtain ⟨f, hf, ⟨w, hw, hW⟩, h0⟩ := hm
  rcases hc with ⟨rfl, rfl⟩ | ⟨s1, c, x, hb, -, -, -, rfl, rfl, hx⟩ | ⟨s1, cp, x, hb, rfl, rfl, U⟩
  · exact localW_same
  · obtain ⟨ei, -, -⟩ := bump_facts hb
    refine ⟨fun q i cp hc => Or.inl (by rw [← ei]; exact hc), fun d y hy => ?_⟩
    obtain ⟨-, d0, -, rfl⟩ := hx
    rw [sentR_send hy]; intro hne; exact absurd rfl hne
  · obtain ⟨ei, et, -⟩ := bump_facts hb
    have hfa : TLe (f a) s1.tag := et ▸ C.store _ _ _ hf
    have hb1 : TLe m.base.t cp.base.t ∧ TLe s1.tag cp.base.t := by
      rcases U.base with ⟨g, e⟩ | ⟨g, e⟩
      · rw [e]; exact ⟨TLe.refl _, gt_false g⟩
      · rw [e]; exact ⟨gt_true g, TLe.refl _⟩
    have hW2 : Wit2 f cp.base := ⟨w, a, hw, hW.mono hb1.1, TLe.trans hfa hb1.2⟩
    refine ⟨fun q i cp' hc' => ?_, fun d y hy => ?_⟩
    · rw [(updateConflicts_inst _ _ _ _ _).1] at hc'
      refine cp_setInst ei ⟨fun _ _ => ⟨f, hf, fun _ => hW2, fun _ => TLe.trans hfa hb1.2⟩, ?_⟩
        q i cp' hc'
      intro lb hl hn
      rcases U.old with hn0 | ⟨c, hc, hnc, -, el⟩
      · rw [preAccept_lb_none h hn0 cp (by
          rw [(updateConflicts_inst _ _ _ _ _).1, setInst_inst, if_pos ⟨rfl, rfl⟩])] at hl
        cases hl
      · rw [el] at hl; exact (C.copies _ _ _ hc).cand lb hl (not_cae hnc)
    · rcases U.out with ⟨-, d0, -, rfl⟩ | ⟨hEQ, hrl, hinit, hne, d0, hd0, rfl⟩
      · rw [sentR_send hy]; intro _; exact ⟨f, hf, hW2⟩
      · obtain ⟨rfl, rfl⟩ := sentR_send2 hy
        have e1 : rid32 d0 = m.replica := by rw [A1b.dstOf_some hd0, hrl]
        refine ⟨f, by rw [e1]; exact hf, a, fun e => hne ?_, ?_⟩
        · rw [C.id, e, A1b.dstOf_some hd0]
        · have g := (U.st2 hEQ).2.2
          rw [U.base.elim (fun k => k.2) (fun k => absurd k.1 (by rw [g]; decide))] at hb1
          have k := h0 (hP0 hinit)
          rw [← e1, rowOf_rid32] at k
          exact TLe.trans (TLe.trans hfa (gt_false g)) k

/-! ## handlePreAcceptReply, handlePreAcceptOK -/

theorem lw_preAcceptReply {m : PreAcceptReplyM} (C : Ctx S s a) (hm : WMsg S a (.preAcceptReply m))
    (h : stepPreAcceptReply s m = .ok (s', o)) : LocalW S s s' a o := by
  obtain ⟨-, hc⟩ := SPA.stepPreAcceptReply_cases h
  rcases hc with ⟨rfl, rfl⟩ | ⟨c, lb, hc, hpre, -, hl, hx⟩
  · exact localW_same
  have hcw := C.copies _ _ _ hc
  rcases hx with ⟨-, rfl, lb', rfl, LS⟩ | ⟨hok, c2, lb2, hx, M, LO⟩
  · exact ⟨cp_setInst rfl (copyW_lb hcw hl LS.recoveryInst), fun _ _ h => (sentR_nil h).elim⟩
  obtain ⟨f, hf, hW⟩ := hm hok
  have hb2 : TLe m.base.t c2.base.t ∧ TLe c.base.t c2.base.t := by
    rcases M.base with ⟨g, e⟩ | ⟨g, e⟩
    · rw [e]; exact ⟨TLe.refl _, gt_true g⟩
    · rw [e]; exact ⟨gt_false g, TLe.refl _⟩
  have hW2 : Wit2 f c2.base := hW.mono hb2.1
  have hnc : ¬ isCommitted c.status := by rw [hpre]; exact st_dec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcand : CandOK S m.replica m.inst lb2.recoveryInst := by
    rw [LO.recoveryInst]; exact hcw.cand lb hl hnc
  rcases hx with ⟨-, -, -, hlc⟩ | ⟨rfl, hbc⟩ | ⟨-, rfl, rfl⟩
  · exact lw_leaderCommit C (fun _ => ⟨f, hf, hW2⟩) hlc
  · refine ⟨cp_setInst rfl ⟨fun _ _ => ⟨f, hf, fun _ => hW2, fun he => absurd he st_dec.2.2.2.2.2.1⟩,
      fun lb' hl' _ => by cases hl'; exact hcand⟩, fun d y hy => ?_⟩
    rw [sentR_bcast hbc hy]; intro _; exact ⟨f, hf, hW2⟩
  · refine ⟨cp_setInst rfl ⟨fun hn _ => ?_, fun lb' hl' _ => by cases hl'; exact hcand⟩,
      fun _ _ h => (sentR_nil h).elim⟩
    change c2.cmds ≠ [] at hn
    rw [M.cmds] at hn
    obtain ⟨g, hg, -, k⟩ := hcw.val hn (by rw [hpre]; exact st_dec.2.1)
    have := S_fun hf hg; subst this
    refine ⟨f, hf, fun _ => hW2, fun _ => (k hpre).mono hb2.2⟩

theorem lw_preAcceptOK {m : PreAcceptOKM} (C : Ctx S s a) (hm : WMsg S a (.preAcceptOK m))
    (h : stepPreAcceptOK s m = .ok (s', o)) : LocalW S s s' a o := by
  obtain ⟨-, hc⟩ := SPA.stepPreAcceptOK_cases h
  rcases hc with ⟨rfl, rfl⟩ | ⟨c, lb, hc, hpre, -, hl, hx⟩
  · exact localW_same
  obtain ⟨f, hf, X, hX, hXa⟩ := hm
  have hid := C.id
  rw [hid] at hc hx
  have hcw := C.copies _ _ _ hc
  have hv : c.cmds ≠ [] → ∃ g, S (rid32 a) m.inst = some g ∧ Wit2 g c.base := fun hn => by
    obtain ⟨g, hg, -, k⟩ := hcw.val hn (by rw [hpre]; exact st_dec.2.1)
    have := S_fun hf hg; subst this
    exact ⟨f, hf, X, a, hX, TLe.trans hXa (k hpre), k hpre⟩
  have hnc : ¬ isCommitted c.status := by rw [hpre]; exact st_dec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases hx with ⟨-, hlc⟩ | ⟨rfl, hbc⟩ | ⟨-, rfl, rfl⟩
  · exact lw_leaderCommit C hv hlc
  · refine ⟨cp_setInst rfl (copyW_strong st_dec.2.2.2.2.2.2.2.2.1 hv
      (fun lb' hl' _ => by cases hl'; exact hcw.cand lb hl hnc)), fun d y hy => ?_⟩
    rw [sentR_bcast hbc hy]; exact hv
  · exact ⟨cp_setInst rfl (copyW_lb hcw hl rfl), fun _ _ h => (sentR_nil h).elim⟩

/-! ## handlePrepare, startRecoveryForInstance -/

theorem lw_prepare {m : PrepareM} (C : Ctx S s a) (h : stepPrepare s m = .ok (s', o)) :
    LocalW S s s' a o := by
  obtain ⟨-, cp', r, x, rfl, hx, rfl, -, er, ei, hc⟩ := A1b.stepPrepare_cases h
  have hmsg : RepW S r → ∀ d y, y ∈ A1b.sentR d [x] → WMsg S d y := fun hr d y hy => by
    rw [sentR_sendPeer hx hy]; exact hr
  rcases hc with ⟨-, rfl, -, -, hst, -⟩ | ⟨c, hc, -, rfl, -, hst, hcm, -, -, hb⟩ |
      ⟨c, hc, -, rfl, -, -, hst, -, hcm, -, -, hb⟩
  · refine ⟨cp_setInst rfl ⟨fun _ hn => absurd rfl hn, fun _ hl => by cases hl⟩, hmsg ?_⟩
    intro _ hn; exact absurd hst hn
  · have hcw := C.copies _ _ _ hc
    refine ⟨cp_setInst rfl hcw, hmsg ?_⟩
    intro h1 h2; rw [hcm] at h1; rw [hst] at h2 ⊢; rw [hb, er, ei]
    obtain ⟨f, hf, k, -⟩ := hcw.val h1 h2; exact ⟨f, hf, k⟩
  · have hcw := C.copies _ _ _ hc
    refine ⟨cp_setInst rfl (copyW_ballot hcw _), hmsg ?_⟩
    intro h1 h2; rw [hcm] at h1; rw [hst] at h2 ⊢; rw [hb, er, ei]
    obtain ⟨f, hf, k, -⟩ := hcw.val h1 h2; exact ⟨f, hf, k⟩

theorem candOK_recRI {q i sid q' : w32} {c0 : Copy} (h : CopyW S q i a c0) :
    CandOK S q i (recRI c0 sid q') := by
  unfold recRI
  split
  · rename_i hs
    intro r hr hc; cases hr
    obtain ⟨f, hf, k, -⟩ := h.val hc (by rw [hs]; exact st_dec.2.2.1)
    exact ⟨f, hf, fun _ => k (by rw [hs]; exact st_dec.2.2.2.2.2.2.2.2.1)⟩
  · split
    · rename_i _ hs
      intro r hr hc; cases hr
      have hn : c0.status ≠ St.NONE := fun e => by rw [e] at hs; exact absurd hs (by decide)
      obtain ⟨f, hf, k, -⟩ := h.val hc hn
      refine ⟨f, hf, fun hs' => k ?_⟩
      rcases hs' with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    · intro r hr; cases hr

theorem lw_recover {q i : w32} (C : Ctx S s a) (h : stepRecover s q i = .ok (s', o)) :
    LocalW S s s' a o := by
  rcases stepRecover_cases h with ⟨rfl, rfl⟩ | ⟨c0, hc0, -, -, -, -, -, rfl, hbc⟩
  · exact localW_same
  have hcw : CopyW S q i a c0 := by
    rcases hc0 with hc | ⟨-, rfl⟩
    · exact C.copies _ _ _ hc
    · exact ⟨fun _ hn => absurd rfl hn, fun _ hl => by cases hl⟩
  refine ⟨cp_setInst rfl ⟨hcw.val, fun lb hl _ => by cases hl; exact candOK_recRI hcw⟩,
    fun d y hy => by rw [sentR_bcast hbc hy]; trivial⟩

/-! ## handlePrepareReply -/

theorem candOK_riOf {m : PrepareReplyM} (hs : m.status ≠ St.NONE) (hm : RepW S m) (c : w64)
    (lr : Bool) : CandOK S m.replica m.inst (some (riOf m c lr)) := by
  intro r hr hc; cases hr
  obtain ⟨f, hf, k⟩ := hm hc hs
  refine ⟨f, hf, fun hs' => k ?_⟩
  rcases hs' with e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)

theorem candOK_upd {ri : Option RecoveryInstance} {m : PrepareReplyM}
    (h : CandOK S m.replica m.inst ri) (hm : RepW S m) : CandOK S m.replica m.inst (upd ri m) := by
  have h1 : CandOK S m.replica m.inst (upd1 ri m) := by
    unfold upd1; split
    · rename_i hs; dsimp only; split
      · exact candOK_riOf (by rw [hs]; exact st_dec.2.2.1) hm _ _
      · split
        · exact candOK_riOf (by rw [hs]; exact st_dec.2.2.1) hm _ _
        · exact h
    · exact h
  unfold upd upd2
  split
  · rename_i hc
    have hs : m.status ≠ St.NONE := by
      rcases hc.1 with e | e <;> rw [e] <;> decide
    dsimp only
    split
    · exact candOK_riOf hs hm _ _
    · rename_i r hr
      split
      · intro r' hr' hc'; cases hr'; exact h1 r hr hc'
      · split
        · exact candOK_riOf hs hm _ _
        · intro r' hr' hc'; cases hr'; exact h1 r hr hc'
  · exact h1

theorem candOK_setLr {q i : w32} {r : RecoveryInstance} (h : CandOK S q i (some r)) :
    CandOK S q i (some (setLr r)) := fun r' hr' hc' => by cases hr'; exact h r rfl hc'

/-- `prMain` (the reply is OK, at the copy's ballot, not committed). -/
theorem lw_prMain {m : PrepareReplyM} {c : Copy} {lb0 : LB} (C : Ctx S s a)
    (hc : s.inst m.replica m.inst = some c) (hl : c.lb = some lb0)
    (hst : ¬ (c.status = St.COMMITTED ∨ c.status = St.EXECUTED)) (hm : RepW S m)
    (hb0 : c.ballot ≠ 0) (h : prMain s m c lb0 = .ok (s', o)) : LocalW S s s' a o := by
  have hcw := C.copies _ _ _ hc
  have hcand := candOK_upd (hcw.cand lb0 hl (not_committed_of hst)) hm
  unfold prMain at h
  dsimp only at h
  split at h
  · split at h
    · rename_i r hr
      cases h
      exact ⟨cp_setInst rfl (copyW_withLb hcw _ (fun _ => by
        show CandOK S m.replica m.inst (some (setLr r)); rw [hr] at hcand; exact candOK_setLr hcand)),
        fun _ _ h => (sentR_nil h).elim⟩
    · cases h
  split at h
  · cases h
    exact ⟨cp_setInst rfl (copyW_withLb hcw _ (fun _ => hcand)), fun _ _ h => (sentR_nil h).elim⟩
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
        have hv : ir.cmds ≠ [] → ∃ f, S m.replica m.inst = some f ∧ Wit2 f ir.base := fun hn => by
          obtain ⟨f, hf, k⟩ := hcand ir rfl hn
          refine ⟨f, hf, k ?_⟩
          rcases hcond with e | ⟨-, -, e⟩
          · exact Or.inl e
          · exact Or.inr e
        refine ⟨cp_setInst rfl (copyW_strong st_dec.2.2.2.2.2.2.2.2.1 hv
          (fun lb hl' _ => by cases hl'; show CandOK S m.replica m.inst (upd lb0.recoveryInst m); rw [hir']; exact hcand)), fun d y hy => ?_⟩
        rw [sentR_bcast hbc hy]; exact hv
      · cases h
    · split at h
      · cases h
      · obtain ⟨cp, hi, -, -, hps, -, hcm, hne, hbase, hlb, hout⟩ := sp1W h
        obtain ⟨f, hf, -⟩ := hcand ir rfl hne
        have hW : W1 f a cp.base := by rw [hbase]; exact C.store _ _ _ hf
        refine ⟨fun q j cp' hc' => ?_, fun d y hy => ?_⟩
        · rw [hi] at hc'
          split at hc'
          · rename_i e; obtain ⟨rfl, rfl⟩ := e; cases hc'
            refine Or.inr ⟨fun _ _ => ⟨f, hf, fun hs => absurd hs (by rw [hps]; exact st_dec.2.2.2.2.2.2.2.2.2.2.2.1),
              fun _ => hW⟩, fun lb hl' _ => by rw [hlb lb hl']; intro r hr; cases hr⟩
          · rw [setInst_inst, if_neg (by assumption)] at hc'; exact Or.inl hc'
        · obtain ⟨x, rfl, hxr, hxi, hxb, hxbase, hd⟩ := hout d y hy
          have hda : a ≠ d := fun e => hd (by rw [← e, ← C.id]; rfl)
          refine ⟨f, by rw [hxr, hxi]; exact hf, ⟨a, hda, by rw [hxbase]; exact hW⟩, fun h0 => ?_⟩
          rw [hxb] at h0; exact absurd h0 hb0
  · rename_i hir
    dsimp only at h
    split at h
    · rename_i outs hbc
      cases h
      refine ⟨cp_setInst rfl ⟨fun hn _ => absurd rfl hn, fun lb hl' _ => by
        cases hl'; show CandOK S m.replica m.inst (upd lb0.recoveryInst m)
        intro r hr; rw [hr] at hir; cases hir⟩, fun d y hy => ?_⟩
      rw [sentR_bcast hbc hy]; intro hn; exact absurd rfl hn
    · cases h

theorem lw_prepareReply {m : PrepareReplyM} (C : Ctx S s a) (hm : WMsg S a (.prepareReply m))
    (hb0 : m.ok ≠ FALSE → m.ballot ≠ 0)
    (h : stepPrepareReply s m = .ok (s', o)) : LocalW S s s' a o := by
  rcases stepPrepareReply_cases h with ⟨rfl, rfl⟩ | ⟨c, lb0, hc, hl, rfl, rfl⟩ |
      ⟨c, lb0, hc, hl, -, -, -, -, hms, rfl, hbc⟩ | ⟨c, lb0, hc, hl, -, hst, hok, hb, -, -, -, hpm⟩
  · exact localW_same
  · exact ⟨cp_setInst rfl (copyW_lb (C.copies _ _ _ hc) hl rfl), fun _ _ h => (sentR_nil h).elim⟩
  · have hv : m.cmds ≠ [] → ∃ f, S m.replica m.inst = some f ∧ Wit2 f m.base := fun hn => by
      have hs : Strong m.status := by
        rcases hms with e | e
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inr (Or.inr (Or.inr e))
      obtain ⟨f, hf, k⟩ := hm hn (fun e => by rw [e] at hs; exact absurd hs (by unfold Strong; decide))
      exact ⟨f, hf, k hs⟩
    refine ⟨cp_setInst rfl (copyW_strong st_dec.2.2.2.2.2.2.2.2.2.1 hv
      (fun _ _ hn => absurd st_dec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hn)), fun d y hy => ?_⟩
    rw [sentR_bcast hbc hy]; exact hv
  · exact lw_prMain C hc hl hst hm (by rw [← hb]; exact hb0 hok) hpm

/-! ## The RMW (creation): the new ghost entry -/

/-- The creation's local obligations, with the ghost extended at the new instance by the current
stores `F` (`F a` is `a`'s store). -/
theorem lw_rmw {rid cid : w32} {k : w64} {d : Dep} {oldV newV : w64} {F : Fin 3 → model.Tag}
    (C : Ctx S s a) (hF : F a = s.tag) (hS : S (rid32 a) (s.crt (rid32 a)) = none)
    (h : stepClientRMW s rid cid k d oldV newV = .ok (s', o)) :
    LocalW (S.set (rid32 a) (s.crt (rid32 a)) F) s s' a o := by
  obtain ⟨t, ps, cs, hti, htt, htinst, -, hsp⟩ := rmwW h
  obtain ⟨cp, hi, -, -, hps, hcb, hcm, hne, hbase, hlb, hout⟩ := sp1W hsp
  have hle := CSG.set_le (f := F) hS
  have hid := C.id
  have hF' : (S.set (rid32 a) (s.crt (rid32 a)) F) (rid32 a) (s.crt (rid32 a)) = some F := by
    simp [CSG.set]
  have hW : W1 F a cp.base := by
    rw [hbase]; show TLe (F a) t.tag; rw [hF, htt]; exact TLe.refl _
  refine ⟨fun q j cp' hc' => ?_, fun d' y hy => ?_⟩
  · rw [hi] at hc'
    split at hc'
    · rename_i e; obtain ⟨rfl, rfl⟩ := e; cases hc'
      rw [hid]
      refine Or.inr ⟨fun _ _ => ⟨F, hF', fun hs => absurd hs (by rw [hps]; exact st_dec.2.2.2.2.2.2.2.2.2.2.2.1),
        fun _ => hW⟩, fun lb hl' _ => by rw [hlb lb hl']; intro r hr; cases hr⟩
    · rw [htinst] at hc'; exact Or.inl hc'
  · obtain ⟨x, rfl, hxr, hxi, hxb, hxbase, hd⟩ := hout d' y hy
    have hda : a ≠ d' := fun e => hd (by rw [← e, hti, hid])
    refine ⟨F, by rw [hxr, hxi, hid]; exact hF', ⟨a, hda, by rw [hxbase]; exact hW⟩, fun _ => ?_⟩
    rw [hxr, hid, rowOf_rid32, hxbase, hbase, hF, ← htt]; exact TLe.refl _

end Perennial.gryff.pureA.AW
