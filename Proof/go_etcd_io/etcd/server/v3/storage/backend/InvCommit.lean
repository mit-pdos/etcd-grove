/-
The batch lock's ghost state across a commit (`unsafeCommit`): the payment (`payIn`) spent,
the counters reset (`commit_bgOk`), the lock's share of the free state rebuilt
(`commit_ghost`). Lean-first (no Rocq counterpart); see `InvBatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CommitLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.WritebackLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClaimedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **A commit keeps the buffers' receipt** (2026-11-22, step 2): it drops the read buffer and keeps
the write buffer. -/
theorem bufRc_commitSt (st : BSess) (C' : Data) (tx' : Loc) (cnt' : BCnt) :
    bufRc (GF := GF) st ⊢ bufRc (commitSt st C' tx' cnt') :=
  bufRc_mono (fun i => by
    rw [commitSt_R, commitSt_W]
    show (bkOf (bksReset st.R.bks) i).length + _ ≤ _
    rw [bkOf_bksResetC]
    simp)

/-- **A write-back keeps the buffers' receipt** (2026-11-22, step 2): it moves the write buffer's
entries into the read buffer (`wbMerge`, no longer than both) and empties the write buffer. -/
theorem bufRc_wbSt (P : BParams) (st : BSess) :
    bufRc (GF := GF) st ⊢ bufRc (wbSt P st) :=
  bufRc_mono (fun i => by
    show (bkOf (wbMerge st.W.bks st.R.bks) i).length + (bkOf (writebackW st.W st.R).bks i).length ≤ _
    rw [bkOf_writebackW]
    have := length_bkOf_wbMerge st.W.bks st.R.bks i
    simp only [List.length_nil, Nat.add_zero]
    omega)

/-- The batch lock's share of the free state after a commit from `st` (the hook ran into
`st'`), paid by `payIn`: the new committed data `C'`, write transaction `tx'`. -/
theorem commit_ghost (γ : BNames) (P : BParams) (st st' : BSess) (C' : Data) (tx' : Loc)
    (m u n w u0 : Nat) (L : VData) (cnt0 : BCnt)
    (hW : ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = [])
    (hp0 : st.cnt.p0 = sint.nat st.pend) (hs : hookStep P st st') (hst : sessWf P st)
    (hb' : bgOk P st' false n w u0) (hC' : C' = st'.S ∨ (st'.pend = W64 0 ∧ C' = st'.C))
    (hdl : dlsS P st' ∧ dlsOk P st' L)
    (htk : ∀ n, P.RB n = true → st.tk n = .idle ∨ st.tk n = .del) (hst' : sessWf P st') :
    payIn (GF := GF) γ st false m u ∗ ownTokAuth γ.wb n ∗ monoNatAuthOwn γ.wbc 1 w ∗
      ghostVar γ.used (1 : Qp).half u0 ∗ dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
      viewQ γ (1 : Qp).half.half (vData P (C', st'.R.reset)) L ∗
      ghostVar γ.rvs (1 : Qp).half (((C', st'.R.reset) : RView), false) ∗
      trkSide γ P (commitSt st' C' tx' cnt0) ∗ fkHalf γ P st' ∗ bufRc st' ⊢
    |==> ∃ cnt' : BCnt, ⌜cnt'.hw = false⌝ ∗ batchGhostAt γ P (commitSt st' C' tx' cnt') true ∗
      payOut γ false m := by
  iintro ⟨Hpay, Ha, Hm, Hu, Ho, Hv, Hr, Hk, Hfk, #Hbr⟩
  have hC0 : C' = st'.S ∨ C' = st'.C := hC'.imp id (fun h => h.2)
  have hT := fun (cnt' : BCnt) =>
    (trkOk_commitG (tx' := tx') (cnt' := cnt') hs htk hb'.2.2.2.2.2.2.2.2.2.2.1 hst' hC').1
  have hR := hs.2.1
  have hcnt := hs.2.2.2.2.2.2.2.2.2.1
  have hb'0 := hb'
  obtain ⟨hb1, hb2, hb3, -⟩ := hb'0
  have hwv : (w : Int) ≤ uint.Z st.R.ver := by
    have := hb'.2.2.2.2.2.2.2.2.2.1; rw [hR] at this; exact this
  rw [hcnt, hR] at hb1
  rw [hcnt] at hb3
  unfold payIn payOut
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hm0 : m = 0
  · rw [if_pos hm0, if_neg (fun h : True ∧ m = 1 => by omega)]
    unfold wbTok
    icombine Ha Hpay gives %Hle
    imod ownTokAuth_sub 1 γ.wb n $$ Ha Hpay with Ha
    imodintro
    iexists ⟨st.cnt.k + 1, st.cnt.c + 1, 0, 0, false⟩
    isplitr
    · ipureintro; rfl
    ihave Hk := trkSide_congr γ P (commitSt st' C' tx' cnt0) (commitSt st' C' tx' ⟨st.cnt.k + 1, st.cnt.c + 1, 0, 0, false⟩) rfl rfl rfl
      (fun _ _ => rfl) rfl false (fun _ _ _ _ => rfl) $$ Hk
    isplitl [Hv Hr Ha Hm Hu Ho Hk Hfk]
    · unfold batchGhostAt batchViewQ
      ihave Hfk := fkHalf_mono γ P (st' := commitSt st' C' tx' _) (fkOkG_commit hC0) rfl rfl $$ Hfk
      simp only [commitSt_C, commitSt_R, commitSt_S]
      iframe Hk Hfk
      isplitl [Hv]
      · iexists L; iframe Hv; ipureintro; exact ⟨hdl.1, fun _ => hdl.2, fun _ => rfl⟩
      iexists n - 1, w, u0
      iframe Hr Ha Hm Hu Ho
      ihave #Hbrc := bufRc_commitSt st' C' tx' ⟨st.cnt.k + 1, st.cnt.c + 1, 0, 0, false⟩ $$ Hbr
      iframe Hbrc
      ipureintro
      have hb4 : uint.Z st.R.ver + ((n - 1 : Nat) : Int) + ((st.cnt.k + 1 : Nat) : Int) < 2 ^ 62 := by
        omega
      refine (commit_bgOk (k' := st.cnt.k + 1) hW hp0 hs hst hb' (n - 1) w u0
        hb4 hb2 ?_ hwv (hT _))
      split at hb3 <;> split <;> omega
    · itrivial
  by_cases hm1 : m = 1
  · rw [if_neg hm0, if_pos hm1, if_pos ⟨trivial, hm1⟩]
    icases Hpay with ⟨Hru, #Hlb⟩
    icombine Hu Hru gives % ⟨_, Hueq⟩
    subst Hueq
    ihave %Hlw := monoNatLbOwn_valid γ.wbc 1 w (u0 + 1) $$ Hm Hlb
    imod ghostVar_update_halves w γ.used u0 u0 $$ Hu Hru with ⟨Hu, Hru⟩
    imodintro
    iexists ⟨st.cnt.k, st.cnt.c + 1, 0, 0, false⟩
    isplitr
    · ipureintro; rfl
    ihave Hk := trkSide_congr γ P (commitSt st' C' tx' cnt0) (commitSt st' C' tx' ⟨st.cnt.k, st.cnt.c + 1, 0, 0, false⟩) rfl rfl rfl
      (fun _ _ => rfl) rfl false (fun _ _ _ _ => rfl) $$ Hk
    isplitl [Hv Hr Ha Hm Hu Ho Hk Hfk]
    · unfold batchGhostAt batchViewQ
      ihave Hfk := fkHalf_mono γ P (st' := commitSt st' C' tx' _) (fkOkG_commit hC0) rfl rfl $$ Hfk
      simp only [commitSt_C, commitSt_R, commitSt_S]
      iframe Hk Hfk
      isplitl [Hv]
      · iexists L; iframe Hv; ipureintro; exact ⟨hdl.1, fun _ => hdl.2, fun _ => rfl⟩
      iexists n, w, w
      iframe Hr Ha Hm Hu Ho
      ihave #Hbrc := bufRc_commitSt st' C' tx' ⟨st.cnt.k, st.cnt.c + 1, 0, 0, false⟩ $$ Hbr
      iframe Hbrc
      ipureintro
      refine (commit_bgOk (k' := st.cnt.k) hW hp0 hs hst hb' n w w
        hb1 (Nat.le_refl _) ?_ hwv (hT _))
      have : u0 ≠ w := by omega
      simp only [this, ↓reduceIte] at hb3
      simp only [↓reduceIte]
      omega
    · iexists w
      iexact Hru
  · rw [if_neg hm0, if_neg hm1, if_neg (fun h : True ∧ m = 1 => hm1 h.2)]
    icases Hpay with ⟨%Hc0, -⟩
    imodintro
    iexists ⟨st.cnt.k, st.cnt.c + 1, 0, 0, false⟩
    isplitr
    · ipureintro; rfl
    ihave Hk := trkSide_congr γ P (commitSt st' C' tx' cnt0) (commitSt st' C' tx' ⟨st.cnt.k, st.cnt.c + 1, 0, 0, false⟩) rfl rfl rfl
      (fun _ _ => rfl) rfl false (fun _ _ _ _ => rfl) $$ Hk
    isplitl [Hv Hr Ha Hm Hu Ho Hk Hfk]
    · unfold batchGhostAt batchViewQ
      ihave Hfk := fkHalf_mono γ P (st' := commitSt st' C' tx' _) (fkOkG_commit hC0) rfl rfl $$ Hfk
      simp only [commitSt_C, commitSt_R, commitSt_S]
      iframe Hk Hfk
      isplitl [Hv]
      · iexists L; iframe Hv; ipureintro; exact ⟨hdl.1, fun _ => hdl.2, fun _ => rfl⟩
      iexists n, w, u0
      iframe Hr Ha Hm Hu Ho
      ihave #Hbrc := bufRc_commitSt st' C' tx' ⟨st.cnt.k, st.cnt.c + 1, 0, 0, false⟩ $$ Hbr
      iframe Hbrc
      ipureintro
      refine (commit_bgOk (k' := st.cnt.k) hW hp0 hs hst hb' n w u0
        hb1 hb2 ?_ hwv (hT _))
      rw [Hc0]
      split <;> omega
    · itrivial

theorem payIn_setHw (γ : BNames) (st : BSess) (x stop : Bool) (m u : Nat) :
    payIn (GF := GF) γ (st.setHw x) stop m u = payIn γ st stop m u := rfl

/-- **The batch lock's quarter at the hook's window** (`BSess.setHw`): from an `Unlock`'s commit
window's (`win`, the state marked as one: `hw`) or from the batch lock's. -/
theorem batchViewQ_setHw (γ : BNames) (P : BParams) (st : BSess) (win : Bool)
    (hw : win = true → st.win = true) :
    (if win then batchViewQ0 (GF := GF) γ P st else batchViewQ γ P st) ⊢
      batchViewQ γ P (st.setHw true) := by
  cases win with
  | true =>
    simp only [↓reduceIte]
    unfold batchViewQ0 batchViewQ
    simp only [setHw_C, setHw_R]
    iintro ⟨%L, Hq, %Hd⟩
    iexists L
    iframe Hq
    ipureintro
    refine ⟨Hd, fun hf => ?_, fun hh => ?_⟩
    · have : (st.setHw true).win = st.win := rfl
      rw [this, hw rfl] at hf; cases hf
    · exact absurd hh (by simp [BSess.setHw])
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iapply batchViewQ_mono γ P (st := st) (st' := st.setHw true) rfl rfl
      (fun _ _ h => ⟨h.1, h.2.1, fun hh => absurd hh (by simp [BSess.setHw])⟩)

/-- Out of an `Unlock`'s commit window, a state out of the hook's window is out of an `Unlock`'s
window (the batch lock's quarter's agreement). -/
theorem batchViewQW_win (γ : BNames) (P : BParams) (st : BSess) (win : Bool) :
    (if win then batchViewQ0 (GF := GF) γ P st else batchViewQ γ P st) ⊢
      (if win then batchViewQ0 γ P st else batchViewQ γ P st) ∗
        ⌜win = false → st.cnt.hw = false → st.win = false⌝ := by
  cases win with
  | true =>
    simp only [↓reduceIte]
    iintro H; iframe H; ipureintro; intro h; cases h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold batchViewQ
    iintro ⟨%L, Hq, %Hd⟩
    isplitl
    · iexists L; iframe Hq; ipureintro; exact Hd
    · ipureintro; intro _ hh; exact Hd.2.2 hh

/-- The batch lock held at the hook's window, from its parts. -/
theorem batchLocked_setHw_mk (γ : BNames) (P : BParams) (b t db : Loc) (st : BSess) (c : Bool := false) :
    (bF go!"batchTx" b ↦□ t : IProp GF) ∗ sync.ownMutex (muOf t) ∗ batchPhys γ b t db st ∗
      batchViewQ γ P (st.setHw true) ∗
      (∃ (n w u : Nat), ghostVar γ.rvs (1 : Qp).half (((st.C, st.R) : RView), false) ∗
        ownTokAuth γ.wb n ∗ monoNatAuthOwn γ.wbc 1 w ∗ ghostVar γ.used (1 : Qp).half u ∗
        dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
        trkSide γ P st c ∗ fkHalf γ P st ∗ bufRc st ∗ ⌜bgOk P st false n w u⌝) ∗ ⌜sessWf P st⌝ ⊢
    batchLocked γ P b (st.setHw true) := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt
  iintro ⟨#Ht, Hown, Hph, Hv, ⟨%n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, #Hbr, %Hok⟩, %Hwf⟩
  ihave #Hbr2 := bufRc_congr (st := st) (st' := st.setHw true) rfl rfl $$ Hbr
  -- (A1.5) in the hook's window the client-facing mode allows claimed writes
  ihave Hk := trkSide_congr γ P st (st.setHw true) rfl rfl rfl (fun _ _ => rfl) rfl c
    (fun _ _ h => by simp [BSess.setHw] at h) $$ Hk
  ihave Hk := trkSide_mode_win γ P (st.setHw true) c false rfl $$ Hk
  iexists t, db
  rw [show batchPhys γ b t db (st.setHw true) = batchPhys γ b t db st from rfl]
  simp only [setHw_C, setHw_R, setHw_S]
  iframe Ht Hown Hph Hv
  isplitl [Hr Ha Hm Hu Ho Hk Hfk]
  · iexists n, w, u
    ihave Hfk := fkHalf_mono γ P (st' := st.setHw true) (fkOkG_setHw true) rfl rfl $$ Hfk
    iframe
    iframe Hbr2
    ipureintro
    exact bgOk_setHw true Hok
  · ipureintro
    exact sessWf_setHw Hwf

/-- The commit opens the hook's window on the batch lock's state (`BSess.setHw`). -/
theorem batchLockedW_setHw (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (c : Bool := false) :
    batchLockedW (GF := GF) γ P b st false c ⊢ batchLocked γ P b (st.setHw true) := by
  unfold batchLockedW batchGhostW
  iintro ⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, Hrest⟩, %Hwf⟩
  ihave Hv := batchViewQ_setHw γ P st false (fun h => by cases h) $$ Hv
  iapply batchLocked_setHw_mk γ P b t db st c
  iframe Ht Hown Hph Hv Hrest
  ipureintro; exact Hwf

end lemmas

end backend
end EtcdGrove
end Perennial
