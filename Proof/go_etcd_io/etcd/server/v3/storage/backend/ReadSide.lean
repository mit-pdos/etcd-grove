/-
The read side's part of the batch transaction's `Unlock` and commit (`batch_tx.go`): the
transitions of `readTx.mu`'s resource (`rtRes`, held whole through `readTx.Lock`) that the
write-back and the commit make, and the rollback goroutine's `Wait`. Lean-first (no Rocq
counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend: the buffers, bbolt
as a key-value contract, the locks and the views".

**The write-back** (`Unlock`, `pending != 0`): `rtRes_wb_open` gives the read buffer
(`ownRB`, for `txWriteBuffer.writeback`) and keeps the rest (`rtWb`); `rtRes_wb_close` takes
the written-back buffer `writebackR W R` (a new version, the history's state `(ver + 1, 0)`),
the clients' whole share of the view and the batch lock's quarter, and gives back `rtRes`. With
`win` (the commit follows: a delete is pending), the window opens: the clients' share is
deposited in `cacheInv` and the new state is poisoned (never cached), since the commit changes
the readers' view under an unchanged version.

**The commit** (`unsafeCommit`): `rtRes_cm_open` gives the shared transaction's fields and the
read buffer (for `readTx.reset`), ends the interval (deposits `wgOpen 1` in its `WaitGroup`'s
protocol) and hands the rollback goroutine `rollbackRes` (with which `wp_rollback_Wait` waits
for the readers and gets the whole bbolt read transaction back, for `Rollback`), keeping the rest
(`rtCm`); `rtRes_cm_close` takes the reset fields and buffer and the new bbolt read
transaction (or, at `CommitAndStop`, `bStopped`), allocates the new interval's invariants, and
records the state `(ver, i + 1)` (the version unchanged) with the new committed data. Out of a
window it gives back the clients' share; otherwise the readers' view must be unchanged
(`vData P (C', R.reset) = vData P (C, R)`: the hook changes only its own buckets).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `readTx.mu`'s resource during a write-back of the read buffer `R` over the committed data
`C`, but the read buffer. -/
def rtWb (γ : BNames) (P : BParams) (rt : Loc) (C : Data) (R : RBuf) : IProp GF :=
  iprop(∃ (rd : RdSt) (cm : GoMap) (H : GMap (w64 × Nat) RView), ⌜rd.win = false⌝ ∗
    rbktOf (baseOf rt) ↦ cm ∗ rtRest γ P rt 1 rd (C, R) cm H)

/-- `readTx.mu`'s resource during a commit from the readers' state `(C, R)` (in a window or
not): its ghost state, without the shared transaction's fields, the read buffer and the
interval. -/
def rtCm (γ : BNames) (P : BParams) (C : Data) (R : RBuf) (win : Bool) : IProp GF :=
  iprop(∃ (rd : RdSt) (H : GMap (w64 × Nat) RView),
    ghostVar γ.rd 1 rd ∗ ghostVar γ.view (1 : Qp).half.half (vData P (C, R)) ∗
    ghostVar γ.rvs (1 : Qp).half ((C, R), win) ∗
    ghostVar γ.cur (1 : Qp).half ((R.ver, rd.idx), win) ∗ ghostMapAuth γ.hist 1 H ∗
    ⌜rd.win = win ∧ R.Wf ∧ idsOk P R.bks ∧ H.lookup (R.ver, rd.idx) = some (C, R) ∧
      (∀ k rv', H.lookup k = some rv' → keyLe k (R.ver, rd.idx)) ∧ (win = true → rd.idx = 0)⌝ ∗
    histAt γ R.ver rd.idx (C, R) ∗ cacheValid γ P (C, R) rd.idx ∗
    (if win then poisonAt γ R.ver rd.idx else iprop(True)) ∗
    ownTokAuthDfrac γ.rdt DFrac.discard rdMax)

/-- What the rollback goroutine of an ended interval holds: the interval's `WaitGroup`, closed
to readers (its waiters' authority), the other half of the bbolt read transaction and its
snapshot. -/
def rollbackRes (γ : BNames) (rtx wg : Loc) : IProp GF :=
  iprop(∃ (γwg : sync.WaitGroupNames) (γw γo γt : GName) (D : Data),
    sync.isWaitGroup wg γwg (bN.@"wg") ∗ inv (bN.@"wgi") (wgBody γ rtx γwg γw γo γt) ∗
    sync.ownWaitGroupWaiters γwg 0 ∗ ghostVar γt 1 () ∗ txLive rtx (1 : Qp).half ∗
    rtxSnap rtx D)

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `readTx.mu`'s whole resource holds a half of `γ.rvs`. -/
theorem rtRes_rvs (γ : BNames) (P : BParams) (rt : Loc) :
    rtRes (GF := GF) γ P rt 1 ⊢ ∃ y : RView × Bool, ghostVar γ.rvs (1 : Qp).half y ∗
      (ghostVar γ.rvs (1 : Qp).half y -∗ rtRes γ P rt 1) := by
  unfold rtRes rtResAt rtRest rtCore
  iintro ⟨%rd, %rv, %H, %m, %Pb, %cm, Hrb, %Hok, Hcm, Hview, Hrd, Hrvs, Hr⟩
  iexists (rv, rd.win)
  iframe Hrvs
  iintro Hrvs
  iexists rd, rv, H, m, Pb, cm
  iframe
  ipureintro; exact Hok

/-- `rtCm`'s half of `γ.rvs`, out and back. -/
theorem rtCm_rvs (γ : BNames) (P : BParams) (C : Data) (R : RBuf) (win : Bool) :
    rtCm (GF := GF) γ P C R win ⊢ ghostVar γ.rvs (1 : Qp).half ((C, R), win) ∗
      (ghostVar γ.rvs (1 : Qp).half ((C, R), win) -∗ rtCm γ P C R win) := by
  unfold rtCm
  iintro ⟨%rd, %H, Hrd, Hview, Hrvs, Hr⟩
  iframe Hrvs
  iintro Hrvs
  iexists rd, H
  iframe

/-! ## The write-back -/

/-- Before the write-back: the read buffer out of `readTx.mu`'s resource (the batch lock's
share of `γ.rvs` says which). -/
theorem rtRes_wb_open (γ : BNames) (P : BParams) (rt : Loc) (C : Data) (R : RBuf) :
    rtRes (GF := GF) γ P rt 1 ∗ ghostVar γ.rvs (1 : Qp).half ((C, R), false) ⊢
      ownRB (rbufOf (baseOf rt)) R ∗ ⌜R.Wf ∧ idsOk P R.bks⌝ ∗ rtWb γ P rt C R ∗
      ghostVar γ.rvs (1 : Qp).half ((C, R), false) := by
  unfold rtRes rtResAt
  iintro ⟨⟨%rd, %rv, %H, %m, %Pb, %cm, Hrb, %Hok, Hcm, Hr⟩, Hb⟩
  unfold rtRest rtCore
  icases Hr with ⟨Hview, Hrd, Hrvs, Hr⟩
  icombine Hrvs Hb gives %Heq0
  have Heq := Heq0.2
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, Hw⟩ := Heq
  ihave Hown := rbAt_ownRB _ m Pb R Hok $$ Hrb
  icases Hr with ⟨Hcur, Hhist, Hrtx, Hwg, %Hf, Hr⟩
  iframe
  isplitr
  · ipureintro; exact ⟨Hf.1, Hf.2.1⟩
  unfold rtWb
  iexists rd, cm, H
  unfold rtRest rtCore
  iframe
  ipureintro; exact ⟨Hw, Hf⟩

/-- The view's two quarters and the clients' half updated together. -/
theorem view_upd3 (γ : BNames) (a1 a2 a3 b : VData) :
    ghostVar (GF := GF) γ.view (1 : Qp).half.half a1 ∗ ghostVar γ.view (1 : Qp).half.half a2 ∗
      ghostVar γ.view (1 : Qp).half a3 ⊢
    |==> (ghostVar γ.view (1 : Qp).half.half b ∗ ghostVar γ.view (1 : Qp).half.half b ∗
      ghostVar γ.view (1 : Qp).half b) := by
  iintro ⟨H1, H2, H3⟩
  icombine H1 H2 gives %h12
  obtain ⟨_, rfl⟩ := h12
  ihave H12 := ((ghostVar_fractional (GF := GF) γ.view a1).fractional
    (1 : Qp).half.half (1 : Qp).half.half).2 $$ [H1 H2]
  · iframe
  have Hq : ((1 : Qp).half.half + (1 : Qp).half.half) + (1 : Qp).half = 1 := by
    rw [Qp.half_add_half, Qp.half_add_half]
  imod ghostVar_update_2 b γ.view a1 _ a3 _ Hq $$ H12 H3 with ⟨H12, H3⟩
  icases ghostVar_split γ.view b (1 : Qp).half.half (1 : Qp).half.half $$ H12 with ⟨H1, H2⟩
  imodintro
  iframe

theorem rtIntv_congr (γ : BNames) (P : BParams) (q : Qp) (rd rd' : RdSt) (cm : GoMap) (D : Data)
    (h1 : rd'.rtx = rd.rtx) (h2 : rd'.wg = rd.wg) (h3 : rd'.γw = rd.γw) (h4 : rd'.γo = rd.γo)
    (h5 : rd'.live = rd.live) (h6 : rd'.γt = rd.γt) :
    rtIntv (GF := GF) γ P q rd cm D ⊢ rtIntv γ P q rd' cm D := by
  unfold rtIntv; rw [h1, h2, h3, h4, h5, h6]

theorem rtIntv_upd (γ : BNames) (P : BParams) (q : Qp) (rd : RdSt) (i : Nat) (w : Bool)
    (cm : GoMap) (D : Data) :
    rtIntv (GF := GF) γ P q { rd with idx := i, win := w } cm D = rtIntv γ P q rd cm D := rfl

/-- The write-back's common part: the new version's state `(ver + 1, 0)`, given the view's
quarter already at the new view, the clients' share to deposit for a window. -/
theorem wb_core (γ : BNames) (P : BParams) (rt : Loc) (W : WBuf) (C : Data) (R : RBuf)
    (win : Bool) (hW : idsOk P W.bks) (hver : uint.Z R.ver + 1 < 2 ^ 64) :
    cacheInv (GF := GF) γ ∗
      (∃ (rd : RdSt) (cm : GoMap) (H : GMap (w64 × Nat) RView), ⌜rd.win = false⌝ ∗
        rbktOf (baseOf rt) ↦ cm ∗ rtCore γ P rt 1 rd (C, R) cm H) ∗
      ghostVar γ.view (1 : Qp).half.half (vData P (C, writebackR W R)) ∗
      ownRB (rbufOf (baseOf rt)) (writebackR W R) ∗
      ghostVar γ.rvs (1 : Qp).half ((C, R), false) ∗
      (if win then iprop(∃ vd, bView γ 1 vd) else iprop(True)) ⊢
    |={⊤}=> (rtRes γ P rt 1 ∗ ghostVar γ.rvs (1 : Qp).half ((C, writebackR W R), win)) := by
  iintro ⟨#Hci, ⟨%rd, %cm, %H, %Hw, Hcm, Hc⟩, Hview, Hrb, Hb, Hdep⟩
  unfold rtCore
  icases Hc with ⟨Hrd, Hrvs, Hcur, Hhist, Hrtx, Hwg, %Hf, #Hha, #Hcv, Hpo, #Hauth, Hiv⟩
  obtain ⟨hRwf, hids, hHl, hHall, -⟩ := Hf
  -- `γ.rvs`
  imod ghostVar_update_halves ((C, writebackR W R), win) γ.rvs _ _ $$ Hrvs Hb with ⟨Hrvs, Hb⟩
  -- the layout: index 0, the window
  let rd' : RdSt := { rd with idx := 0, win := win }
  imod ghostVar_update rd' γ.rd rd $$ Hrd with Hrd
  -- the history
  have hfresh := fresh_next_ver H R.ver rd.idx hHall hver
  imod ghost_map_insert_persist (R.ver + W64 1, 0) (C, writebackR W R) hfresh $$ Hhist
    with ⟨Hhist, #Hnew⟩
  -- the cache's marks
  unfold cacheInv
  iinv Hci with ⟨%Cs, %k, %w0, >Hca, >#Hels, >Hcurinv, >Hcvw, >%Hcs, Hwin⟩ Hclose
  icombine Hcur Hcurinv gives %Hck
  have Hk := Hck.2
  simp only [Prod.mk.injEq] at Hk
  obtain ⟨rfl, rfl⟩ := Hk
  rw [Hw]
  imod ghostVar_update_halves (((R.ver + W64 1), 0), win) γ.cur _ _ $$ Hcur Hcurinv
    with ⟨Hcur, Hcurinv⟩
  have hcfresh := fresh_next_ver Cs R.ver rd.idx (fun k b h => Hcs.1 k b h) hver
  iclear Hwin
  -- the new state's facts
  have hR'wf : (writebackR W R).Wf := writebackR_wf W hRwf
  have hR'ids : idsOk P (writebackR W R).bks := idsOk_writebackR hW hids
  ihave #Hcv' : cacheValid γ P (C, writebackR W R) 0 $$ []
  · unfold cacheValid
    rw [show (C, writebackR W R).2.ver = R.ver + W64 1 from rfl]
    iintro !> %i %rv' %hi #Hh' _
    have : i = 0 := by omega
    subst this
    unfold histAt
    ihave %Hag := ghostMapElem_agree (R.ver + W64 1, 0) γ.hist _ _ _ _ $$ Hnew Hh'
    subst Hag
    ipureintro; rfl
  icases ownRB_rbAt _ _ $$ Hrb with ⟨%m, %Pb, Hrb, %Hok⟩
  -- close the cache's invariant (a window: the clients' share deposited, the state poisoned)
  have h1 : ∀ k' b, Cs.lookup k' = some b → keyLe k' (R.ver + W64 1, 0) :=
    fun k' b h => keyLe_next_ver (Hcs.1 k' b h) hver
  have h2 : Cs.lookup (R.ver + W64 1, 0) ≠ some false := by rw [hcfresh]; simp
  cases win
  · imod Hclose $$ [Hca Hcurinv Hcvw] with -
    · inext
      iexists Cs, (R.ver + W64 1, 0), false
      iframe; iframe #
      isplitr
      · ipureintro; first | exact ⟨h1, fun _ => h2⟩ | exact ⟨⟨h1, fun _ => h2⟩, trivial⟩
      ileft; ipureintro; trivial
    ihave Hpo' : (if false = true then poisonAt γ (R.ver + W64 1) 0 else iprop(True)) $$ []
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    imodintro
    iframe Hb
    unfold rtRes rtResAt rtRest rtCore
    iexists rd', (C, writebackR W R), H.insert (R.ver + W64 1, 0) (C, writebackR W R), m, Pb, cm
    simp only [rd']
    iframe
    iframe #
    isplitr
    · ipureintro; exact Hok
    isplitr
    · ipureintro
      refine ⟨hR'wf, hR'ids, GMap.lookup_insert _ _ _, ?_, fun _ => trivial⟩
      intro k rv' hk
      by_cases hkk : (R.ver + W64 1, 0) = k
      · subst hkk; exact keyLe_refl _
      · rw [GMap.lookup_insert_ne _ _ hkk] at hk; exact keyLe_next_ver (hHall k rv' hk) hver
    isplitr
    · rw [show (writebackR W R).ver = R.ver + W64 1 from rfl]; unfold histAt; iexact Hnew
    first
      | iapply (rtIntv_congr γ P 1 rd { rd with idx := 0, win := false } cm C rfl rfl rfl rfl rfl rfl)
          $$ Hiv
      | iapply (rtIntv_congr γ P 1 rd { rd with idx := 0, win := true } cm C rfl rfl rfl rfl rfl rfl)
          $$ Hiv
  · imod ghost_map_insert_persist (R.ver + W64 1, 0) false hcfresh $$ Hca with ⟨Hca, #Hpo⟩
    simp only [↓reduceIte]
    icases Hdep with ⟨%vd, Hdep⟩
    ihave #Hels' : [∗map] k' ↦ b ∈ Cs.insert (R.ver + W64 1, 0) false,
        ghostMapElem γ.cached k' DFrac.discard b $$ []
    · iapply (BigSepM.bigSepM_insert_elim (M := GMap (w64 × Nat)) (m := Cs)
        (Φ := fun k b => ghostMapElem (GF := GF) γ.cached k DFrac.discard b)
        (i := (R.ver + W64 1, 0)) (x := false)) $$ Hpo Hels
    imod Hclose $$ [Hca Hcurinv Hcvw Hdep] with -
    · inext
      iexists Cs.insert (R.ver + W64 1, 0) false, (R.ver + W64 1, 0), true
      iframe Hca Hcurinv Hcvw
      iframe #
      isplitr
      · ipureintro
        constructor
        · intro k' b h
          by_cases hk : k' = (R.ver + W64 1, 0)
          · subst hk; exact keyLe_refl _
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at h; exact h1 k' b h
        · intro h; cases h
      iright; iexists vd; iexact Hdep
    ihave Hpo' : (if true = true then poisonAt γ (R.ver + W64 1) 0 else iprop(True)) $$ []
    · simp only [↓reduceIte]; unfold poisonAt; iexact Hpo
    imodintro
    iframe Hb
    unfold rtRes rtResAt rtRest rtCore
    iexists rd', (C, writebackR W R), H.insert (R.ver + W64 1, 0) (C, writebackR W R), m, Pb, cm
    simp only [rd']
    iframe
    iframe #
    isplitr
    · ipureintro; exact Hok
    isplitr
    · ipureintro
      refine ⟨hR'wf, hR'ids, GMap.lookup_insert _ _ _, ?_, fun _ => trivial⟩
      intro k rv' hk
      by_cases hkk : (R.ver + W64 1, 0) = k
      · subst hkk; exact keyLe_refl _
      · rw [GMap.lookup_insert_ne _ _ hkk] at hk; exact keyLe_next_ver (hHall k rv' hk) hver
    isplitr
    · rw [show (writebackR W R).ver = R.ver + W64 1 from rfl]; unfold histAt; iexact Hnew
    first
      | iapply (rtIntv_congr γ P 1 rd { rd with idx := 0, win := false } cm C rfl rfl rfl rfl rfl rfl)
          $$ Hiv
      | iapply (rtIntv_congr γ P 1 rd { rd with idx := 0, win := true } cm C rfl rfl rfl rfl rfl rfl)
          $$ Hiv

/-- After the write-back of `W`: the new version's state, the view updated (the clients' whole
share and the batch lock's quarter); with `win`, the window opens (the clients' share stays in
`cacheInv`). -/
theorem rtRes_wb_close (γ : BNames) (P : BParams) (rt : Loc) (W : WBuf) (C : Data) (R : RBuf)
    (vd : VData) (win : Bool) (hW : idsOk P W.bks) (hver : uint.Z R.ver + 1 < 2 ^ 64) :
    cacheInv (GF := GF) γ ∗ rtWb γ P rt C R ∗ ownRB (rbufOf (baseOf rt)) (writebackR W R) ∗
      ghostVar γ.rvs (1 : Qp).half ((C, R), false) ∗
      ghostVar γ.view (1 : Qp).half.half (vData P (C, R)) ∗ bView γ 1 vd ⊢
    |={⊤}=> (rtRes γ P rt 1 ∗ ghostVar γ.rvs (1 : Qp).half ((C, writebackR W R), win) ∗
      ghostVar γ.view (1 : Qp).half.half (vData P (C, writebackR W R)) ∗
      (if win then iprop(True) else bView γ 1 (vData P (C, writebackR W R)))) := by
  iintro ⟨#Hci, Hwb, Hrb, Hb, Hvq, Hbv⟩
  unfold rtWb rtRest
  icases Hwb with ⟨%rd, %cm, %H, %Hw, Hcm, Hvr, Hcore⟩
  unfold bView
  icases Hbv with ⟨Hvc, Hcw⟩
  imod view_upd3 γ _ _ _ (vData P (C, writebackR W R)) $$ [Hvr Hvq Hvc] with ⟨Hvr, Hvq, Hvc⟩
  · iframe
  cases win
  · imod wb_core γ P rt W C R false hW hver $$ [Hcm Hcore Hvr Hrb Hb] with ⟨Hres, Hb⟩
    · iframe #; iframe
      isplitr
      · ipureintro; exact Hw
      simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    imodintro
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  · imod wb_core γ P rt W C R true hW hver $$ [Hcm Hcore Hvr Hrb Hb Hvc Hcw] with ⟨Hres, Hb⟩
    · iframe #; iframe
      isplitr
      · ipureintro; exact Hw
      simp only [↓reduceIte]
      iexists _
      unfold bView
      iframe
    imodintro
    simp only [↓reduceIte]
    iframe

/-- After a write-back of `W` that does not change the readers' view (the write buffer only in
the hook's buckets): the new version's state, no window, the view (and the clients' share)
untouched. -/
theorem rtRes_wb_close_same (γ : BNames) (P : BParams) (rt : Loc) (W : WBuf) (C : Data)
    (R : RBuf) (hW : idsOk P W.bks) (hver : uint.Z R.ver + 1 < 2 ^ 64)
    (hsame : vData P (C, writebackR W R) = vData P (C, R)) :
    cacheInv (GF := GF) γ ∗ rtWb γ P rt C R ∗ ownRB (rbufOf (baseOf rt)) (writebackR W R) ∗
      ghostVar γ.rvs (1 : Qp).half ((C, R), false) ⊢
    |={⊤}=> (rtRes γ P rt 1 ∗ ghostVar γ.rvs (1 : Qp).half ((C, writebackR W R), false)) := by
  iintro ⟨#Hci, Hwb, Hrb, Hb⟩
  unfold rtWb rtRest
  icases Hwb with ⟨%rd, %cm, %H, %Hw, Hcm, Hvr, Hcore⟩
  rw [← hsame] at *
  iapply wb_core γ P rt W C R false hW hver $$ [Hcm Hcore Hvr Hrb Hb]
  iframe #; iframe
  isplitr
  · ipureintro; exact Hw
  simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

/-! ## The commit -/

/-- The commit begins: the shared transaction's fields and the read buffer out (for
`readTx.reset`), the interval ended (`wgOpen 1` deposited in its protocol) and the rollback
goroutine's resources (unless no interval was open: then the transaction is null and the
backend stopped). -/
theorem rtRes_cm_open (γ : BNames) (P : BParams) (rt : Loc) (C : Data) (R : RBuf) (win : Bool) :
    rtRes (GF := GF) γ P rt 1 ∗ ghostVar γ.rvs (1 : Qp).half ((C, R), win) ⊢
    |={⊤}=> ∃ (rtx : Loc) (cm : GoMap) (wg : Loc),
      rtxOf (baseOf rt) ↦ rtx ∗ rbktOf (baseOf rt) ↦ cm ∗ rwgOf (baseOf rt) ↦ wg ∗
      ownRB (rbufOf (baseOf rt)) R ∗
      (rollbackRes γ rtx wg ∨ (⌜rtx = Loc.null⌝ ∗ bStopped γ)) ∗
      rtCm γ P C R win ∗ ghostVar γ.rvs (1 : Qp).half ((C, R), win) := by
  unfold rtRes rtResAt rtRest rtCore
  iintro ⟨⟨%rd, %rv, %H, %m, %Pb, %cm, Hrb, %Hok, Hcm, Hview, Hrd, Hrvs, Hcur, Hhist, Hrtx, Hwg,
    %Hf, #Hha, #Hcv, Hpo, #Hauth, Hiv⟩, Hb⟩
  icombine Hrvs Hb gives %Heq0
  have Heq := Heq0.2
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, Hw⟩ := Heq
  ihave Hown := rbAt_ownRB _ m Pb R Hok $$ Hrb
  iexists rd.rtx, cm, rd.wg
  iframe Hrtx Hcm Hwg Hown Hb
  -- the interval ends
  unfold rtCm
  unfold rtIntv
  rw [← Hw]
  cases hl : rd.live
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hiv with ⟨%Hnull, #Hst⟩
    imodintro
    isplitr
    · iright; iframe #; ipureintro; exact Hnull
    iexists rd, H
    iframe; iframe #
    ipureintro; exact ⟨rfl, Hf⟩
  simp only [↓reduceIte]
  icases Hiv with ⟨Hlive, #Hsnap, -, #Hwgi, Hwo, Htk⟩
  unfold wgInv
  icases Hwgi with ⟨%γwg, #Hisw, #Hi, -⟩
  iinv Hi with >Hbody Hclose
  all_goals try (exact fun _ _ => CoPset.mem_full)
  iunfold wgBody at Hbody
  icases Hbody with (⟨%n, %outs, %pool, Hwgo, Hoa, Hpool, Htoks, %Hn, Hwt⟩ | ⟨Hoa, Hwo', -⟩)
  · icases Hwt with (Hwt | Hwo')
    · imod Hclose $$ [Hwgo Hoa Hpool Htoks Hwo] with -
      · inext
        unfold wgBody
        ileft
        iexists n, outs, pool
        iframe
        isplitr
        · ipureintro; exact Hn.1
        ipureintro; exact Hn.2
      imodintro
      isplitr [Hrd Hview Hrvs Hcur Hhist Hpo]
      · ileft
        unfold rollbackRes
        iexists γwg, rd.γw, rd.γo, rd.γt, C
        iframe; iframe #
      iexists rd, H
      iframe; iframe #
      ipureintro; exact ⟨rfl, Hf⟩
    · unfold wgOpen
      ihave %Hv := ghostVar_valid_2 rd.γw () 1 () 1 $$ Hwo Hwo'
      exfalso; have := Hv.1; simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at this; grind
  · unfold wgOpen
    ihave %Hv := ghostVar_valid_2 rd.γw () 1 () 1 $$ Hwo Hwo'
    exfalso; have := Hv.1; simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at this; grind

/-- A new interval for the bbolt read transaction `tx` over `D` (with a fresh buckets map and
`WaitGroup`), or none at a stop: its invariants and `readTx.mu`'s whole share. -/
theorem new_intv (γ : BNames) (P : BParams) (cm : GoMap) (D : Data) (tx wg : Loc) (idx : Nat)
    (stop : Bool) :
    (if stop then iprop(⌜tx = Loc.null⌝ ∗ bStopped γ)
       else iprop(txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx)) ∗
      cm ↦$ (∅ : GMap w64 Loc) ∗ wg ↦ (zero_val sync.WaitGroup) ∗
      ownTokAuthDfrac (GF := GF) γ.rdt DFrac.discard rdMax ⊢
    |={⊤}=> ∃ rd' : RdSt, ⌜rd'.rtx = tx ∧ rd'.wg = wg ∧ rd'.idx = idx ∧ rd'.win = false⌝ ∗
      rtIntv γ P 1 rd' cm D := by
  iintro ⟨Hn, Hcm, Hwg, #Hauth⟩
  cases stop
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hn with ⟨Hlive, #Hsnap, Hst⟩
    imod sync.init_WaitGroup (bN.@"wg") wg $$ Hwg with ⟨%γwg, #Hisw, Hctr, Hwt⟩
    imod ghost_map_alloc_empty (K := Nat) (V := Qp) with ⟨%γo, Hoa⟩
    imod ghostVar_alloc () with ⟨%γw, Hwo⟩
    imod ghostVar_alloc () with ⟨%γt, Htk⟩
    imod ownToks_0 γ.rdt with H0
    ihave Hlive2 : txLive tx ((1 : Qp).half + (1 : Qp).half) $$ [Hlive]
    · rw [Qp.half_add_half]; iexact Hlive
    icases ((txLive_fractional tx).fractional (1 : Qp).half (1 : Qp).half).1 $$ Hlive2
      with ⟨Hl1, Hl2⟩
    imod inv_alloc (bN.@"wgi") ⊤ (wgBody γ tx γwg γw γo γt) $$ [Hctr Hoa Hl2 H0 Hwt] with #Hi
    · inext
      unfold wgBody
      ileft
      iexists W32 0, ∅, (1 : Qp).half
      rw [show sint.nat (W32 0) = 0 from rfl]
      iframe
      isplitr
      · ipureintro; rw [GMap.map_size_empty]; decide
      ipureintro
      rw [qsum_empty]; show (1 : Qp).val / 2 + 0 = 1 / 2; rw [Qp.val_one]; grind
    imod inv_alloc (bN.@"intv") ⊤ iprop(∃ (M : GMap w64 Loc) (qm : Rat), □ cmFacts P tx D M ∗
        ⌜0 ≤ qm ∧ qm ≤ 1⌝ ∗ mapPart cm qm M ∗ tokPart γ (1 - qm)) $$ [Hcm] with #Hiv1
    · inext
      iexists ∅, 1
      ihave #Hf := cmFacts_empty (GF := GF) P tx D
      iframe #
      unfold mapPart tokPart
      rw [dif_pos (show (0 : Rat) < 1 by decide), dif_neg (show ¬ (0 : Rat) < 1 - 1 by grind)]
      isplitr
      · ipureintro; decide
      iframe
    imod inv_alloc (bN.@"stats") ⊤ iprop(rtxStats tx ∨ ghostVar γ.txb 1 ()) $$ [Hst] with #Hiv2
    · inext; ileft; iexact Hst
    imodintro
    iexists (⟨tx, wg, γw, γo, γt, idx, false, true⟩ : RdSt)
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    unfold rtIntv
    simp only [↓reduceIte]
    iframe; iframe #
    isplitr
    · unfold intvInv; iframe #
    isplitl []
    · imodintro; unfold wgInv; iexists γwg; iframe #
    unfold wgOpen; iframe
  · simp only [↓reduceIte]
    icases Hn with ⟨%Hnull, #Hst⟩
    imodintro
    iexists (⟨tx, wg, γ.rd, γ.rd, γ.rd, idx, false, false⟩ : RdSt)
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    unfold rtIntv
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe #
    ipureintro; exact Hnull

/-- The commit ends: the reset fields and read buffer back, the new bbolt read transaction
`tx` over the new committed data `C'` (a new interval: its `WaitGroup`, buckets map and
invariants), or, at a stop, none and `bStopped`; the state `(ver, i + 1)` recorded, the view
updated (the batch lock's quarter; out of a window, the clients' whole share, back from
`cacheInv`). Not in a window, the view must be unchanged. -/
theorem rtRes_cm_close (γ : BNames) (P : BParams) (rt : Loc) (C C' : Data) (R : RBuf)
    (win stop : Bool) (tx : Loc) (cm : GoMap) (wg : Loc)
    (hview : win = false → vData P (C', R.reset) = vData P (C, R)) :
    cacheInv (GF := GF) γ ∗ rtCm γ P C R win ∗ ghostVar γ.rvs (1 : Qp).half ((C, R), win) ∗
      ghostVar γ.view (1 : Qp).half.half (vData P (C, R)) ∗
      rtxOf (baseOf rt) ↦ tx ∗ rbktOf (baseOf rt) ↦ cm ∗ cm ↦$ (∅ : GMap w64 Loc) ∗
      rwgOf (baseOf rt) ↦ wg ∗ wg ↦ (zero_val sync.WaitGroup) ∗
      ownRB (rbufOf (baseOf rt)) R.reset ∗
      (if stop then iprop(⌜tx = Loc.null⌝ ∗ bStopped γ)
       else iprop(txLive tx 1 ∗ rtxSnap tx C' ∗ rtxStats tx)) ⊢
    |={⊤}=> (rtRes γ P rt 1 ∗ ghostVar γ.rvs (1 : Qp).half ((C', R.reset), false) ∗
      ghostVar γ.view (1 : Qp).half.half (vData P (C', R.reset)) ∗
      (if win then bView γ 1 (vData P (C', R.reset)) else iprop(True))) := by
  iintro ⟨#Hci, Hcm, Hb, Hvq, Htx, Hcmf, Hcm0, Hwgf, Hwg0, Hrb, Hn⟩
  unfold rtCm
  icases Hcm with ⟨%rd, %H, Hrd, Hvr, Hrvs, Hcur, Hhist, %Hf, #Hha, #Hcv, Hpo, #Hauth⟩
  obtain ⟨Hw, hRwf, hids, hHl, hHall, hwin0⟩ := Hf
  -- the new interval
  imod new_intv γ P cm C' tx wg (rd.idx + 1) stop $$ [Hn Hcm0 Hwg0] with ⟨%rd', %Hrd', Hiv⟩
  · iframe; iframe #
  obtain ⟨hr1, hr2, hr3, hr4⟩ := Hrd'
  -- `γ.rvs`, the layout, the history
  imod ghostVar_update_halves ((C', R.reset), false) γ.rvs _ _ $$ Hrvs Hb with ⟨Hrvs, Hb⟩
  imod ghostVar_update rd' γ.rd rd $$ Hrd with Hrd
  have hfresh := fresh_next_idx H R.ver rd.idx (fun k x h => hHall k x h)
  imod ghost_map_insert_persist (R.ver, rd.idx + 1) (C', R.reset) hfresh $$ Hhist
    with ⟨Hhist, #Hnew⟩
  -- the cache's marks
  unfold cacheInv
  iinv Hci with ⟨%Cs, %k, %w0, >Hca, >#Hels, >Hcurinv, >Hcvw, >%Hcs, Hwin⟩ Hclose
  icombine Hcur Hcurinv gives %Hck
  have Hk := Hck.2
  simp only [Prod.mk.injEq] at Hk
  obtain ⟨rfl, rfl⟩ := Hk
  imod ghostVar_update_halves ((R.ver, rd.idx + 1), false) γ.cur _ _ $$ Hcur Hcurinv
    with ⟨Hcur, Hcurinv⟩
  have hcfresh := fresh_next_idx Cs R.ver rd.idx (fun k b h => Hcs.1 k b h)
  have h1 : ∀ k' b, Cs.lookup k' = some b → keyLe k' (R.ver, rd.idx + 1) :=
    fun k' b h => keyLe_next_idx (Hcs.1 k' b h)
  have h2 : Cs.lookup (R.ver, rd.idx + 1) ≠ some false := by rw [hcfresh]; simp
  have hR'wf : R.reset.Wf := RBuf.reset_wf hRwf
  have hR'ids : idsOk P R.reset.bks := idsOk_reset hids
  have hH' : ∀ k rv', (H.insert (R.ver, rd.idx + 1) (C', R.reset)).lookup k = some rv' →
      keyLe k (R.ver, rd.idx + 1) := by
    intro k rv' hk
    by_cases hkk : (R.ver, rd.idx + 1) = k
    · subst hkk; exact keyLe_refl _
    · rw [GMap.lookup_insert_ne _ _ hkk] at hk; exact keyLe_next_idx (hHall k rv' hk)
  icases ownRB_rbAt _ _ $$ Hrb with ⟨%m, %Pb, Hrb, %Hok⟩
  cases win
  · -- not in a window: the view unchanged; the marks at this version still read right
    ihave #Hcv' : cacheValid γ P (C', R.reset) (rd.idx + 1) $$ []
    · unfold cacheValid
      rw [show (C', R.reset).2.ver = R.ver from rfl]
      iintro !> %i %rv' %hi #Hh #Hc
      by_cases hii : i = rd.idx + 1
      · subst hii
        unfold histAt
        ihave %Hag := ghostMapElem_agree (R.ver, rd.idx + 1) γ.hist _ _ _ _ $$ Hnew Hh
        subst Hag
        ipureintro; rfl
      · ihave %Hold := Hcv $$ %i %rv' %(by omega) Hh Hc
        ipureintro
        exact vData_rebase P C C' rv'.2 R Hold (hview rfl)
    imod Hclose $$ [Hca Hcurinv Hcvw] with -
    · inext
      iexists Cs, (R.ver, rd.idx + 1), false
      iframe; iframe #
      isplitr
      · ipureintro; first | exact ⟨h1, fun _ => h2⟩ | exact ⟨⟨h1, fun _ => h2⟩, trivial⟩
      ileft; ipureintro; trivial
    imodintro
    rw [hview rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hb Hvq
    unfold rtRes rtResAt rtRest rtCore
    iexists rd', (C', R.reset), H.insert (R.ver, rd.idx + 1) (C', R.reset), m, Pb, cm
    rw [hr1, hr2, hr3, hr4, show R.reset.ver = R.ver from rfl, hview rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe; iframe #
    isplitr
    · ipureintro; exact Hok
    isplitr
    · ipureintro
      exact ⟨hR'wf, hR'ids, GMap.lookup_insert _ _ _, hH', fun h => by cases h⟩
    unfold histAt; iexact Hnew
  · -- a window: the clients' share back from the cache's invariant, the view updated
    icases Hwin with (>%Hbad | ⟨%vd, >Hbv⟩)
    · cases Hbad
    unfold bView
    icases Hbv with ⟨Hvc, Hcw⟩
    ihave #Hpo' : poisonAt γ R.ver rd.idx $$ [Hpo]
    · simp only [↓reduceIte]; iexact Hpo
    ihave #Hcv' : cacheValid γ P (C', R.reset) (rd.idx + 1) $$ []
    · unfold cacheValid
      rw [show (C', R.reset).2.ver = R.ver from rfl]
      iintro !> %i %rv' %hi #Hh #Hc
      by_cases hii : i = rd.idx + 1
      · subst hii
        unfold histAt
        ihave %Hag := ghostMapElem_agree (R.ver, rd.idx + 1) γ.hist _ _ _ _ $$ Hnew Hh
        subst Hag
        ipureintro; rfl
      · have hi0 : i = rd.idx := by have := hwin0 rfl; omega
        subst hi0
        unfold poisonAt cachedAt
        ihave %Hbad := ghostMapElem_agree (R.ver, rd.idx) γ.cached _ _ _ _ $$ Hpo' Hc
        cases Hbad
    imod view_upd3 γ _ _ _ (vData P (C', R.reset)) $$ [Hvr Hvq Hvc] with ⟨Hvr, Hvq, Hvc⟩
    · iframe
    imod Hclose $$ [Hca Hcurinv Hcvw] with -
    · inext
      iexists Cs, (R.ver, rd.idx + 1), false
      iframe; iframe #
      isplitr
      · ipureintro; first | exact ⟨h1, fun _ => h2⟩ | exact ⟨⟨h1, fun _ => h2⟩, trivial⟩
      ileft; ipureintro; trivial
    imodintro
    simp only [↓reduceIte]
    iframe Hb Hvq
    isplitr [Hvc Hcw]
    · unfold rtRes rtResAt rtRest rtCore
      iexists rd', (C', R.reset), H.insert (R.ver, rd.idx + 1) (C', R.reset), m, Pb, cm
      rw [hr1, hr2, hr3, hr4, show R.reset.ver = R.ver from rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe; iframe #
      isplitr
      · ipureintro; exact Hok
      isplitr
      · ipureintro
        exact ⟨hR'wf, hR'ids, GMap.lookup_insert _ _ _, hH', fun h => by cases h⟩
      unfold histAt; iexact Hnew
    iframe

/-- The rollback goroutine's `wg.Wait()`: once every reader of the ended interval is done, the
whole bbolt read transaction (for `Rollback`). -/
theorem wp_rollback_Wait (γ : BNames) (rtx wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rollbackRes γ rtx wg }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); ∃ D : Data, txLive rtx 1 ∗ rtxSnap rtx D }} := by
  iintro %Φ ⟨#Hsync, Hr⟩ HΦ
  unfold rollbackRes
  icases Hr with ⟨%γwg, %γw, %γo, %γt, %D, #Hisw, #Hi, Hwt, Htk, Hl, #Hsnap⟩
  -- register as the waiter
  iapply fupd_wp
  imod fupd_mask_subseteq (show (↑(bN.@"wg") : CoPset) ⊆ ⊤ from fun _ _ => CoPset.mem_full)
    with Hmask
  imod sync.alloc_wait_token wg γwg (bN.@"wg") 0 (by decide) $$ Hisw Hwt with ⟨Hwt, Htok⟩
  imod Hmask with -
  imodintro
  iapply sync.WaitGroup.wp_Wait wg γwg (bN.@"wg") $$ [Htok] [Hl Htk Hwt HΦ]
  · iframe #; iframe
  iinv Hi with >Hb Hclose
  all_goals try (exact fun _ h => ⟨CoPset.mem_full, fun h' => by
    exact (sync.wg_mask_ndot_ne bN "wg" "wgi" (by decide)) h' |>.2 h⟩)
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold wgBody at Hb
  icases Hb with (⟨%n, %outs, %pool, Hwgo, Hoa, Hpool, Htoks, %Hn, Hwo⟩ | ⟨Hoa, Hwo, Htk'⟩)
  rotate_left
  · ihave %Hv := ghostVar_valid_2 γt () 1 () 1 $$ Htk Htk'
    exfalso; have := Hv.1; simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at this; grind
  iexists n
  iframe Hwgo
  iintro %Hz Hwgo
  imod Hmask with -
  icases Hwo with (Hw0 | Hwo)
  · rw [sync.ownWaitGroupWaiters_unseal]
    unfold sync.ownWaitGroupWaitersDef
    icombine Hwt Hw0 gives %Hbad
    exfalso; have := Hbad.2; simp at this
  have hsz : GMap.size outs = 0 := by omega
  have hout : outs = ∅ := GMap.map_size_empty_inv outs hsz
  subst hout
  have hpool : pool = (1 : Qp).half := by
    apply Subtype.ext
    have := Hn.2; rw [qsum_empty] at this
    show pool.val = (1 : Qp).val / 2
    rw [Qp.val_one]; grind
  subst hpool
  imod Hclose $$ [Hoa Hwo Htk] with -
  · inext
    unfold wgBody
    iright
    iframe
  imodintro
  iintro -
  iapply HΦ
  iexists D
  iframe #
  iapply ((txLive_fractional rtx).fractional (1 : Qp).half (1 : Qp).half |>.2).trans
    (by rw [Qp.half_add_half])
  iframe

end lemmas

end backend
end EtcdGrove
end Perennial
