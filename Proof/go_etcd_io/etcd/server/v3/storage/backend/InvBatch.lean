/-
The batch transaction below the buffers (`batch_tx.go`'s `batchTx` methods): the writer's
fields and bbolt's write transaction for a state `st` (`btW`), which `batchTx.UnsafePut` and
the others change before `batchTxBuffered`'s wrapper updates the write buffer (in between,
`sessWf` does not hold: bbolt's writer has the entry, the write buffer not yet). And what a
batch transaction's method reads of the backend (`isBackend_bt`). Lean-first (no Rocq
counterpart); see `InvBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BatchLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `int64` is not an interface type (Perennial has the instance for `go.Named _ _`, which
`go.int64` is, but instance search does not unfold it): what `MethodResolve` needs of
`time.Duration` (underlying `int64`) for `d.Seconds()`. -/
instance notInterface_int64 [GooseExts] : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩

/-- The batch transaction's writer for `st`: its `tx` and `pending` fields and bbolt's write
transaction `st.tx` (begun at `st.C`, contents `st.S`). The rest of `st` is not its. -/
def btW (γ : BNames) (t : Loc) (st : BSess) : IProp GF :=
  iprop(txFOf t ↦ st.tx ∗ pendOf t ↦ st.pend ∗ ownWTx st.tx γ.db st.C st.S)

/-- What a batch transaction's method reads of its backend: the backend field, the logger (not
nil), the batch limit, the hooks, the batch lock, bbolt's database. -/
theorem isBackend_bt (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) :
    isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      ∃ (db lg : Loc) (h : GoInterface), beOf t ↦□ b ∗ bF go!"lg" b ↦□ lg ∗ ⌜lg ≠ Loc.null⌝ ∗
        bF go!"batchLimit" b ↦□ P.limit ∗ bF go!"hooks" b ↦□ h ∗ hooksSpec γ P Pk b t h ∗
        sync.isMutex (muOf t) (batchFree γ P W Pk b t) ∗ isDB db ∗ ⌜P.Wf⌝ := by
  iintro ⟨#Hb, #Ht⟩
  unfold isBackend
  icases Hb with ⟨%t', %rt, %tm, %db, %lg, %h, #Ht', #-, #Hl, #Hlg, %Hlgn, #Hh, #Hbe, #-,
    #Hhs, #Hm, #-, #-, #-, #-, #-, #-, #Hdb, %HP⟩
  icombine Ht Ht' gives %Heq
  subst Heq
  iexists db, lg, h
  iframe #
  ipureintro
  exact ⟨Hlgn, HP⟩

/-- What the backend's own methods read of it: the logger (not nil), the metrics, the batch
transaction and the read transaction. -/
theorem isBackend_b (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) :
    isBackend γ P W Pk b ⊢
      ∃ (t rt db lg : Loc), bF go!"batchTx" b ↦□ t ∗ bF go!"readTx" b ↦□ rt ∗
        bF go!"lg" b ↦□ lg ∗ ⌜lg ≠ Loc.null⌝ ∗ metricsInv b ∗ beOf t ↦□ b ∗
        sync.isMutex (muOf t) (batchFree γ P W Pk b t) ∗
        sync.isRWMutexGuard (rmuOf (baseOf rt)) (rtRes γ P rt) ∗
        sync.isRWMutexGuard (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
        isDB db ∗ cacheInv γ ∗ ⌜P.Wf⌝ := by
  iintro #Hb
  unfold isBackend
  icases Hb with ⟨%t, %rt, %tm, %db, %lg, %h, #Ht, #Hrt, #Hl, #Hlg, %Hlgn, #Hh, #Hbe, #-,
    #Hhs, #Hm, #Hrm, #-, #-, #Hci, #Hmi, #Hmu, #Hdb, %HP⟩
  iexists t, rt, db, lg
  iframe #
  ipureintro
  exact ⟨Hlgn, HP⟩

/-- `atomic.StoreInt64` on one of the backend's metrics fields. -/
theorem wp_metricStore (b : Loc) (f : GoString) (v : w64)
    (hf : f = go!"size" ∨ f = go!"sizeInUse" ∨ f = go!"commits" ∨ f = go!"openReadTxN") :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ metricsInv b }}
      (App (App (Val (@! _root_.Perennial.sync.atomic.StoreInt64)) (Val #(bF f b))) (Val #v))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hat, #Hm⟩ HΦ
  iapply (sync.atomic.wp_StoreInt64 (bF f b) v) $$ Hat
  unfold metricsInv
  iinv Hm with >Hi Hclose
  icases Hi with ⟨%a, %c, %d, %e, Ha, Hc, Hd, He⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  rcases hf with rfl | rfl | rfl | rfl
  · iexists a
    iframe Ha
    iintro Ha
    imod Hmask with -
    imod Hclose $$ [Ha Hc Hd He] with -
    · inext; iexists v, c, d, e; iframe
    imodintro
    iapply HΦ
    itrivial
  · iexists c
    iframe Hc
    iintro Hc
    imod Hmask with -
    imod Hclose $$ [Ha Hc Hd He] with -
    · inext; iexists a, v, d, e; iframe
    imodintro
    iapply HΦ
    itrivial
  · iexists d
    iframe Hd
    iintro Hd
    imod Hmask with -
    imod Hclose $$ [Ha Hc Hd He] with -
    · inext; iexists a, c, v, e; iframe
    imodintro
    iapply HΦ
    itrivial
  · iexists e
    iframe He
    iintro He
    imod Hmask with -
    imod Hclose $$ [Ha Hc Hd He] with -
    · inext; iexists a, c, d, v; iframe
    imodintro
    iapply HΦ
    itrivial

/-- `atomic.AddInt64(&b.commits, v)`. -/
theorem wp_commitsAdd (b : Loc) (v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ metricsInv b }}
      (App (App (Val (@! _root_.Perennial.sync.atomic.AddInt64)) (Val #(bF go!"commits" b))) (Val #v))
    {{ (n : w64), RET #n; True }} := by
  iintro %Φ ⟨#Hat, #Hm⟩ HΦ
  iapply (sync.atomic.wp_AddInt64 (bF go!"commits" b) v) $$ Hat
  unfold metricsInv
  iinv Hm with >Hi Hclose
  icases Hi with ⟨%a, %c, %d, %e, Ha, Hc, Hd, He⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists d
  iframe Hd
  iintro Hd
  imod Hmask with -
  imod Hclose $$ [Ha Hc Hd He] with -
  · inext; iexists a, c, d + v, e; iframe
  imodintro
  iapply HΦ
  itrivial

/-- A session's operation (one more pending operation, at most one more entry per bucket of the
write buffer, the committed data, the read buffer and the counters unchanged) keeps the batch
lock's ghost share; one that leaves the hook's own keys and the tracked buckets, without the
client's halves of them. -/
theorem batchGhost_step (γ : BNames) (P : BParams) {st st' : BSess} (hC : st'.C = st.C)
    (hR : st'.R = st.R) (hc : st'.cnt = st.cnt) (hp : sint.nat st'.pend = sint.nat st.pend + 1)
    (hW : ∀ i, (bkOf st'.W.bks i).length ≤ (bkOf st.W.bks i).length + 1)
    (hS : hkData P st'.S = hkData P st.S) (hB : rbData P st'.S = rbData P st.S) :
    batchGhost (GF := GF) γ P st ⊢ batchGhost γ P st' := by
  unfold batchGhost batchGhostAt
  rw [hC, hR, trkHalf_eq γ P (S := st.S) (S' := st'.S) hS hB]
  iintro ⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, %Hok⟩
  iframe Hv
  iexists n, w, u
  iframe
  ipureintro
  exact bgOk_step Hok hR hc hp hW

/-- A session's operation on the bucket `n` (as `batchGhost_step`, the hook's own keys
unchanged): with the client's half of the tracked buckets if `n` is one (`rbPut`), both halves
updated to the new contents; else they are unchanged. -/
theorem batchGhost_step_rb (γ : BNames) (P : BParams) {st st' : BSess} (hC : st'.C = st.C)
    (hR : st'.R = st.R) (hc : st'.cnt = st.cnt) (hp : sint.nat st'.pend = sint.nat st.pend + 1)
    (hW : ∀ i, (bkOf st'.W.bks i).length ≤ (bkOf st.W.bks i).length + 1) (n : GoString)
    (hS : hkData P st'.S = hkData P st.S)
    (hB : P.RB n = false → rbData P st'.S = rbData P st.S) :
    ⊢ batchGhost (GF := GF) γ P st -∗ rbPut γ P n st.S ==∗
      batchGhost γ P st' ∗ rbPut γ P n st'.S := by
  unfold rbPut
  cases hb : P.RB n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro Hg -
    ihave Hg := batchGhost_step γ P hC hR hc hp hW hS (hB hb) $$ Hg
    imodintro
    iframe Hg
  · simp only [↓reduceIte]
    unfold batchGhost batchGhostAt rbOwn trkHalf
    rw [hC, hR, hS]
    iintro ⟨Hv, %n0, %w, %u, Hr, Ha, Hm, Hu, Ho, ⟨Hk, Hb⟩, %Hok⟩ Hc
    imod ghostVar_update_halves (rbData P st'.S) γ.rbk _ _ $$ Hb Hc with ⟨Hb, Hc⟩
    imodintro
    isplitl [Hv Hr Ha Hm Hu Ho Hk Hb]
    · iframe Hv
      iexists n0, w, u
      iframe
      ipureintro
      exact bgOk_step Hok hR hc hp hW
    · iexact Hc

/-- A put of key `k` in bucket `n` (as `batchGhost_step`): with the client's half of the hook's
own keys if `k` is one (`hkPut`), and of the tracked buckets if `n` is one (`rbPut`), both halves
updated to the new contents; else they are unchanged. -/
theorem batchGhost_step_put (γ : BNames) (P : BParams) {st st' : BSess} (hC : st'.C = st.C)
    (hR : st'.R = st.R) (hc : st'.cnt = st.cnt) (hp : sint.nat st'.pend = sint.nat st.pend + 1)
    (hW : ∀ i, (bkOf st'.W.bks i).length ≤ (bkOf st.W.bks i).length + 1) (n k : GoString)
    (hS : P.hk n k = false → hkData P st'.S = hkData P st.S)
    (hB : P.RB n = false → rbData P st'.S = rbData P st.S) :
    ⊢ batchGhost (GF := GF) γ P st -∗ hkPut γ P n k st.S -∗ rbPut γ P n st.S ==∗
      batchGhost γ P st' ∗ hkPut γ P n k st'.S ∗ rbPut γ P n st'.S := by
  unfold batchGhost batchGhostAt trkHalf
  rw [hC, hR]
  iintro ⟨Hv, %n0, %w, %u, Hr, Ha, Hm, Hu, Ho, ⟨Hk, Hb⟩, %Hok⟩ Hhp Hrp
  ihave Hk2 : iprop(|==> (ghostVar γ.hkd (1 : Qp).half (hkData P st'.S) ∗ hkPut γ P n k st'.S))
    $$ [Hk Hhp]
  · unfold hkPut
    cases hk : P.hk n k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hS hk]
      imodintro
      iframe Hk
    · simp only [↓reduceIte]
      unfold hkOwn
      iapply ghostVar_update_halves (hkData P st'.S) γ.hkd _ _ $$ Hk Hhp
  ihave Hb2 : iprop(|==> (ghostVar γ.rbk (1 : Qp).half (rbData P st'.S) ∗ rbPut γ P n st'.S))
    $$ [Hb Hrp]
  · unfold rbPut
    cases hb : P.RB n
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hB hb]
      imodintro
      iframe Hb
    · simp only [↓reduceIte]
      unfold rbOwn
      iapply ghostVar_update_halves (rbData P st'.S) γ.rbk _ _ $$ Hb Hrp
  imod Hk2 with ⟨Hk, Hhp⟩
  imod Hb2 with ⟨Hb, Hrp⟩
  imodintro
  iframe Hhp Hrp Hv
  iexists n0, w, u
  iframe
  ipureintro
  exact bgOk_step Hok hR hc hp hW

/-- The client's half of the hook's own keys agrees with the batch lock's state. -/
theorem batchLocked_hk (γ : BNames) (P : BParams) (b : Loc) (st : BSess)
    (d : GMap (GoString × GoString) GoString) :
    batchLocked (GF := GF) γ P b st ∗ hkOwn γ d ⊢
      batchLocked γ P b st ∗ hkOwn γ d ∗ ⌜d = hkData P st.S⌝ := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt hkOwn trkHalf
  iintro ⟨⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, %n0, %w, %u, Hr, Ha, Hm, Hu, Ho, ⟨Hk, Hb⟩, %Hok⟩, %Hwf⟩,
    Hc⟩
  icombine Hc Hk gives %Heq
  iframe Hc
  isplitl
  · iexists t, db
    iframe
    iframe #
    ipureintro; exact ⟨Hok, Hwf⟩
  · ipureintro; exact Heq.2

/-- The client's half of the tracked buckets agrees with the batch lock's state (leases T3: `lessor.Revoke`'s
delete from the `Lease` bucket, `BackendBridge.lean`). -/
theorem batchLocked_rb (γ : BNames) (P : BParams) (b : Loc) (st : BSess)
    (r : GMap GoString BktData) :
    batchLocked (GF := GF) γ P b st ∗ rbOwn γ r ⊢
      batchLocked γ P b st ∗ rbOwn γ r ∗ ⌜r = rbData P st.S⌝ := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt rbOwn trkHalf
  iintro ⟨⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, %n0, %w, %u, Hr, Ha, Hm, Hu, Ho, ⟨Hk, Hb⟩, %Hok⟩, %Hwf⟩,
    Hc⟩
  icombine Hc Hb gives %Heq
  iframe Hc
  isplitl
  · iexists t, db
    iframe
    iframe #
    ipureintro; exact ⟨Hok, Hwf⟩
  · ipureintro; exact Heq.2

/-- The batch lock's ghost share bounds the buffers' buckets. -/
theorem batchGhostAt_bound (γ : BNames) (P : BParams) (st : BSess) (free : Bool) (hP : P.Wf)
    (hst : sessWf P st) :
    batchGhostAt (GF := GF) γ P st free ⊢
      ⌜∀ i, (bkOf st.R.bks i).length + (bkOf st.W.bks i).length < bufBound⌝ := by
  unfold batchGhostAt
  iintro ⟨-, %n, %w, %u, -, -, -, -, -, -, %Hok⟩
  ipureintro
  exact bgOk_bufBound hP hst Hok

/-- At a free lock, every put was written back. -/
theorem batchGhostAt_p0 (γ : BNames) (P : BParams) (st : BSess) :
    batchGhostAt (GF := GF) γ P st true ⊢ ⌜st.cnt.p0 = sint.nat st.pend⌝ := by
  unfold batchGhostAt
  iintro ⟨-, %n, %w, %u, -, -, -, -, -, -, %Hok⟩
  ipureintro
  exact (Hok.2.2.2.2.2.2.2.2.1 rfl).1

/-- The free lock's ghost share, taken by a session. -/
theorem batchGhostAt_take (γ : BNames) (P : BParams) (st : BSess) :
    batchGhostAt (GF := GF) γ P st true ⊢ batchGhost γ P st := by
  unfold batchGhost batchGhostAt
  iintro ⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, %Hok⟩
  iframe Hv
  iexists n, w, u
  iframe
  ipureintro
  unfold bgOk at Hok ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, h10⟩ := Hok
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by simp, h10⟩

/-- A slice a range of the writer returned, read under the batch lock in a state with the same
write transaction (`UnsafeRange`'s capability). -/
theorem batchLocked_rdB (γ : BNames) (P : BParams) (b : Loc) (st st' : BSess) (s : GoSlice)
    (v : GoString) :
    rdB st.tx s v ∗ batchLocked γ P b st' ∗ ⌜st'.tx = st.tx⌝ ⊢
      ∃ dq : DFrac, s ↦*{dq} v ∗ (s ↦*{dq} v -∗ batchLocked (GF := GF) γ P b st') := by
  iintro ⟨Hr, Hl, %Htx⟩
  unfold rdB
  icases Hr with (#Hs | #Hs)
  · iexists DFrac.discard
    iframe Hs
    iintro -
    iexact Hl
  · unfold batchLocked batchLockedAt batchPhys
    icases Hl with ⟨%t, %db, #Ht, Hown, ⟨%hk, Htxf, Hpend, Hdel, HW, Hhkf, Hhk, Hdb, Hwtx, #Htxdb, Hmu⟩,
      Hg, %Hwf⟩
    rw [Htx]
    icases ownWTx_live st.tx γ.db st'.C st'.S $$ Hwtx with ⟨Hlive, Hback⟩
    icases txBytes_acc st.tx s v 1 $$ [Hs Hlive] with ⟨%dq, Hsv, Hclose⟩
    · iframe Hlive
      iexact Hs
    iexists dq
    iframe Hsv
    iintro Hsv
    ispecialize Hclose $$ Hsv
    ispecialize Hback $$ Hclose
    iexists t, db
    iframe
    iframe #
    ipureintro
    exact Hwf

/-! ## The batch lock held, with its window flag -/

/-- The batch lock's ghost share, held, with the `Unlock` window flag `win`. -/
def batchGhostW (γ : BNames) (P : BParams) (st : BSess) (win : Bool) : IProp GF :=
  iprop(ghostVar γ.view (1 : Qp).half.half (vData P (st.C, st.R)) ∗
    ∃ (n w u : Nat), ghostVar γ.rvs (1 : Qp).half (((st.C, st.R) : RView), win) ∗
      ownTokAuth γ.wb n ∗ monoNatAuthOwn γ.wbc 1 w ∗ ghostVar γ.used (1 : Qp).half u ∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
      trkHalf γ P st.S ∗ ⌜bgOk P st false n w u⌝)

/-- The batch lock held in state `st`, with the window flag `win`. -/
def batchLockedW (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (win : Bool) : IProp GF :=
  iprop(∃ (t db : Loc), bF go!"batchTx" b ↦□ t ∗ sync.ownMutex (muOf t) ∗
    batchPhys γ b t db st ∗ batchGhostW γ P st win ∗ ⌜sessWf P st⌝)

theorem batchLocked_W (γ : BNames) (P : BParams) (b : Loc) (st : BSess) :
    batchLocked (GF := GF) γ P b st ⊢ batchLockedW γ P b st false := by
  unfold batchLockedW batchLocked batchLockedAt batchGhost batchGhostAt batchGhostW
  iintro H
  iexact H

/-! ## Paying for a commit -/

/-- What a commit gives back of the payment: the `run` goroutine's half of `γ.used`. -/
def payOut (γ : BNames) (stop : Bool) (m : Nat) : IProp GF :=
  if stop = false ∧ m = 1 then iprop(∃ u' : Nat, ghostVar γ.used (1 : Qp).half u') else iprop(True)

/-- The whole open token stops the backend (persistently). -/
theorem opn_stop (γ : BNames) :
    ⊢ dghostVar (GF := GF) γ.opn (DFrac.own (1 : Qp).half.half) false -∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false -∗
      dghostVar γ.opn (DFrac.own (1 : Qp).half) false ==∗ bStopped γ := by
  iintro H1 H2 Ho
  icombine H1 H2 as H
  unfold bStopped
  imod dghostVar_update_halves true γ.opn false false $$ H Ho with ⟨H, -⟩
  iapply dghostVar_persist $$ H

end preds

end backend
end EtcdGrove
end Perennial
