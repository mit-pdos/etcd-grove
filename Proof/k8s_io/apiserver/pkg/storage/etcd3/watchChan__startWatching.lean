/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__startWatching.lean`. Lean-first (no Rocq
counterpart).

Three phases. **The check** (initial events at a positive requested revision): `getCurrentStorageRV`
(the store's `GetCurrentResourceVersion`, with the caller's read update `Q 0` at the members) fires at
some `σ1`; an error or a requested revision above `σ1`'s is sent (`kErrOk`: E4, E6), else the read
updates are re-armed at `σ1.rev`, at least the requested revision. **The initial part**: `sync()` (the
initial raw events at its first page's state `σ0`, `kInitRaws`), then the annotated bookmark at
`σ0.rev` if asked (`kInit_ok`): the producer's state is the ideal stream's initial part
(`kProdAt_start`). **The watch**: the client watch of the scope from `initialRev + 1`, with
`WithPrevKV` (`withPrevKVM`) and `WithPrefix` when recursive, with the read update `Q 0`; the loop's
invariant: the consumer's state, the watch's cursor `cur` at the responses received, and the
producer's position `kProdAt` at the latest state `σc` read (each response's state and `σc` are of one
history, `hH`: the later of the two serves both, `kProdAt_hist`, `kRawSeg_hist`). A progress
notification queues `KRaw.bm` (a segment, `kRawSeg_bm1`), a response with events its events one by
one (a segment, `kRawSeg_chg1`, each a prefix of it, `kProdAt_ok`), an error response or a
`parseEvent` error is sent after `kProdExited` is set (the cancel's proposition, `kCancelPD`), and the
channel's closing closes `watchClosedCh` (`kProdExited`, the broadcast's).

**The client watch's close error** (E2; ledger 2026-11-16): the element's error arm gives
`closeErrOk` of it (a client error, a pointer if an `*errors.errorString`), and `WatchResponse.Err`
of its result, which `kErrOk_clientP` turns into `kErrOk`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__startWatching
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__sync
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__queueEvent
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__sendError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.progressNotifyEvent
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.parseEvent
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.logWatchChannelErr
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GetCurrentResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getResourceSizeEstimator
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdEvent
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdBookmark
public import Spec.k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError
public import Spec.k8s_io.apimachinery.pkg.util.wait.Jitter
public import Spec.time.Duration__Seconds
public import Spec.k8s_io.klog.v2.Errorf
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithPrevKV
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__Err
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__IsProgressNotify
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader__GetRevision
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.compactor__runWatchLoop
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ErrOk
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.OptsOwn
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.SyncPages
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- The client watch's options: `WithRev(rv)`, `WithPrevKV()`, and `WithPrefix()` when recursive. -/
def startOps (recur : Bool) (rv : w64) : List (OpFull → OpFull) :=
  [withRevM rv, withPrevKVM] ++ (if recur then [withPrefixM] else [])

/-- The client watch's operation: of the scope (`kp`, its prefix when recursive), from `rv`, with
previous key-values, accepted by `Watch` (`isRangeWatchP`, no panic, small). -/
theorem startOp_facts (kp : GoString) (recur : Bool) (rv : w64) (hkp : kp ≠ [])
    (hl : kp.length ≤ opKeyMax) :
    (opWatchModel kp (startOps recur rv)).isRangeWatchP rv = true ∧
    ¬ opWatchPanics kp (startOps recur rv) ∧ watchSizeOk (opWatchModel kp (startOps recur rv)) ∧
    (opWatchModel kp (startOps recur rv)).watchNorm = opWatchModel kp (startOps recur rv) ∧
    (opWatchModel kp (startOps recur rv)).key = kp ∧
    (opWatchModel kp (startOps recur rv)).base.rangeEnd = (if recur then prefixRangeEnd kp else []) ∧
    (opWatchModel kp (startOps recur rv)).base.prevKV = true := by
  have hle := prefixRangeEnd_length_le kp
  simp only [opKeyMax] at hl
  cases recur <;>
    simp [startOps, opWatchModel, opFold, OpFull.getInit, withRevM, withPrevKVM, withPrefixM, hkp,
      OpFull.isRangeWatchP, opWatchPanics, OpFull.watchPanics, OpFull.newOp, OpModel.zero,
      watchSizeOk, OpFull.watchNorm] <;> omega

/-- **The later of two states of one history** serves both: the producer's position moves to it. -/
theorem kProdAt_join {inS : GoString → Bool} {m : KWatchMode} {σc σ : KVState} {st c : Nat}
    {I : List KRaw} (h : kProdAt inS m σc st c I) (hh : kvSameHist σc σ) :
    kProdAt inS m (if σc.rev ≤ σ.rev then σ else σc) st c I ∧
    σ.rev ≤ (if σc.rev ≤ σ.rev then σ else σc).rev ∧
    kvSameHist σ (if σc.rev ≤ σ.rev then σ else σc) := by
  split
  · exact ⟨kProdAt_hist hh (by assumption) h, Nat.le_refl _, ⟨rfl, rfl, Or.inl (List.prefix_refl _)⟩⟩
  · exact ⟨h, by omega, kvSameHist_symm hh⟩

/-- The ideal raw stream's initial part: the initial events and the bookmark if asked. -/
theorem kRawIdealL_nil (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat) :
    kRawIdealL inS m σ st [] = if m.forceInit then
      kInitRaws inS σ st ++ (if m.bmReq then [KRaw.bm st true] else []) else [] := by
  unfold kRawIdealL kInitRaws; split <;> simp

/-- Without initial events, at a positive requested revision, any state is a start. -/
theorem kStart_any {inS : GoString → Bool} {m : KWatchMode} {st : Nat} (σ : KVState)
    (hf : m.forceInit = false) (hr : 0 < m.req) (hst : st = m.req) :
    kStartOk m σ st ∧ kProdAt inS m σ st st [] := by
  refine ⟨?_, ?_⟩
  · unfold kStartOk; simp [hf, hr, hst]
  · have := kProdAt_start (inS := inS) (m := m) (σ := σ) (st := st) (fun h => by simp [hf] at h)
    unfold kRawIdealL at this; simpa [hf] using this

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj] [Pos.Countable Obj]

/-- **`sendError`'s commit from a running producer of `resultChan`** (`kResChan`, `kResAlive`): the
token back on either outcome. -/
theorem kRes_errCommit (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (chR : Loc) (q : Qp) :
    ⊢ kResChan c W γ cd sel emp inS m Q procd alive chR -∗ kResAlive alive q -∗
      (kResAlive alive q ∧ ∀ v : k8s_io.apimachinery.pkg.watch.Event, ⌜v.Type' = go!"ERROR"⌝ -∗
        statusFailureAt v.Object' -∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ : IProp GF,
          ▷ (kResAlive alive q ∗ emp -∗ Φ) -∗ sendAu γ.res.chanName v Φ) := by
  iintro #Hrc HT
  isplit
  · iexact HT
  iintro %v %hv Hst
  unfold kResChan
  icases Hrc with ⟨#Hch, #Hinv⟩
  iapply spsc_send_commit_inv γ.res chR (kResElem c W γ cd sel emp inS m Q) (fun _ => iprop(True))
    iprop(kResInv c γ cd sel emp inS m Q procd ∨ kResClosed alive) (kResAlive alive q) iprop(emp) v
    $$ Hch Hinv [] HT
  · iapply kResChan_nc
  iintro HT HX
  iapply kResInv_err_acc c W γ cd sel emp inS m Q procd alive q v hv $$ Hst HT HX

/-- An event's `PrevKv` read at a state, at a later state of the same history. -/
theorem prevKvOk_hist (o : OpFull) (σ σ' : KVState) (ev : mvcc.EvM) (pk : Loc)
    (hh : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev) (hr : sint.nat ev.kv.modRev - 1 ≤ σ.rev) :
    prevKvOk (GF := GF) o σ ev pk ⊢ prevKvOk o σ' ev pk := by
  unfold prevKvOk
  split
  · iintro (%h | ⟨%r, %h, #Hk⟩)
    · ileft; ipureintro; exact h
    · iright; iexists r; iframe Hk; ipureintro
      rw [← kvSameHist_at σ σ' _ hh hr (by omega)]; exact h
  · iintro %h; ipureintro; exact h

/-- **The producer exits** (before a `sendError` or the closing): `prodEx` set, for good. -/
theorem kProdExited_set (γ : KWatchNames) :
    ⊢ dghostVar (GF := GF) γ.prodEx (DFrac.own 1) false ==∗ kProdExited γ := by
  iintro Hd
  imod dghostVar_update true $$ Hd with Hd
  unfold kProdExited
  iapply dghostVar_persist $$ Hd

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [ctxDescs : EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- **The producer's `sendError`** (then it returns): `kProdExited` set first (`kCancelPD`'s producer
arm, for `wc.cancel()`), the commit from `kResChan`, the running-producer token back. -/
theorem wp_prod_sendError [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (wp_sendError : watchChan.sendError.spec (GF := GF) (hG := hG))
    {Obj : Type} [DecidableEq Obj] [Pos.Countable Obj] (wc sp : Loc)
    (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γ : KWatchNames) (cd : context.ContextDesc (IProp GF))
    (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool) (m : KWatchMode)
    (Q : Nat → KVState → IProp GF) (procd alive : GName) (ctx : GoInterfaceOk) (kp : GoString)
    (recur : Bool) (q : Qp) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
        kWcProd wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur ∗ kErrOk err ∗
        dghostVar γ.prodEx (DFrac.own 1) false ∗ kResAlive alive q }}
      (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
        go!"sendError")) (Val #err))
    {{ RET #(); kResAlive alive q }} := by
  iintro %Φ ⟨#Hpkg, #Hwc, #Hok, Hpe, Halive⟩ HΦ
  iunfold kWcProd at Hwc
  icases Hwc with ⟨%wp, %chI, %chR, %lg, %cf, %rse, %γc, -, -, -, -, -, -,
    #Hfctx, #Hfcf, #Hcs, -, -, -, -, -, -, #HfR, #Hrc, #Hctx, -, -, -⟩
  imod kProdExited_set γ $$ Hpe with #Hex
  ihave #Hrc' := Hrc
  iunfold kResChan at Hrc'
  icases Hrc' with ⟨#HchR, -⟩
  wp_apply (wp_sendError wc chR ctx (kCdw γ cd) γ.res.chanName cf γc (kCancelPD γ cd) err
      (kResAlive alive q) iprop(kResAlive alive q ∗ emp)) $$ [Halive] as Hres
  · iframe #
    isplitr
    · iintro !>; unfold kCancelPD; iright; ileft; iexact Hex
    iapply kRes_errCommit $$ Hrc Halive
  iapply HΦ
  icases Hres with (⟨Ha, -⟩ | Ha) <;> iexact Ha

theorem watchChan.startWatching.wp_proof
    (wp_AsLeafTy : errors.AsLeafTy.spec (GF := GF) (hG := hG))
    (wp_ECode : rpctypes.EtcdError.Code.spec (GF := GF) (hG := hG))
    (wp_SCode : status.Status.Code.spec (GF := GF) (hG := hG))
    (wp_GetCRV : store.GetCurrentResourceVersion.spec (GF := GF) (hG := hG))
    (wp_TooLarge : storage.NewTooLargeResourceVersionError.spec (GF := GF) (hG := hG))
    (wp_Jitter : wait.Jitter.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (wp_sendError : watchChan.sendError.spec (GF := GF) (hG := hG))
    (wp_sync : watchChan.sync.spec (GF := GF) (hG := hG))
    (wp_Errorf : klog.Errorf.spec (GF := GF) (hG := hG))
    (wp_progressNotifyEvent : progressNotifyEvent.spec (GF := GF) (hG := hG))
    (wp_queueEvent : watchChan.queueEvent.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithPrevKV : WithPrevKV.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_getRSE : store.getResourceSizeEstimator.spec (GF := GF) (hG := hG))
    (wp_Err : WatchResponse.Err.spec (GF := GF) (hG := hG))
    (wp_IsPN : WatchResponse.IsProgressNotify.spec (GF := GF) (hG := hG))
    (wp_GetRevision : ResponseHeader.GetRevision.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdBookmark : metrics.RecordEtcdBookmark.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdEvent : metrics.RecordEtcdEvent.spec (GF := GF) (hG := hG))
    (wp_parseEvent : parseEvent.spec (GF := GF) (hG := hG))
    (wp_logWatchChannelErr : logWatchChannelErr.spec (GF := GF) (hG := hG)) :
    watchChan.startWatching.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ _ wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur r0 q wcc γb
    hQ hH hR hbm hrpl
  haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
  wp_start as ⟨#Hoff, #Hst, #Hsw, #Hwc, Hir, Hpre, #Hra, #Hre, Hps, Hpe, Halive, Hbc, Htok⟩
  ihave #Hwc' := Hwc
  iunfold kWcProd at Hwc'
  icases Hwc' with ⟨%wp, %chI, %chR, %lg, %cf, %rse, %γc, #Hfw, #Hsw1, #Hfk, #Hfr, #Hfpn, #Hfrt,
    #Hfctx, #Hfcf, #Hcs, #Hfrse, #Hrse, #HfI, #HfL, #Hbl, #Hspsc, #HfR, #Hrc, #Hctx, #Hoc, #Hce, %Hp⟩
  obtain ⟨hinS, hkpl, hkp⟩ := Hp
  ihave #Hsw' := Hsw
  iunfold storeWatchOk at Hsw'
  icases Hsw' with ⟨%wp', %nf, %crv, %rse', #Hsw2, #Hwcl, -, -, #Hwgr, -, -, #Hwcrv, -, -, #Hcrv, -,
    #Hcwo, -⟩
  ihave %Hwp := typedPointsto_agree_wand _ _ _ _ _ $$ Hsw1 Hsw2
  subst Hwp
  ihave #Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, -, -, -, -, -, -, -, -, -, -, -, -, #Hcl, -, #Hregs, -, #Hlst⟩
  iunfold storeListOk at Hlst
  icases Hlst with ⟨%lf, %lγ, -, -, -, %Hutf, %Hrp⟩
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pme : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pklog : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
  · iPkgInit
  ihave #HctxOk : ctxOk ctx (kCdw γ cd) $$ []
  · iapply ctxOk_of_isContext
    iframe Hctx Hoc
  ihave #Hspsc' := Hspsc
  iunfold isSpsc at Hspsc'
  icases Hspsc' with ⟨#HchI, -⟩
  ihave ⟨%HPf, %HPn, #HP0⟩ : (⌜m.forceInit = true → uint.nat r0 = m.req ∧ uint.Z r0 < 2 ^ 63⌝ ∗
      ⌜m.forceInit = false → 0 < m.req → uint.nat r0 = m.req ∧ uint.Z r0 + 1 < 2 ^ 63⌝ ∗
      (⌜m.forceInit = true ∨ 0 < m.req⌝ ∨
        ∃ (lb0 : Nat) (σ0 : KVState), □ Q lb0 σ0 ∗ ⌜r0 = W64 (σ0.rev : Int) ∧ kvRevFits σ0.rev⌝) :
      IProp GF) $$ [Hpre]
  · iunfold kStartPre at Hpre
    cases hf : m.forceInit
    · isimp only [Bool.false_eq_true, ↓reduceIte] at Hpre
      by_cases hr : 0 < m.req
      · isimp only [hr, ↓reduceIte] at Hpre
        icases Hpre with %H
        isplitr; · ipureintro; simp
        isplitr; · ipureintro; intro _ _; exact H
        ileft; ipureintro; right; exact hr
      · isimp only [hr, ↓reduceIte] at Hpre
        isplitr; · ipureintro; simp
        isplitr; · ipureintro; intro _ h; exact absurd h hr
        iright; iexact Hpre
    · isimp only [↓reduceIte] at Hpre
      icases Hpre with %H
      isplitr; · ipureintro; intro _; exact H
      isplitr; · ipureintro; simp
      ileft; ipureintro; left; rfl
  wp_auto
  -- the check: initial events at a positive requested revision
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ wc_ptr ↦ wc ∗
      forceInitialEvents_ptr ↦ m.forceInit ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦ r0 ∗
      dghostVar γ.prodEx (DFrac.own 1) false ∗ kResAlive alive q ∗ threadTok ∗
      (kResAlive alive q ∗ threadTok -∗ Φ #()) ∗
      ∃ lbf : Nat, readAus c γk (Q lbf) ∗ ⌜m.forceInit = true → m.req ≤ lbf⌝) ∨
      (⌜v = returnVal #()⌝ ∗ Φ #())))
    at next with [wc forceInitialEvents Hir Hpe Halive Htok HΦ]
  · by_cases hck : 0 < sint.Z r0 ∧ m.forceInit = true
    rotate_left
    · -- no check: the read updates from `Q 0`
      by_cases h0 : 0 < sint.Z r0
      · have hf : m.forceInit = false := by
          cases hf : m.forceInit
          · rfl
          · exact absurd ⟨h0, hf⟩ hck
        rw [decide_eq_true (show sint.Z (W64 0) < sint.Z r0 from h0)]
        wp_auto
        rw [hf]
        wp_auto
        ileft
        iframe
        isplitr; · ipureintro; rfl
        iexists 0
        iframe Hra
        ipureintro
        intro h; cases h
      · rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z r0 from h0)]
        wp_auto
        ileft
        iframe
        isplitr; · ipureintro; rfl
        iexists 0
        iframe Hra
        ipureintro
        intro hf
        obtain ⟨h1, h2⟩ := HPf hf
        have : uint.nat r0 = 0 := by
          have h0' : sint.Z r0 ≤ 0 := by simpa using h0
          word
        omega
    obtain ⟨h0, hf⟩ := hck
    rw [hf, decide_eq_true (show sint.Z (W64 0) < sint.Z r0 from h0)]
    obtain ⟨hr0, hr0'⟩ := HPf hf
    wp_auto
    wp_bind (App (Val #crv) (Val _))
    iapply Hcrv
    icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, Htok⟩
    wp_apply (wp_GetCRV Obj sp c ctx (kCdw γ cd) c.resourcePrefix (fun _ _ => Q 0) Hrp hrpl) $$ [$Hlt]
      as %n %err ⟨Hlt, Hout⟩
    · iframe #
      iapply readAus_crv $$ Hra
    ihave Htok := (threadTok_level0 (GF := GF)).2 $$ [Hlt Htok]
    · iframe
    iexists n, err
    isplitr
    · ipureintro; rfl
    icases Hout with (⟨%Herr, Herr2⟩ | ⟨%Herr, %σ1, #HQ1, %Hσ1⟩)
    · -- the read's error: sent
      ihave #Hok : kErrOk err $$ [Herr2]
      · icases Herr2 with (⟨%Hc, #Hs, #Hcl⟩ | ⟨%x, %hx, #Hx⟩)
        · iapply (kErrOk_client wp_AsLeafTy wp_ECode wp_SCode) $$ Perr
          iunfold kClientErr
          iframe #
          ipureintro; exact ⟨Herr, Hc⟩
        · subst hx
          iapply (kErrOk_errorString wp_AsLeafTy x) $$ Perr Hx
      cases err with
      | nil => exact absurd rfl Herr
      | ok ei =>
      wp_auto
      wp_apply (wp_prod_sendError wp_sendError wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur q
        _) $$ [Hpe Halive] as Halive
      · iframe #
        iframe
      (try wp_auto)
      iright
      isplitr; · ipureintro; rfl
      iapply HΦ
      iframe
    obtain ⟨hn, hσpos⟩ := Hσ1
    subst Herr hn
    wp_auto
    by_cases hlt : uint.Z (W64 (σ1.rev : Int)) < uint.Z r0
    · -- above the current revision: `NewTooLargeResourceVersionError`
      rw [decide_eq_true hlt]
      wp_auto
      ihave #Pw : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait $$ []
      · iPkgInit
      ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
      · iPkgInit
      ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
      · iPkgInit
      wp_apply wp_Jitter as %j -
      (try wp_auto)
      wp_apply wp_Seconds as %fl -
      (try wp_auto)
      wp_apply wp_ArbitraryInt as %ai -
      (try wp_auto)
      wp_apply wp_TooLarge as %e ⟨-, %l, %st, %dv, %Hst, #Hl, -⟩
      obtain ⟨rfl, hst, -⟩ := Hst
      ihave #Hok := kErrOk_statusError wp_AsLeafTy l st hst $$ Perr Hl
      (try wp_auto)
      wp_apply (wp_prod_sendError wp_sendError wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur q
        _) $$ [Hpe Halive] as Halive
      · iframe #
        iframe
      (try wp_auto)
      iright
      isplitr; · ipureintro; rfl
      iapply HΦ
      iframe
    · rw [decide_eq_false hlt]
      ihave Hra1 := Hre $$ %0 %σ1 HQ1
      imod Hra1 with #Hra1
      wp_auto
      ileft
      iframe
      isplitr; · ipureintro; rfl
      iexists σ1.rev
      iframe Hra1
      ipureintro
      intro _
      rw [← hr0]
      have : uint.Z r0 ≤ uint.Z (W64 (σ1.rev : Int)) := by omega
      have h2 : uint.Z (W64 (σ1.rev : Int)) ≤ σ1.rev := by
        simp only [uint.Z, W64, BitVec.toNat_ofInt]; omega
      have h3 : (uint.nat r0 : Int) = uint.Z r0 := by simp [uint.nat, uint.Z]
      omega
  iintro (⟨%Hv, wc, forceInitialEvents, Hir, Hpe, Halive, Htok, HΦ, %lbf, #Hraf, %Hlbf⟩ |
    ⟨%Hv, HΦ⟩)
  rotate_left
  · try subst Hv
    wp_auto
    iexact HΦ
  try subst Hv
  wp_auto
  -- the initial events
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ wc_ptr ↦ wc ∗
      dghostVar γ.prodEx (DFrac.own 1) false ∗ kResAlive alive q ∗ threadTok ∗
      (kResAlive alive q ∗ threadTok -∗ Φ #()) ∗
      ∃ (r1 : w64) (I : List KRaw) (st : Nat),
        structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦ r1 ∗
        kProdSt γ cd I ∗ ⌜uint.nat r1 = st ∧ uint.Z r1 + 1 < 2 ^ 63⌝ ∗
        ((∃ (lb0 : Nat) (σ0 : KVState), □ Q lb0 σ0 ∗ ⌜kStartOk m σ0 st ∧
            (m.forceInit = true → st = σ0.rev ∧ I = kInitRaws inS σ0 st) ∧
            (m.forceInit = false → I = [])⌝) ∨
          ⌜m.forceInit = false ∧ 0 < m.req ∧ st = m.req ∧ I = []⌝)) ∨
      (⌜v = returnVal #()⌝ ∗ Φ #())))
    at next with [wc Hir Hpe Halive Htok HΦ Hps]
  · cases hf : m.forceInit
    · -- none
      wp_auto
      ileft
      isplitr; · ipureintro; rfl
      iframe wc Hpe Halive Htok HΦ
      by_cases hr : 0 < m.req
      · obtain ⟨h1, h2⟩ := HPn hf hr
        iexists r0, [], m.req
        iframe Hir Hps
        isplitr; · ipureintro; exact ⟨h1, h2⟩
        iright; ipureintro; exact ⟨rfl, hr, rfl, rfl⟩
      · icases HP0 with (%H | ⟨%lb0, %σ0, #HQ0, %H⟩)
        · exfalso; rcases H with H | H
          · simp_all
          · exact hr H
        obtain ⟨rfl, hfit⟩ := H
        have hfit' := hfit.lt
        iexists W64 (σ0.rev : Int), [], σ0.rev
        iframe Hir Hps
        isplitr; · ipureintro; constructor <;> word
        ileft
        iexists lb0, σ0
        iframe HQ0
        ipureintro
        refine ⟨?_, ⟨fun h => absurd h (by decide), fun _ => rfl⟩⟩
        unfold kStartOk; simp [hr]
        all_goals (intro h; simp [hf] at h)
    · -- `sync()`
      wp_auto
      icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, Htok⟩
      wp_apply (wp_sync Obj wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur r0 lbf 1 hQ hH hR
          hf (Hlbf hf)) $$ [$Hlt Hir Hps Hpe] as %err ⟨Hlt, Hpe, Hout⟩
      · iframe #
        iframe
      ihave Htok := (threadTok_level0 (GF := GF)).2 $$ [Hlt Htok]
      · iframe
      icases Hout with (⟨%Herr, %lb0, %σ0, #HQ0, %Hσ0, Hir, Hps⟩ | ⟨#Hok, %r', Hir⟩)
      · subst Herr
        obtain ⟨hst0, hfit⟩ := Hσ0
        have hfit' := hfit.lt
        wp_auto
        ileft
        isplitr; · ipureintro; rfl
        iframe wc Hpe Halive Htok HΦ
        iexists W64 (σ0.rev : Int), kInitRaws inS σ0 σ0.rev, σ0.rev
        iframe Hir Hps
        isplitr; · ipureintro; constructor <;> word
        ileft
        iexists lb0, σ0
        iframe HQ0
        ipureintro
        exact ⟨hst0, ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by decide)⟩⟩
      · -- logged and sent
        ihave #Hok' := Hok
        iunfold kErrOk at Hok'
        icases Hok' with ⟨%e, %He, -, #Hstr, %Hfmt, -⟩
        subst He
        ihave HerrF : fmt.argOk (GF := GF) (GoInterface.ok e) $$ []
        · unfold fmt.argOk
          iright; ileft
          iframe #
          ipureintro; exact Hfmt
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        (try wp_auto)
        wp_apply wp_Errorf _ _ _ _ $$ [$Hsl HerrF] as -
        · iframe #
          klog_args_intro
          isplitl [HerrF]
          · iapply klog.argOkAt_of_argOk
            isplitr
            · ipureintro; decide
            iexact HerrF
          itrivial
        (try wp_auto)
        wp_apply (wp_prod_sendError wp_sendError wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur q
          _) $$ [Hpe Halive] as Halive
        · iframe #
          iframe
        (try wp_auto)
        iright
        isplitr; · ipureintro; rfl
        iapply HΦ
        iframe
  iintro (⟨%Hv, wc, Hpe, Halive, Htok, HΦ, %r1, %I, %st, Hir, Hps, %Hr1, #HS⟩ | ⟨%Hv, HΦ⟩)
  rotate_left
  · try subst Hv
    wp_auto
    iexact HΦ
  try subst Hv
  wp_auto
  -- the initial-events-end bookmark
  wp_join (Q := fun v => iprop(⌜v = executeVal⌝ ∗ wc_ptr ↦ wc ∗
      dghostVar γ.prodEx (DFrac.own 1) false ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦ r1 ∗
      ∃ I' : List KRaw, kProdSt γ cd I' ∗
        ((∃ (lb0 : Nat) (σ0 : KVState), □ Q lb0 σ0 ∗ ⌜kStartOk m σ0 st ∧ kProdAt inS m σ0 st st I'⌝) ∨
          ⌜m.forceInit = false ∧ 0 < m.req ∧ st = m.req ∧ I' = []⌝)))
    at next with [wc Hir Hpe Hps]
  · cases hb : m.bmReq
    · wp_auto
      iframe
      isplitr; · ipureintro; rfl
      icases HS with (⟨%lb0, %σ0, #HQ0, %H⟩ | %H)
      · ileft
        iexists lb0, σ0
        iframe HQ0
        ipureintro
        obtain ⟨hst0, hf1, hf2⟩ := H
        refine ⟨hst0, ?_⟩
        cases hf : m.forceInit
        · rw [hf2 hf]
          have := kProdAt_start (inS := inS) (m := m) (σ := σ0) (st := st) (fun h => by simp [hf] at h)
          rwa [kRawIdealL_nil, hf] at this
        · obtain ⟨h1, h2⟩ := hf1 hf
          rw [h2]
          have := kProdAt_start (inS := inS) (m := m) (σ := σ0) (st := st) (fun _ => by omega)
          rw [kRawIdealL_nil] at this; simpa [hf, hb] using this
      · iright; ipureintro; exact H
    · have hf := hbm hb
      icases HS with (⟨%lb0, %σ0, #HQ0, %H⟩ | %H)
      rotate_left
      · exfalso; rw [hf] at H; exact absurd H.1 (by decide)
      obtain ⟨hst0, hf1, -⟩ := H
      obtain ⟨hst, hI⟩ := hf1 hf
      subst hI
      have hr1 : r1 = W64 (st : Int) := by
        have := Hr1.1; have := Hr1.2; word
      wp_auto
      wp_apply wp_progressNotifyEvent as %p ⟨%ev, Hp, %Hev⟩
      ipersist Hp
      ihave #Hea : eventAt σ0 p (KRaw.bm st true) $$ []
      · iunfold eventAt
        iexists _
        iframe Hp
        unfold kEvIs
        ipureintro
        exact ⟨by rw [Hev.1, hr1], Hev.2.1, rfl⟩
      have hok : kRawStreamOk inS m σ0 st (kInitRaws inS σ0 st ++ [KRaw.bm st true]) := by
        apply kInit_ok (fun _ => by omega)
        rw [kRawIdealL_nil]; simp [hf, hb]
      ihave ⟨%S, %Qs, Hsc, HQs, Hdrop⟩ := kProd_queue γ cd inS m Q chI p (KRaw.bm st true) _ lb0 lb0 st
        σ0 σ0 hst0 hok $$ Hspsc Hea HQ0 HQ0 Hps
      wp_apply (wp_queueEvent wc chI lg ctx (kCdw γ cd) γ.inc.chanName p S Qs) $$ [Hsc] as Hres
      · iframe #
        iexact Hsc
      ihave ⟨Hps, Hpe⟩ : (kProdSt γ cd (kInitRaws inS σ0 st ++ [KRaw.bm st true]) ∗
          dghostVar γ.prodEx (DFrac.own 1) false : IProp GF) $$ [Hres HQs Hdrop Hpe]
      · icases Hres with (HQs' | ⟨#Hpd, HS⟩)
        · iframe Hpe
          iapply HQs $$ HQs'
        · ihave H2 := Hdrop $$ %1 HS
          iapply H2
          · iintro !>
            unfold kCdw
            iexact Hpd
          · iexact Hpe
      (try wp_auto)
      iframe
      isplitr; · ipureintro; rfl
      ileft
      iexists lb0, σ0
      iframe HQ0
      ipureintro
      refine ⟨hst0, ?_⟩
      have := kProdAt_start (inS := inS) (m := m) (σ := σ0) (st := st) (fun _ => by omega)
      rw [kRawIdealL_nil] at this; simpa [hf, hb] using this
  iintro ⟨%Hv, wc, Hpe, Hir, %I, Hps, #HS⟩
  try subst Hv
  wp_auto
  -- the watch's options
  wp_apply wp_WithRev as %f1 #Hf1
  wp_apply wp_WithPrevKV as %f2 #Hf2
  wp_apply (wp_slice_literal (V := GoFunc) [f1, f2])
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, Hcap0⟩
  imod ownSlice_persist _ _ _ $$ Hsl0 with #Hsl0
  generalize hosl : slice.mk sl0 _ _ = osl0
  ihave Ho0 : optsOwn (GF := GF) osl0 [withRevM (r1 + W64 1), withPrevKVM] $$ [Hcap0]
  · iunfold optsOwn
    iexists [f1, f2]
    iframe Hsl0 Hcap0
    isplitr
    · ipureintro; rfl
    iintro !> %i %f %g %Hf %Hg
    rcases i with _ | _ | i
    · cases Hf; cases Hg; iexact Hf1
    · cases Hf; cases Hg; iexact Hf2
    · simp at Hf
  wp_auto
  wp_join (Q := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ osl : GoSlice, opts_ptr ↦ osl ∗
      optsOwn (GF := GF) osl (startOps recur (r1 + W64 1)))) at next with [opts Ho0]
  · cases recur
    · wp_auto
      isplitr; · ipureintro; rfl
      iexists osl0
      iframe opts
      iExactEq Ho0
      rfl
    · wp_auto
      wp_apply wp_WithPrefix as %f3 #Hf3
      wp_apply (wp_slice_literal (V := GoFunc) [f3])
      isplitr
      · ipureintro; rfl
      iintro %sl3 ⟨Hsl3, -⟩
      (try wp_auto)
      wp_apply (wp_optsOwn_append _ _ _ f3 withPrefixM) $$ [Ho0 Hsl3] as %o3 Ho3
      · iframe Ho0 Hsl3 Hf3
      (try wp_auto)
      isplitr; · ipureintro; rfl
      iexists o3
      iframe opts
      iExactEq Ho3
      rfl
  iintro ⟨%Hv, %osl, opts, Ho⟩
  try subst Hv
  wp_auto
  -- the client watch of the scope from `initialRev + 1`
  icases optsOwn_optsAt _ _ $$ Ho with ⟨#HoAt, -⟩
  ihave #Hcwo' := Hcwo
  iunfold clientWatchOk at Hcwo'
  icases Hcwo' with ⟨%w, %Vw, #Hwf, #Hcw, %Hkst⟩
  ihave #Hwctx := context.watchCtx_of_isContext ctx (kCdw γ cd) $$ [Hctx Hoc]
  · iframe #
  ihave ⟨%wom, #Hwom⟩ := context.watchCtx_outMD _ _ $$ Hwctx
  ihave #Hra' := Hra
  iunfold readAus at Hra'
  icases Hra' with ⟨#Hkr, -⟩
  obtain ⟨hrw, hnp, hsz, hnorm, hkey, hre, hpk⟩ := startOp_facts kp recur (r1 + W64 1) hkp hkpl
  have hrev1 : 1 ≤ sint.Z (r1 + W64 1) := by have := Hr1.2; word
  wp_apply (client_Watch_field wp_Watch c.cl w Vw γk ctx (kCdw γ cd) wom kp osl (startOps recur (r1 + W64 1)) (r1 + W64 1)
      (Q 0) 0) $$ [] as %wch %γw ⟨#Hwsp, Hcons, #Hcur0⟩
  · iunfold kvReadAu at Hkr
    iunfold kvAu at Hkr
    iframe #
    isplitr
    · ipureintro; exact Hkst
    isplitr
    · ipureintro; exact ⟨hrw, hnp, hrev1, hsz⟩
    iintro !> %h
    exact absurd h.2 (Nat.lt_irrefl 0)
  (try wp_auto)
  -- the size estimator: `nil`
  wp_bind (App (Val #rse) (Val _))
  iapply Hrse
  wp_apply (wp_getRSE Obj sp c) $$ [Htok] as Htok
  · iframe #
    iframe
  (try wp_auto)
  have hcur0 : r1 + W64 1 - W64 1 = r1 := by word
  ihave #Hcur1 : monoListIdxOwn γw.cur 0 r1 $$ []
  · iExactEq Hcur0; rw [hcur0]
  have hst1 : sint.nat r1 = st := by have := Hr1.1; have := Hr1.2; word
  ihave HJ : (∃ (rs : List go_etcd_io.etcd.client.v3.WatchResponse) (cur : w64) (I : List KRaw),
      "Hcons" ∷ spscConsumer γw.spsc rs ∗ "#Hcur" ∷ monoListIdxOwn γw.cur rs.length cur ∗
      "Hps" ∷ kProdSt γ cd I ∗ "Hpe" ∷ dghostVar γ.prodEx (DFrac.own 1) false ∗
      "Halive" ∷ kResAlive alive q ∗ "Htok" ∷ threadTok ∗
      "HΦ" ∷ (kResAlive alive q ∗ threadTok -∗ Φ #()) ∗
      "Hbc" ∷ ownBroadcastChan wcc γb (kProdExited γ) Broadcast.Pending ∗
      "%Hc0" ∷ ⌜0 ≤ sint.Z cur⌝ ∗
      "#HP" ∷ ((∃ (lb0 lbc : Nat) (σ0 σc : KVState), □ Q lb0 σ0 ∗ □ Q lbc σc ∗
          ⌜kStartOk m σ0 st ∧ kProdAt inS m σc st (sint.nat cur) I⌝) ∨
        ⌜m.forceInit = false ∧ 0 < m.req ∧ st = m.req ∧ I = [] ∧ sint.nat cur = st⌝) : IProp GF)
      $$ [Hcons Hps Hpe Halive Htok HΦ Hbc]
  · iexists [], r1, I
    simp only [named, List.length_nil]
    iframe
    isplitr
    · iexact Hcur1
    isplitr
    · ipureintro; have := Hr1.2; word
    icases HS with (⟨%lb0, %σ0, #HQ0, %H⟩ | %H)
    · ileft
      iexists lb0, lb0, σ0, σ0
      iframe HQ0
      ipureintro; rw [hst1]; exact H
    · iright; ipureintro; exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2, hst1⟩
  have hscope : ∀ (σ : KVState) (lo hi : Nat),
      σ.rangeEvents (opWatchModel kp (startOps recur (r1 + W64 1))).watchNorm lo hi =
        kRangeEvsL σ inS lo hi := by
    intro σ lo hi
    apply rangeEvents_scope
    intro k
    rw [hnorm, hkey, hre, inRange_scope kp recur (fun _ => hkp) k, hinS]
  wp_for HJ
  wp_apply (wp_spsc_receive (t := go_etcd_io.etcd.client.v3.WatchResponse.ty) γw.spsc wch _ _ rs)
    $$ [$Hwsp $Hcons] as %v %ok Hv
  cases ok
  · -- the channel closed: the producer exits
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hv with ⟨-, %Hv⟩
    wp_auto
    wp_for_post
    imod kProdExited_set γ $$ Hpe with #Hex
    (try wp_auto)
    wp_apply (wp_broadcast_chan_close wcc γb (kProdExited γ)) $$ [Hbc]
    · iframe #
      iframe
    iintro -
    (try wp_auto)
    iapply HΦ
    iframe
  simp only [↓reduceIte]
  icases Hv with ⟨HP', Hcons⟩
  iunfold watchStateElemP at HP'
  icases HP' with ⟨%r, %σ, %c0, %c1, #Hr, #HQσ, #Hi0, #Hi1, #Hok, -, -⟩
  ihave #Hi0' : monoListIdxOwn γw.cur rs.length c0 $$ []
  · iExactEq Hi0; simp
  ihave #Hi1' : monoListIdxOwn γw.cur (rs ++ [v]).length c1 $$ []
  · iExactEq Hi1; simp
  ihave %Hc0e := mono_list_idx_agree γw.cur _ c0 cur $$ Hi0' Hcur
  subst Hc0e
  -- the later of the producer's state and the response's
  ihave ⟨%lb0, %lbc, %σ0, %σ', #HQ0, #HQ', %Hj⟩ : (∃ (lb0 lbc : Nat) (σ0 σ' : KVState),
      □ Q lb0 σ0 ∗ □ Q lbc σ' ∗ ⌜kStartOk m σ0 st ∧ kProdAt inS m σ' st (sint.nat c0) I ∧
        σ.rev ≤ σ'.rev ∧ kvSameHist σ σ'⌝ : IProp GF) $$ []
  · icases HP with (⟨%lb0, %lbc, %σ0, %σc, #HQ0, #HQc, %H⟩ | %H)
    · ihave %Hh := hH _ _ σc σ $$ [HQc HQσ]
      · iframe HQc HQσ
      obtain ⟨hat, hle, hhist⟩ := kProdAt_join H.2 Hh
      by_cases hcr : σc.rev ≤ σ.rev
      · iexists lb0, 0, σ0, σ
        iframe HQ0 HQσ
        ipureintro
        simp only [hcr, ↓reduceIte] at hat hle hhist
        exact ⟨H.1, hat, hle, hhist⟩
      · iexists lb0, lbc, σ0, σc
        iframe HQ0 HQc
        ipureintro
        simp only [hcr, ↓reduceIte] at hat hle hhist
        exact ⟨H.1, hat, hle, hhist⟩
    · obtain ⟨hf, hr, hst, hI, hc⟩ := H
      obtain ⟨h1, h2⟩ := kStart_any (inS := inS) σ hf hr hst
      iexists 0, 0, σ, σ
      iframe HQσ
      ipureintro
      refine ⟨h1, by rw [hc, hI]; exact h2, Nat.le_refl _, ⟨rfl, rfl, Or.inl (List.prefix_refl _)⟩⟩
  obtain ⟨hst0, hat, hle, hhist⟩ := Hj
  -- the close error is a watch's (`closeErrOk`)
  ihave #Hse : closeErrOk v.closeErr' $$ []
  · iunfold watchStateRespOkP at Hok
    icases Hok with ⟨Hok1, -⟩
    iunfold watchStateRespOk at Hok1
    icases Hok1 with (⟨-, #H⟩ | %H | %H | ⟨%H, -⟩)
    · iexact H
    all_goals
      have hn : v.closeErr' = interface.nil := by
        have := H.1; unfold watchErr at this
        simp only [not_or, ne_eq, Decidable.not_not] at this; exact this.1
      rw [hn]
      iapply closeErrOk_nil
  ihave #Hsce := closeErrOk_status _ $$ Hse
  wp_auto
  wp_apply (wp_Err wres_ptr v (DFrac.own 1)) $$ [$wres $Hsce] as %err ⟨wres, %Herr, -, -, -, -, -⟩
  cases err with
  | ok ei =>
    -- an error response: logged and sent
    wp_auto
    wp_apply (wp_Err wres_ptr v (DFrac.own 1)) $$ [$wres $Hsce] as %err2
      ⟨wres, %Herr2, -, #Hes2, %Hcl2, -, %Hptr2⟩
    have hne2 : err2 ≠ interface.nil := by
      intro h; rw [h] at Herr2; have := Herr2.1 rfl; have := Herr.2 this; cases this
    ihave %Hce := closeErrOk_pure _ $$ Hse
    ihave #Hok : kErrOk err2 $$ []
    · iapply (kErrOk_clientP wp_AsLeafTy wp_ECode wp_SCode err2
        ⟨hne2, Hcl2 EtcdGrove.rpctypesEtcdError_asTarget Hce.1⟩ (Hptr2 Hce.2)) $$ Perr Hes2
    (try wp_auto)
    wp_apply wp_logWatchChannelErr
    · iframe #
    (try wp_auto)
    wp_apply (wp_prod_sendError wp_sendError wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur q
      _) $$ [Hpe Halive] as Halive
    · iframe #
      iframe
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iframe
  | nil =>
  have hnw : ¬ watchErr v := by
    have := Herr.1 rfl; unfold watchErr
    simp only [not_or, ne_eq, Decidable.not_not, Bool.not_eq_true]; exact this
  iunfold respAtP at Hr
  icases Hr with ⟨#Hra, #Hpks⟩
  ihave Hpre1 := respAt_isProgressPre v r $$ Hra
  wp_auto
  wp_apply (wp_IsPN wres_ptr v r (DFrac.own 1)) $$ [$wres $Hpre1] as wres
  iunfold watchStateRespOkP at Hok
  icases Hok with ⟨#Hok1, #Hpk⟩
  cases hpn : r.isProgressNotify
  · -- events (none, or the revisions `(c0, c1]`)
    ihave ⟨#Hevs, %Hseg⟩ : (eventsIs r.events
        (kRangeEvsL σ inS (sint.nat c0 + 1) (sint.nat c1 + 1)) ∗
        ⌜KRawSeg σ inS (sint.nat c0) (sint.nat c1)
            ((kRangeEvsL σ inS (sint.nat c0 + 1) (sint.nat c1 + 1)).map KRaw.ev) ∧
          0 ≤ sint.Z c1 ∧ (r.events ≠ [] → sint.nat c1 ≤ σ.rev)⌝ : IProp GF) $$ []
    · iunfold watchStateRespOk at Hok1
      icases Hok1 with (⟨%H, -⟩ | %H | %H | ⟨%H, #Hes⟩)
      · exact absurd H.1 hnw
      · obtain ⟨-, he, -, hc⟩ := H
        rw [hc]
        have h0 : kRangeEvsL σ inS (sint.nat c0 + 1) (sint.nat c0 + 1) = [] := by
          unfold kRangeEvsL; simp
        rw [h0, he]
        isplitl
        · unfold eventsIs
          isplitl
          · ipureintro; rfl
          iintro !> %i %e %ev %h
          simp at h
        ipureintro
        exact ⟨KRawSeg.nil _, Hc0, fun h => absurd rfl h⟩
      · rw [hpn] at H; exact absurd H.2.1 (by decide)
      · obtain ⟨-, hne, h0, hlt, hrv, -, -⟩ := H
        rw [← hscope]
        iframe Hes
        ipureintro
        have h1 : sint.nat c0 < sint.nat c1 := by word
        have h2 : sint.nat c1 ≤ σ.rev := by word
        rw [hscope]
        exact ⟨kRawSeg_chg1 h1 h2, by omega, fun _ => h2⟩
    obtain ⟨hsegS, hc1, hc1le⟩ := Hseg
    have hsegS' := kRawSeg_hist hhist hle hsegS
    generalize hevs : kRangeEvsL σ inS (sint.nat c0 + 1) (sint.nat c1 + 1) = evs at hsegS hsegS' ⊢
    iunfold respAt at Hra
    icases Hra with ⟨#HevA, -, -⟩
    iunfold eventsAt at HevA
    icases HevA with ⟨%ls, #Hls, %Hlen, #HevE⟩
    iunfold eventsPkAt at Hpks
    icases Hpks with ⟨%ls', #Hls', %Hlen', #HpkE⟩
    ihave %Hlseq := ownSlice_agree _ _ _ _ _ $$ Hls Hls'
    subst Hlseq
    iunfold eventsIs at Hevs
    icases Hevs with ⟨%HlenE, #HevI⟩
    ihave %Hsll := ownSlice_len $$ Hls
    wp_auto
    ihave IH2 : (∃ (n : w64) (e0 : Loc), "i" ∷ i_ptr ↦ n ∗ "e" ∷ e_ptr ↦ e0 ∗
        "Hps" ∷ kProdSt γ cd (I ++ (evs.map KRaw.ev).take (sint.nat n)) ∗
        "Hpe" ∷ dghostVar γ.prodEx (DFrac.own 1) false ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ls.length : Int)⌝ : IProp GF) $$ [i e Hps Hpe]
    · iexists W64 0, _
      simp only [named]
      iframe i e Hpe
      isplitl [Hps]
      · iExactEq Hps; rw [show sint.nat (W64 0) = 0 from rfl]; simp
      ipureintro; constructor
      · decide
      · simp
    wp_for IH2
    wp_if_destruct
    · -- the next event: parsed, then queued
      have hjl : sint.nat n < ls.length := by
        have h1 := Hsll.1; have h4 := Hn; simp only [sint.nat, sint.Z] at h1 h4 Hif ⊢; omega
      obtain ⟨l, hl⟩ : ∃ l, ls[sint.nat n]? = some l := ⟨_, List.getElem?_eq_getElem hjl⟩
      obtain ⟨ee, hee⟩ : ∃ e, r.events[sint.nat n]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact hjl)⟩
      obtain ⟨ev, hev⟩ : ∃ e, evs[sint.nat n]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [← HlenE, ← Hlen]; exact hjl)⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z v.Events'.len := ⟨Hn.1, Hif⟩
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z n) l v.Events' DFrac.discard ls Hn.1 hl $$ Hls with ⟨#Hle, -⟩
      ihave #Hea := HevE $$ %(sint.nat n) %l %ee %hl %hee
      ihave #Hei := HevI $$ %(sint.nat n) %ee %ev %hee %hev
      ihave #Hpkf := HpkE $$ %(sint.nat n) %l %ee %hl %hee
      have hev' : (σ.rangeEvents (opWatchModel kp (startOps recur (r1 + W64 1))).watchNorm
          (sint.nat c0 + 1) (sint.nat c1 + 1))[sint.nat n]? = some ev := by
        rw [hscope, hevs]; exact hev
      iunfold respPkOk at Hpk
      ihave #Hpko := Hpk $$ %(sint.nat n) %ee %ev %hee %hev'
      have hmr : sint.nat ev.kv.modRev - 1 ≤ σ.rev := by
        have hmem : ev ∈ kRangeEvsL σ inS (sint.nat c0 + 1) (sint.nat c1 + 1) := by
          rw [hevs]; exact List.mem_of_getElem? hev
        obtain ⟨-, rv, -, hrv, hmod⟩ := kRangeEvsL_mem hmem
        have hne : r.events ≠ [] := by intro h; rw [h] at hee; simp at hee
        have := hc1le hne
        have := sint_nat_W64_le rv
        rw [hmod]; omega
      ihave #Hpko' := prevKvOk_hist _ σ σ' ev ee.prevKv hhist hle hmr $$ Hpko
      ihave #Hea' := Hea
      iunfold EtcdGrove.eventAt at Hea'
      icases Hea' with ⟨%k0, -, -, -, -, -, %Hnn⟩
      wp_auto
      wp_apply (wp_RecordEtcdEvent c.gr Hutf.1 Hutf.2)
      (try wp_auto)
      wp_apply (wp_parseEvent l ee ev _ σ') $$ [] as %pe %perr Hpout
      · iframe #
        ipureintro; exact Hnn
      icases Hpout with (⟨%Hpe, %x, Hx, #Hkx⟩ | ⟨⟨%Hpe, -⟩, %x, %hx, #Hx⟩)
      rotate_left
      · -- the event without its previous key-value: logged and sent
        subst hx
        ihave #Hok := kErrOk_errorString wp_AsLeafTy x $$ Perr Hx
        (try wp_auto)
        wp_apply wp_logWatchChannelErr
        · iframe #
        (try wp_auto)
        wp_apply (wp_prod_sendError wp_sendError wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur q
          _) $$ [Hpe Halive] as Halive
        · iframe #
          iframe
        (try wp_auto)
        wp_for_post
        (try wp_auto)
        wp_for_post
        (try wp_auto)
        iapply HΦ
        iframe
      subst Hpe
      ipersist Hx
      ihave #Hepe : eventAt σ' pe (KRaw.ev ev) $$ []
      · iunfold eventAt
        iexists x
        iframe Hx Hkx
      have hjm : sint.nat n < (evs.map KRaw.ev).length := by
        rw [List.length_map, ← HlenE, ← Hlen]; exact hjl
      have hok : kRawStreamOk inS m σ' st
          (I ++ (evs.map KRaw.ev).take (sint.nat n) ++ [KRaw.ev ev]) := by
        have h := kProdAt_ok hat hsegS' (List.take_prefix (sint.nat n + 1) (evs.map KRaw.ev))
        rw [List.take_add_one, List.getElem?_map, hev] at h
        simpa [List.append_assoc] using h
      ihave ⟨%S, %Qs, Hsc, HQs, Hdrop⟩ := kProd_queue γ cd inS m Q chI pe _ _ lbc lb0 st σ' σ0 hst0 hok
        $$ Hspsc Hepe HQ' HQ0 Hps
      wp_auto
      wp_apply (wp_queueEvent wc chI lg ctx (kCdw γ cd) γ.inc.chanName pe S Qs) $$ [Hsc] as Hres
      · iframe #
        iexact Hsc
      ihave ⟨Hps, Hpe⟩ : (kProdSt γ cd (I ++ (evs.map KRaw.ev).take (sint.nat n) ++ [KRaw.ev ev]) ∗
          dghostVar γ.prodEx (DFrac.own 1) false : IProp GF) $$ [Hres HQs Hdrop Hpe]
      · icases Hres with (HQs' | ⟨#Hpd, HS⟩)
        · iframe Hpe
          iapply HQs $$ HQs'
        · ihave H2 := Hdrop $$ %1 HS
          iapply H2
          · iintro !>
            unfold kCdw
            iexact Hpd
          · iexact Hpe
      (try wp_auto)
      wp_for_post
      have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
        have h1 := Hsll.1; have h4 := Hn
        simp only [sint.nat, sint.Z] at h1 h4 Hif hjl ⊢; word
      iframe
      iexists n + W64 1, l
      simp only [named]
      iframe
      isplitl [Hps]
      · iExactEq Hps
        rw [hn1, List.take_add_one, List.getElem?_map, hev]
        simp [List.append_assoc]
      ipureintro
      have h1 := Hsll.1; have h4 := Hn
      simp only [sint.nat, sint.Z] at h1 h4 Hif hjl ⊢
      constructor <;> word
    · -- the response is queued: the next one
      have h2 : ¬ sint.Z n < sint.Z v.Events'.len := fun h => Hif (by simp [h])
      have hnl : sint.nat n = ls.length := by
        have h1 := Hsll.1
        have h3 := Hsll.2
        have h4 := Hn
        simp only [sint.nat, sint.Z] at h1 h2 h3 h4 ⊢; omega
      (try wp_auto)
      (try simp only [decide_eq_false h2])
      (try wp_auto)
      wp_for_post
      iframe
      iexists rs ++ [v], c1, I ++ evs.map KRaw.ev
      simp only [named]
      iframe
      isplitr; · iexact Hi1'
      isplitl [Hps]
      · iExactEq Hps
        rw [hnl, Hlen, HlenE, ← List.length_map (f := KRaw.ev), List.take_length]
      isplitr; · ipureintro; exact hc1
      ileft
      iexists lb0, lbc, σ0, σ'
      iframe HQ0 HQ'
      ipureintro
      exact ⟨hst0, kProdAt_step hat hsegS'⟩
  · -- a progress notification: `KRaw.bm` at the header's revision
    have hev0 := isProgressNotify_events hpn
    iunfold watchStateRespOk at Hok1
    icases Hok1 with (⟨%H, -⟩ | %H | %H | ⟨%H, -⟩)
    · exact absurd H.1 hnw
    · rw [hpn] at H; exact absurd H.2.2.1 (by decide)
    rotate_left
    · exact absurd hev0 H.2.1
    obtain ⟨-, -, h0, hle0, rfl, hrv, hnone, -⟩ := H
    iunfold respAt at Hra
    icases Hra with ⟨-, #Hhdr, -⟩
    wp_auto
    wp_apply (wp_GetRevision v.Header' r.hdrRev)
    · iframe #
    wp_apply wp_progressNotifyEvent as %p ⟨%ev, Hp, %Hpev⟩
    ipersist Hp
    have hseg : KRawSeg σ inS (sint.nat c0) (sint.nat r.hdrRev) [KRaw.bm (sint.nat r.hdrRev) false] := by
      apply kRawSeg_bm1
      · word
      · word
      · rw [← hscope]; exact hnone
    have hseg' := kRawSeg_hist hhist hle hseg
    have hok := kProdAt_ok hat hseg' (List.prefix_refl _)
    ihave #Hea : eventAt σ' p (KRaw.bm (sint.nat r.hdrRev) false) $$ []
    · iunfold eventAt
      iexists _
      iframe Hp
      unfold kEvIs
      ipureintro
      refine ⟨?_, Hpev.2.1, Hpev.2.2⟩
      rw [Hpev.1]; word
    ihave ⟨%S, %Qs, Hsc, HQs, Hdrop⟩ := kProd_queue γ cd inS m Q chI p _ I lbc lb0 st σ' σ0 hst0 hok
      $$ Hspsc Hea HQ' HQ0 Hps
    wp_apply (wp_queueEvent wc chI lg ctx (kCdw γ cd) γ.inc.chanName p S Qs) $$ [Hsc] as Hres
    · iframe #
      iexact Hsc
    ihave ⟨Hps, Hpe⟩ : (kProdSt γ cd (I ++ [KRaw.bm (sint.nat r.hdrRev) false]) ∗
        dghostVar γ.prodEx (DFrac.own 1) false : IProp GF) $$ [Hres HQs Hdrop Hpe]
    · icases Hres with (HQs' | ⟨#Hpd, HS⟩)
      · iframe Hpe
        iapply HQs $$ HQs'
      · ihave H2 := Hdrop $$ %1 HS
        iapply H2
        · iintro !>
          unfold kCdw
          iexact Hpd
        · iexact Hpe
    (try wp_auto)
    wp_apply (wp_RecordEtcdBookmark c.gr Hutf.1 Hutf.2)
    (try wp_auto)
    wp_for_post
    iframe
    iexists rs ++ [v], r.hdrRev, I ++ [KRaw.bm (sint.nat r.hdrRev) false]
    simp only [named]
    iframe
    isplitr; · iexact Hi1'
    isplitr; · ipureintro; word
    ileft
    iexists lb0, lbc, σ0, σ'
    iframe HQ0 HQ'
    ipureintro
    exact ⟨hst0, kProdAt_step hat hseg'⟩

end proof

end k8s
end EtcdGrove
end Perennial
