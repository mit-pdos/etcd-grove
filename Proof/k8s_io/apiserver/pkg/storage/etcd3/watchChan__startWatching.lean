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

**PENDING (E2's remaining gap, for etcd-grove-81):** the client watch's close error. `kErrOk` of an
error response's `Err()` needs the close error to be a client error with its cell (`clientErr`,
`errCellOk`; `WatchResponse.Err` then gives them of its result), but the client watch's element
(`watchStateRespOk`) gives only `statusErrOk` of it. Until the client's watch spec says so, the proof
takes the stronger client watch as a hypothesis, `clientWatchCE.spec` (below): `client_Watch_field`'s
triple with `closeErrK` of each response's close error in the element.
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

section pending
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A watch response's close error is a client error** (PENDING, see the file header): `nil`, or a
client error (`clientErr`), and an `*errors.errorString` one is a cell of the client's messages
(`errCellOk`). -/
def closeErrK (e : GoInterface) : IProp GF :=
  iprop(⌜e ≠ GoInterface.nil → clientErr e⌝ ∗ go_etcd_io.etcd.cache.v3.errCellOk e)

instance closeErrK_persistent (e : GoInterface) : Persistent (closeErrK (GF := GF) e) := by
  unfold closeErrK; infer_instance

/-- **PENDING (E2's remaining gap)**: `client_Watch_field`'s triple with `closeErrK` of each
response's close error in the element. A hypothesis of `startWatching`'s proof until the client
watch's spec gives it (see the file header). -/
abbrev clientWatchCE.spec : Prop :=
  ∀ (cl w : Loc) (V : client.WEnv GF) (γ : KVNames) (ctx : GoInterfaceOk)
    (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (opts : List (OpFull → OpFull)) (rev : w64) (Q : KVState → IProp GF) (n : Nat),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        isPkgInit (PROP := IProp GF) pkg_id.context ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"Watcher" cl ↦□
          GoInterface.ok (client.watcherIfaceOf w) ∗
        client.isClientWatcher V w ∗ ⌜V.kst = γ.st⌝ ∗
        EtcdGrove.context.watchCtx ctx cd ∗ optsAt sl opts ∗
        ⌜(opWatchModel key opts).isRangeWatchP rev = true ∧ ¬ opWatchPanics key opts ∧
          1 ≤ sint.Z rev ∧ watchSizeOk (opWatchModel key opts)⌝ ∗
        □ (⌜V.nm = 1 ∧ 0 < n⌝ → auth.authPubLbM (V.mem 0).2.E.authMode n) ∗
        □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV γ σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Watch")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #sl))
    {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
        isSpsc γw.spsc ch (fun i v => iprop(watchStateElemP V.kv γw (opWatchModel key opts).watchNorm Q
          iprop(□ (⌜V.nm = 1⌝ → client.watchCheckOk (V.mem 0).2.tag (V.mem 0).2.s V.conn
            (GoInterface.ok ctx) n (opWatchModel key opts).key
            (opWatchModel key opts).base.rangeEnd)) i v ∗ closeErrK v.closeErr'))
          (fun _ => iprop(True)) ∗
        spscConsumer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
        monoListIdxOwn γw.cur 0 (rev - W64 1) }}

end pending

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
variable {Obj : Type} [DecidableEq Obj] [Pos.Countable Obj] [Pos.Countable KRaw]

/-- **`sendError`'s commit from a running producer of `resultChan`** (`kResChan`, `kResAlive`): the
token back on either outcome. -/
theorem kRes_errCommit (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γ : KWatchNames)
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

/-- The read updates at the members, as `GetCurrentResourceVersion` takes them. -/
theorem readAus_crv (c : StoreCfg GF Obj) (γk : KVNames) (Q : KVState → IProp GF) :
    readAus c γk Q ⊢ ∀ (R m' : w64), |==> □ [∧list] x ∈ c.ms,
      ⌜(fun (_ _ : w64) => Q) R m' = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv ((fun (_ _ : w64) => Q) R m') := by
  unfold readAus
  iintro ⟨-, #H⟩ %R %m'
  imodintro
  imodintro
  iapply (BigAndL.bigAndL_intro (P := iprop(□ [∗list] x ∈ c.ms, kvReadAu x.γr.kv Q))
    (fun k x hk => ?_)) $$ H
  iintro #H'
  ihave #Hx := BigSepL.bigSepL_lookup hk $$ H'
  iright
  iexact Hx

/-- **The producer exits** (before a `sendError` or the closing): `prodEx` set, for good. -/
theorem kProdExited_set (γ : KWatchNames) :
    ⊢ dghostVar (GF := GF) γ.prodEx (DFrac.own 1) false ==∗ kProdExited γ := by
  iintro Hd
  imod dghostVar_update true $$ Hd with Hd
  unfold kProdExited
  iapply dghostVar_persist $$ Hd

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- **The producer's `sendError`** (then it returns): `kProdExited` set first (`kCancelPD`'s producer
arm, for `wc.cancel()`), the commit from `kResChan`, the running-producer token back. -/
theorem wp_prod_sendError [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (wp_sendError : watchChan.sendError.spec (GF := GF) (hG := hG))
    {Obj : Type} [DecidableEq Obj] [Pos.Countable Obj] [Pos.Countable KRaw] (wc sp : Loc)
    (c : StoreCfg GF Obj) (W : WatchSpec Obj) (γ : KWatchNames) (cd : context.ContextDesc (IProp GF))
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
    (wp_WatchCE : clientWatchCE.spec (GF := GF) (hG := hG)) -- PENDING (file header)
    (wp_getRSE : store.getResourceSizeEstimator.spec (GF := GF) (hG := hG))
    (wp_Err : WatchResponse.Err.spec (GF := GF) (hG := hG))
    (wp_IsPN : WatchResponse.IsProgressNotify.spec (GF := GF) (hG := hG))
    (wp_GetRevision : ResponseHeader.GetRevision.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdBookmark : metrics.RecordEtcdBookmark.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdEvent : metrics.RecordEtcdEvent.spec (GF := GF) (hG := hG))
    (wp_parseEvent : parseEvent.spec (GF := GF) (hG := hG))
    (wp_logWatchChannelErr : logWatchChannelErr.spec (GF := GF) (hG := hG)) :
    watchChan.startWatching.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ _ _ wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur r0 q wcc γb
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
    wp_apply (wp_GetCRV Obj sp c ctx (kCdw γ cd) c.resourcePrefix (fun _ _ => Q 0) Hrp hrpl) $$ []
      as %n %err Hout
    · iframe #
      iapply readAus_crv $$ Hra
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
      wp_apply wp_TooLarge as %e ⟨-, %l, %st, %Hst, #Hl⟩
      obtain ⟨rfl, hst⟩ := Hst
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
      wp_apply (wp_sync Obj wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur r0 lbf 1 hQ hH hR
          hf (Hlbf hf)) $$ [Hir Hps Hpe] as %err ⟨Hpe, Hout⟩
      · iframe #
        iframe
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
  sorry

end proof

end k8s
end EtcdGrove
end Perennial
