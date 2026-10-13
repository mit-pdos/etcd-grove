/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Range.lean`. Lean-first (no Rocq
counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__doSerialize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetKey
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetRangeEnd
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetRevision
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetLimit
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetCountOnly
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__GetKeysOnly
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__AddField
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogIfLong
public import Spec.go_opentelemetry_io.otel.trace.WithAttributes
public import Spec.go_opentelemetry_io.otel.«attribute».String
public import Spec.go_opentelemetry_io.otel.«attribute».Int64
public import Spec.go_opentelemetry_io.otel.«attribute».Bool
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveReadOnlyRangeRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Range
public import Spec.strconv.FormatBool
public import Spec.time.Duration__Seconds
public import Spec.github_com.prometheus.client_golang.prometheus.HistogramVec__WithLabelValues
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposerLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- What `Range`'s deferred trace reads of a response: `nil`, or its `Kvs`, `Header` and the
header's `Revision` (read-only). -/
def rangeRespShow (resp : Loc) : IProp GF :=
  iprop(⌜resp = null⌝ ∨ ∃ (h : Loc) (sl : GoSlice) (rv : w64),
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" resp ↦□ sl ∗
    structFieldRef etcdserverpb.RangeResponse go!"Header" resp ↦□ h ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rv)

instance rangeRespShow_persistent (resp : Loc) : Persistent (rangeRespShow (GF := GF) resp) := by
  unfold rangeRespShow; infer_instance

theorem rangeResult_show (resp : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64) (o : OpFull)
    (wt : Bool) : txn.rangeResult (GF := GF) resp err log rev o wt ⊢ rangeRespShow resp := by
  iunfold txn.rangeResult
  iunfold rangeRespShow
  iintro (⟨%H, -⟩ | ⟨%H, -⟩ | ⟨-, %kvs, %more, #Hr, -⟩)
  · ileft; ipureintro; exact H.2
  · ileft; ipureintro; exact H.2.2.2
  · iunfold txn.rangeResponseIs at Hr
    icases Hr with ⟨-, %h, %sl, %ps, #Hh, -, #Hrv, #Hk, -⟩
    iright
    iexists h, sl, rev
    iframe #

instance readIndexOk_persistent_r (γr : ReadNames) (c : w64) :
    Persistent (readIndexOk (GF := GF) γr c) := by
  unfold readIndexOk; infer_instance

instance ite_persistent_r (b : Bool) (P Q : IProp GF) [Persistent P] [Persistent Q] :
    Persistent (if b then P else Q) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- A range's answer without error has a response. -/
theorem rangeResult_nil_ne (resp : Loc) (log : mvcc.Log) (rev : w64) (o : OpFull) (wt : Bool) :
    txn.rangeResult (GF := GF) resp GoInterface.nil log rev o wt ⊢ ⌜resp ≠ null⌝ := by
  iunfold txn.rangeResult
  iintro (⟨-, %ef, -, %He⟩ | ⟨-, #He⟩ | ⟨-, %kvs, %more, #Hr, -⟩)
  · cases He
  · ihave %Hn := mvcc.errorfIs_ne_nil _ $$ He
    exact absurd rfl Hn
  · iunfold txn.rangeResponseIs at Hr
    icases Hr with ⟨%Hn, -⟩
    ipureintro; exact Hn

/-- A range's error: no response, and one the gRPC layer can take (mvcc's `ErrFutureRev`, or
the context's `fmt.Errorf` error, by the leaf fact of `*errors.errorString`). -/
theorem rangeResult_errIs [_root_.Perennial.errors.Assumptions] (resp : Loc) (err : GoInterface)
    (log : mvcc.Log) (rev : w64) (o : OpFull) (wt : Bool) (hne : err ≠ GoInterface.nil)
    (hleaf : ∀ x : Loc, errLeaf ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩) :
    errVarLeaf (GF := GF) go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ⊢
      txn.rangeResult resp err log rev o wt -∗ ⌜resp = null⌝ ∗ applyErrIs err := by
  iintro #Hv
  iunfold txn.rangeResult
  iintro (⟨%H, %ef, #Hef, %He⟩ | ⟨%H, #He⟩ | ⟨%H, -⟩)
  · isplitr
    · ipureintro; exact H.2
    iapply errVar_applyErrIs _ _ $$ Hv
    iexists ef; iframe Hef; ipureintro; exact He
  · isplitr
    · ipureintro; exact H.2.2.2
    iapply applyErrIs_errorf _ hleaf $$ He
  · exact absurd H.2 hne

set_option hygiene false in
/-- The deferred closure from `LogIfLong` on, then the span's `End`. -/
local macro "range_defer_c" : tactic => `(tactic| (
  wp_apply hLong trc _ $$ []
  · iframe #; ipureintro; exact Htrc
  (try wp_auto)
  wp_apply time.wp_Since as %_ -
  (try wp_auto)
  wp_apply hSec as %_ -
  (try wp_auto)
  wp_apply hFB as %_ -
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  (try wp_auto)
  wp_apply hWL hist as %_ ⟨%oi, %Hoi, #Hobs⟩
  subst Hoi
  iunfold prometheus.observerSpec at Hobs
  (try wp_auto)
  wp_apply Hobs
  (try wp_auto)
  wp_apply HEnd
  (try wp_auto)))

set_option hygiene false in
/-- The deferred closure from the trace's fields on. -/
local macro "range_defer_b" : tactic => `(tactic| (
  wp_join with [resp trace]
  · iunfold rangeRespShow at Hshow
    icases Hshow with (%Hn | ⟨%h, %sl, %rv', #HKvs, #Hhd, #Hrv⟩)
    · exact absurd Hn Hif
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨-, -⟩
    (try wp_auto)
    wp_apply hAdd trc _ $$ []
    · iframe #; ipureintro; exact Htrc
    wp_join_done
  range_defer_c))

set_option hygiene false in
/-- The deferred trace and metrics closure, then the span's `End` (at any return). -/
local macro "range_defer" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgn
  (try wp_auto)
  wp_apply hWarn
  (try wp_auto)
  range_defer_b))

set_option hygiene false in
/-- From `doSerialize` on (`HriO`: the read index if linearizable). -/
local macro "range_tail" : tactic => `(tactic| (
  wp_apply (hDS s E ρ γr ctx2 _ _ _
    iprop(resp_ptr ↦ (null : Loc) ∗ err_ptr ↦ GoInterface.nil ∗ mvcc.storeReader E.s E.γ ∗
      srvLgReader s)
    iprop(∃ (respv : Loc) (errv : GoInterface) (log : mvcc.Log), resp_ptr ↦ respv ∗
      err_ptr ↦ errv ∗ mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ mvcc.idxCert E.γ.idx log ∗
      ⌜log₀ <+: log ∧ log.length + 0 + 3 ≤ 2 ^ 63 ∧ log ≠ []⌝ ∗
      txn.rangeResult respv errv log (W64 ((log.length : Int) - 1)) o true ∗
      txn.rangeHdr respv errv)) $$ [resp err Hsr Hlr] as %serr Hds
  · iframe #
    isplitr
    · iintro %a %info %dq !> %Φ' Ha HΦ'
      wp_auto
      rw [Haui]
      (try wp_auto)
      wp_bind (App (App (App (Val _) (Val #a)) (Val #ksl)) (Val #esl))
      iapply HIRP $$ [Ha]
      · iframe Ha Hks Hes
      inext
      iintro %perr ⟨Ha, -, -, #HpE⟩
      wp_auto
      iapply HΦ'
      iframe Ha HpE
    isplitr
    · iintro !> %Φ' ⟨Hresp, Herr, Hsr, Hlr⟩ HΦ'
      wp_auto
      wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
      · iframe #; iframe Hlr; ipureintro; exact Hlgn
      (try wp_auto)
      wp_apply hKV s w.kv $$ []
      · iframe #
      (try wp_auto)
      imod ownToks_0 (GF := GF) E.γ.revs with Hnone
      wp_apply (hRange ctx2 _ false w.lg w.kv E.s E.γ r o true 0 log₀) $$ [Hsr Hnone]
        as %respv %trv %errv ⟨Hsr, -, %Htrv, %log, %rv, #Hcert, %Hlog, #Hres, Hhdr, -⟩
      · iframe # Hsr Hnone
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr
        · itrivial
        isplitr
        · ipureintro; exact Hlgn
        isplitr
        · ipureintro; exact Hvst
        iintro !> %log' - #Hc'
        iunfold storeSmall at Hsmall
        ihave %Hs := Hsmall $$ %log' Hc'
        ipureintro; intro _; exact Hs
      obtain ⟨Hl1, Hl2, Hl3, rfl⟩ := Hlog
      iapply HΦ'
      iexists respv, errv, log
      iframe
      iframe #
      ipureintro; exact ⟨Hl1, Hl2, Hl3⟩
    iframe
  icases Hds with (⟨%Hs0, %respv, %errv, %log, resp, err, Hsr, Hlr, #Hcert, %Hlog, #Hres, Hhdr⟩ |
    ⟨%Hs0, #HsE, Hg⟩)
  · subst Hs0
    ihave #Hshow := rangeResult_show _ _ _ _ _ _ $$ Hres
    rcases errv with ei | _
    · range_defer
      ihave ⟨%Hrn0, #HeE⟩ := rangeResult_errIs _ _ _ _ _ _ (by intro h; cases h) Hleaf $$ HFut Hres
      iapply HΦ
      isplitl [Hsr Hlr Hrr]
      · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr
      iright
      iframe HeE
      ipureintro; exact ⟨Hrn0, by intro h; cases h⟩
    · range_defer
      ihave %Hrn1 := rangeResult_nil_ne _ _ _ _ _ $$ Hres
      iapply HΦ
      isplitl [Hsr Hlr Hrr]
      · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hrn1⟩
      iunfold rangeReadOk
      iexists log
      iframe Hcert Hres
      isplitr
      · ipureintro
        have := Hlog.1.length_le
        exact ⟨by omega, by omega⟩
      isplitr
      · rw [Hser]; simp only [↓reduceIte]; itrivial
      iunfold txn.rangeHdr at Hhdr
      iapply Hhdr
      ipureintro; rfl
  · cases serr with
    | nil => exact absurd rfl Hs0
    | ok sei =>
      icases Hg with (⟨resp, err, Hsr, Hlr⟩ |
        ⟨%respv, %errv, %log, resp, err, Hsr, Hlr, #Hcert, %Hlog, #Hres, -⟩)
      · wp_auto
        wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
        · iframe #; iframe Hlr; ipureintro; exact Hlgn
        (try wp_auto)
        wp_apply hWarn
        (try wp_auto)
        range_defer_c
        iapply HΦ
        isplitl [Hsr Hlr Hrr]
        · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr
        iright
        iframe HsE
        ipureintro; exact ⟨rfl, by intro h; cases h⟩
      · ihave #Hshow := rangeResult_show _ _ _ _ _ _ $$ Hres
        wp_auto
        range_defer
        iapply HΦ
        isplitl [Hsr Hlr Hrr]
        · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr
        iright
        iframe HsE
        ipureintro; exact ⟨rfl, by intro h; cases h⟩))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem EtcdServer.Range.wp_proof
    (hTS : traceutil.Tracer.Start.spec (GF := GF) (hG := hG))
    (hWA : trace.WithAttributes.spec (GF := GF) (hG := hG))
    (hAS : «attribute».String.spec (GF := GF) (hG := hG))
    (hAI64 : «attribute».Int64.spec (GF := GF) (hG := hG))
    (hAB : «attribute».Bool.spec (GF := GF) (hG := hG))
    (hGK : RangeRequest.GetKey.spec (GF := GF) (hG := hG))
    (hGE : RangeRequest.GetRangeEnd.spec (GF := GF) (hG := hG))
    (hGR : RangeRequest.GetRevision.spec (GF := GF) (hG := hG))
    (hGL : RangeRequest.GetLimit.spec (GF := GF) (hG := hG))
    (hGC : RangeRequest.GetCountOnly.spec (GF := GF) (hG := hG))
    (hGKO : RangeRequest.GetKeysOnly.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hET : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hWarn : txn.WarnOfExpensiveReadOnlyRangeRequest.spec (GF := GF) (hG := hG))
    (hAdd : traceutil.Trace.AddField.spec (GF := GF) (hG := hG))
    (hLong : traceutil.Trace.LogIfLong.spec (GF := GF) (hG := hG))
    (hFB : strconv.FormatBool.spec (GF := GF) (hG := hG))
    (hSec : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hWL : prometheus.HistogramVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hRange : txn.Range.spec (GF := GF) (hG := hG))
    (hDS : EtcdServer.doSerialize.spec (GF := GF) (hG := hG)) :
    EtcdServer.Range.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr c ctx cd r o
  wp_start as ⟨#Hsrv, #Hrd, Hcall, #Hctx, #Hr, %Hvst⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hrd' := Hrd
  iunfold isServerRead at Hrd'
  icases Hrd' with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAt at Hw
  icases Hw with ⟨#Hread, #HisRead, #Hkvf, #HisKV, #Hrvf, #Hrv, #Hlef, #Hle, #Hauf, #Hau, #Hlgf,
    %Hlgn, #Hwad, #Hterm, #Hsmall, ⟨%log₀, #Hc0, %Hl0⟩⟩
  iunfold srvRdCall at Hcall
  icases Hcall with ⟨Hsr, Hlr, #Hcal, Hrr⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨⟨%hist, #Hhist⟩, -, -, ⟨%tr, #Htr⟩, ⟨-, -, -, -, -, -, -, -, %Hleaf⟩⟩⟩
  ihave #Papply : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  ihave #HaInit : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Papply
  icases HaInit with ⟨-, -, ⟨-, -, -, -, #HFut, -⟩⟩
  ihave #Hr' := Hr
  iunfold txn.rangeRequestIs at Hr'
  icases Hr' with ⟨%Hrn, %ksl, %esl, %k, %e, %rev0, %limit, %order, %target, %ser, %ko, %co, %minM,
    %maxM, %minC, %maxC, #HK, #Hks, #HE, #Hes, #Hlim, #Hrev, -, -, #Hser, #Hko, #Hco, -, -, -, -, %Ho⟩
  (try wp_auto)
  wp_apply hGK r ksl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [Hks] as -
  · iexact Hks
  (try wp_auto)
  wp_apply hAS as %a1 -
  (try wp_auto)
  wp_apply hGE r esl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [Hes] as -
  · iexact Hes
  (try wp_auto)
  wp_apply hAS as %a2 -
  (try wp_auto)
  wp_apply hGR r rev0 $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hAI64 as %a3 -
  (try wp_auto)
  wp_apply hGL r limit $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hAI64 as %a4 -
  (try wp_auto)
  wp_apply hGC r co $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hAB as %a5 -
  (try wp_auto)
  wp_apply hGKO r ko $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hAB as %a6 -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨-, -⟩
  (try wp_auto)
  wp_apply hWA as %opt -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨-, -⟩
  (try wp_auto)
  wp_apply hTS tr ctx cd _ _ $$ [] as %ctx1 %sp ⟨⟨%vs1, #Hctx1t, Hctx1w⟩, #Hsp⟩
  · iframe #; iunfold mvcc.txnCtx; iright; iexact Hctx
  iunfold trace.isSpan at Hsp
  icases Hsp with ⟨%si, %Hsi, #HEnd, -, -⟩
  subst Hsi
  (try wp_auto)
  wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgn
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [Hks] as -
  · iexact Hks
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [Hes] as -
  · iexact Hes
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply hET ctx1 _ w.lg _ _ $$ [] as %ctx2 %trc ⟨%Htrc, %vs2, #Hctx2, -⟩
  · iframe #
  (try wp_auto)
  wp_apply time.wp_Now as %start -
  (try wp_auto)
  ipersist s
  ipersist r
  ipersist ctx
  ihave #Hau' := Hau
  iunfold apply.isAuthStore at Hau'
  icases Hau' with ⟨%aui, %Haui, -, #HIRP, -⟩
  iunfold apply.permCheck3 at HIRP
  ihave #HisRead' := HisRead
  iunfold isRead at HisRead'
  have Hser : o.base.serializable = ser := by subst Ho; rfl
  cases ser
  · -- linearizable: the read index first
    (try wp_auto)
    iunfold srvReadReader at Hrr
    icases Hrr with ⟨%rd, #Hrd0, Hrr⟩
    icombine Hread Hrd0 gives %Hrdeq
    subst Hrdeq
    wp_apply HisRead' $$ %ctx2 %_ %c [Hrr] as %rerr ⟨Hrr, #HrE, Hri⟩
    · iframe #; iframe Hrr
    ihave Hrr : srvReadReader s γr $$ [Hrr]
    · iunfold srvReadReader; iexists _; iframe Hread Hrr
    (try wp_auto)
    wp_apply hStep trc _ _ $$ []
    · iframe #; ipureintro; exact Htrc
    (try wp_auto)
    cases rerr with
    | ok rei =>
      wp_auto
      wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
      · iframe #; iframe Hlr; ipureintro; exact Hlgn
      (try wp_auto)
      wp_apply hWarn
      (try wp_auto)
      range_defer_c
      iapply HΦ
      isplitl [Hsr Hlr Hrr]
      · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr
      iright
      iframe HrE
      ipureintro; exact ⟨rfl, by intro h; cases h⟩
    | nil =>
      ihave #Hri' := Hri $$ %rfl
      ihave #HriO : (if o.base.serializable then iprop(True) else readIndexOk γr c : IProp GF) $$ []
      · rw [Hser]; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hri'
      wp_auto
      range_tail
  · (try wp_auto)
    ihave #HriO : (if o.base.serializable then iprop(True) else readIndexOk γr c : IProp GF) $$ []
    · rw [Hser]; simp only [↓reduceIte]; itrivial
    range_tail

end proof

end EtcdGrove
end Perennial
