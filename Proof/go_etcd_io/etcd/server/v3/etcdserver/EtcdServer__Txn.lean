/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Txn.lean`. Lean-first (no Rocq
counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Txn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVRead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__doSerialize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.firstCompareKey
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.firstOpKey
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.firstOpType
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.firstOpLease
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.TxnRequest__GetCompare
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.TxnRequest__GetSuccess
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.TxnRequest__GetFailure
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogIfLong
public import Spec.go_opentelemetry_io.otel.trace.WithAttributes
public import Spec.go_opentelemetry_io.otel.«attribute».String
public import Spec.go_opentelemetry_io.otel.«attribute».Int64
public import Spec.go_opentelemetry_io.otel.«attribute».Int
public import Spec.go_opentelemetry_io.otel.«attribute».Bool
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveReadOnlyTxnRequest
public import Spec.google_golang_org.protobuf.proto.Size
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.IsTxnReadonly
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.IsTxnSerializable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.CheckTxnAuth
public import Spec.context.WithValue
public import Spec.strconv.FormatBool
public import Spec.time.Duration__Seconds
public import Spec.github_com.prometheus.client_golang.prometheus.HistogramVec__WithLabelValues
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposerLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WrapLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchLemmas

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

instance readIndexOk_persistent_t (γr : ReadNames) (c : w64) :
    Persistent (readIndexOk (GF := GF) γr c) := by
  unfold readIndexOk; infer_instance

/-- A transaction check's error is one the gRPC layer can take (`applyErrVars`). -/
theorem checkErrIs_applyErrIs [_root_.Perennial.errors.Assumptions] (err : GoInterface) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      txn.checkErrIs err -∗ applyErrIs err := by
  iintro #Hv H
  iunfold txn.checkErrIs at H
  icases Hv with ⟨-, -, #HK, #HL, #HF, #HCp, -⟩
  icases H with (H | H | H | H)
  · iapply apply.errVarIs_errIs _ _ $$ HL H
  · iapply apply.errVarIs_errIs _ _ $$ HK H
  · iapply errVar_applyErrIs _ _ $$ HF H
  · iapply errVar_applyErrIs _ _ $$ HCp H

/-- What `WarnOfExpensiveReadOnlyTxnRequest` needs of a read-only transaction's response (unit
P4, 2026-10-14): its responses, and `proto.Size` of it, lent its header's id fields. -/
theorem txnResp_warn (hSize : proto.Size.spec (GF := GF) (hG := hG)) (resp : Loc) :
    txn.roTxnRespRd (GF := GF) resp ⊢
      txn.txnRespShow resp ∗
      txn.sizeOk (interface.mkOk (go.GoType.PointerType etcdserverpb.TxnResponse.ty) #resp)
        (txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp)) := by
  iintro #Hrd
  isplitr
  · iapply txn.txnRespShow_of_rd $$ Hrd
  iunfold txn.sizeOk
  iintro !> %Φ !> ⟨#Hp, Hh⟩ HΦ
  wp_apply (hSize.2.2 resp) $$ [$Hp $Hrd $Hh] as %n ⟨-, Hh⟩
  iapply HΦ $$ Hh

set_option hygiene false in
/-- The read-only transaction's deferred closure: the logger. -/
local macro "txn_defer_lg" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgn
  (try wp_auto)))

set_option hygiene false in
/-- The deferred `WarnOfExpensiveReadOnlyTxnRequest` without a response (`Hnull`). -/
local macro "txn_warn_null" : tactic => `(tactic| (
  wp_apply (hWarn _ _ _ r t _ _ iprop(True)) $$ []
  · isplitr; · ipureintro; exact Hlgn
    isplitr; · iexact Hrt
    isplitr; · itrivial
    ileft; ipureintro; first | rfl | exact Hnull))

set_option hygiene false in
/-- The deferred `WarnOfExpensiveReadOnlyTxnRequest` with the response `respv` (`Hrd`, read-only),
its header's id fields (`Hh`) lent. -/
local macro "txn_warn_rd" : tactic => `(tactic| (
  ihave ⟨#Hshw, #Hszw⟩ := txnResp_warn hSize respv $$ Hrd
  wp_apply (hWarn _ _ _ r t respv _
    (txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" respv))) $$ [Hh] as Hh
  · isplitr; · ipureintro; exact Hlgn
    isplitr; · iexact Hrt
    iframe Hh
    iright; iframe Hshw Hszw))

set_option hygiene false in
/-- The read-only transaction's deferred closure after `WarnOfExpensiveReadOnlyTxnRequest`
(`LogIfLong`, the metrics), then the span's `End`. -/
local macro "txn_defer" : tactic => `(tactic| (
  (try wp_auto)
  icases Hown with ⟨%teL, HownL⟩
  wp_apply hLong trc teL _ $$ [HownL]
  · iexact HownL
  (try wp_auto)
  wp_apply time.wp_Since as %_ -
  (try wp_auto)
  wp_apply hSec as %_ -
  (try wp_auto)
  wp_apply hFB as %fb %Hfb
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  (try wp_auto)
  wp_apply hWL hist _ [go!"type", go!"success"] _ _ $$ [Hlsl] as %_ ⟨%oi, %Hoi, #Hobs, -⟩
  · iframe #; iframe Hlsl; ipureintro
    refine ⟨Hhl, prometheus.labelValuesOk_two _ _ _ _ (by decide) ?_⟩
    rw [Hfb]; split <;> decide
  subst Hoi
  iunfold prometheus.observerSpec at Hobs
  (try wp_auto)
  wp_apply Hobs
  (try wp_auto)
  wp_apply HEnd
  (try wp_auto)))

set_option hygiene false in
/-- A read-only transaction's error answer (`HeE : applyErrIs err`). -/
local macro "txn_close_err" : tactic => `(tactic| (
  iapply HΦ
  iframe Hlt
  isplitl [Hsr Hlr Hrr Hard]
  · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
  (try rw [hro]); (try simp only [↓reduceIte])
  iframe Hcred
  iright
  iframe HeE
  ipureintro; intro h; cases h))

set_option hygiene false in
/-- The read-only transaction from the deferred closure's registration on (`HriO`: the read
index unless serializable). -/
local macro "txn_tail" : tactic => `(tactic| (
  wp_apply time.wp_Now as %start -
  (try wp_auto)
  wp_apply (hDS s E ρ γr ctx2 _ _ _
    iprop(resp_ptr ↦ (null : Loc) ∗ err_ptr ↦ GoInterface.nil ∗ mvcc.storeReader E.s E.γ ∗
      srvLgReader s)
    iprop(∃ (respv : Loc) (errv : GoInterface) (log : mvcc.Log), resp_ptr ↦ respv ∗
      err_ptr ↦ errv ∗ mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ mvcc.idxCert E.γ.idx log ∗
      mvcc.certOk E.γ log ∗ ⌜logR <+: log ∧ log.length + 0 + 3 ≤ 2 ^ 63 ∧ log ≠ []⌝ ∗
      ((⌜respv = null ∧ errv ≠ GoInterface.nil⌝ ∗ txn.checkErrIs errv) ∨
       (⌜errv = GoInterface.nil⌝ ∗
         txn.txnResponseIs false respv (W64 ((log.length : Int) - 1)) t
           (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
           (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
         txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" respv)) ∨
       (mvcc.errorfIs errv ∗ txn.roTxnRespRd respv ∗
         txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" respv))) ∗
      (∃ te, traceutil.ownTrace trc te)) trc false)
      $$ [resp err Hsr Hlr Hown0 Hard] as %serr Hds
  · iframe #
    isplitr
    · iintro %a %info %dq !> %Φ' ⟨Ha, Hard⟩ HΦ'
      wp_auto
      wp_apply (hCTA w.auth w.lessor E.γ E.P E.f E.RD E.authOn a info dq r t) $$ [Ha Hard] as %cerr ⟨Ha, Hard, #HcE, -⟩
      · iframe # Ha Hard
      iapply HΦ'
      iframe Ha Hard HcE
    isplitr
    · iintro !> %Φ' ⟨⟨Hresp, Herr, Hsr, Hlr⟩, Hown0⟩ HΦ'
      wp_auto
      wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
      · iframe #; iframe Hlr; ipureintro; exact Hlgn
      (try wp_auto)
      rw [Hfi]
      (try wp_auto)
      wp_apply HEn $$ [] as %en -
      · ipureintro; simp [serverFeatures]
      (try wp_auto)
      wp_apply hKV s w.kv $$ []
      · iframe #
      (try wp_auto)
      imod ownToks_0 (GF := GF) E.γ.revs with Hnone
      wp_apply (hTxn.2 ctx2 _ w.lg r en w.kv w.lessor false E.s E.γ 0 logR t (some trc) false)
          $$ [Hsr Hnone Hown0]
        as %respv %trv %errv ⟨Hsr, -, %log, #Hcert, #Hcok, %Hlog, Hres⟩
      · iframe # Hsr Hnone
        isplitl [Hown0]
        · simp only [traceutil.ownTraceOpt]; iexact Hown0
        isplitr
        · ipureintro; exact ⟨Hlgn, hro, Hg⟩
        iintro !> %log' - #Hc'
        iunfold storeSmall at Hsmall
        ihave #Hs' := mvcc.idxCert_sealed _ _ $$ Hc'
        iapply Hsmall $$ %log' Hs'
      iapply HΦ'
      iexists respv, errv, log
      iframe Hresp Herr Hsr Hlr Hcert Hcok
      isplitr
      · ipureintro; exact Hlog
      icases Hres with (⟨%H1, #Hce, %t', %te', Hown, %Hteq⟩ | ⟨%H2, Hown, %Hteq, #Hr, Hh⟩ |
        ⟨-, Hown, %Hteq, #He, #Hrd, Hh⟩)
      · have htv := Hteq trc (by simp) (by simp)
        subst htv
        isplitr [Hown]
        rotate_left
        · iexists te'; iexact Hown
        ileft; iframe Hce; ipureintro; exact ⟨H1.1, H1.2.2⟩
      · have htv := Hteq trc (by simp) (by simp)
        subst htv
        isplitr [Hown]
        rotate_left
        · iexact Hown
        iright; ileft
        isplitr
        · ipureintro; exact H2.1
        isplitl []
        · simp only [txn.srvRunTxn]; iexact Hr
        iexact Hh
      · have htv := Hteq trc (by simp) (by simp)
        subst htv
        isplitr [Hown]
        rotate_left
        · iexact Hown
        iright; iright; iframe He Hrd Hh
    iframe
  icases Hds with ⟨Hard, (⟨%Hs0, %respv, %errv, %log, resp, err, Hsr, Hlr, #Hcert, #Hcok, %Hlog, Hres, Hown⟩ |
    ⟨%Hs0, #HsE, Hg⟩)⟩
  · subst Hs0
    wp_auto_lc 3
    rcases errv with ei | _
    · icases Hres with (⟨%Hnull, #Hce⟩ | ⟨%Hn, -⟩ | ⟨#He, #Hrd, Hh⟩)
      · ihave #HeE : applyErrIs (GoInterface.ok ei) $$ []
        · iapply checkErrIs_applyErrIs $$ Hvars Hce
        replace Hnull := Hnull.1
        txn_defer_lg
        txn_warn_null
        txn_defer
        txn_close_err
      · cases Hn
      · ihave #HeE : applyErrIs (GoInterface.ok ei) $$ []
        · iapply applyErrIs_errorf _ Hleaf $$ He
        txn_defer_lg
        txn_warn_rd
        txn_defer
        txn_close_err
    · icases Hres with (⟨%Hn, -⟩ | ⟨-, #Hr, Hh⟩ | ⟨#He, -⟩)
      · exact absurd rfl Hn.2
      rotate_left
      · ihave %Hne := mvcc.errorfIs_ne_nil _ $$ He
        exact absurd rfl Hne
      ihave #Hrd := txn.roTxnRespRd_of _ _ _ t _ _ hro $$ Hr
      -- the read deposit's result at the log read (unit W-M3, as `Range`'s)
      ihave HQf : iprop(|={⊤}=> (if txn.txnSerializable t then iprop(True) else
          ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModel γr.kv L = log⌝ ∗ □ Qr L)) $$
          [Hlc1 Hlc2 Hlc3]
      · cases hso : txn.txnSerializable t
        · simp only [hso, Bool.false_eq_true, ↓reduceIte]
          icases HwO with ⟨%g', #Hw'⟩
          ihave #Hw'' := readWitAt_mono γr Qr g' logR log Hlog.1 $$ Hw'
          iapply readWit_fire s E γr Qr g' log $$ Hainv Hkvi Hw'' Hcok
          iapply (lc_split (n := 2) (m := 1)).2
          iframe Hlc3
          iapply (lc_split (n := 1) (m := 1)).2
          iframe Hlc1 Hlc2
        · simp only [hso, ↓reduceIte]
          imodintro; itrivial
      imod HQf with #HQf
      txn_defer_lg
      txn_warn_rd
      txn_defer
      ihave %Hrn' : ⌜respv ≠ null⌝ $$ []
      · ihave #Hr' := Hr
        iunfold txn.txnResponseIs at Hr'
        icases Hr' with ⟨%Hn, -⟩
        ipureintro; exact Hn
      iapply HΦ
      iframe Hlt
      isplitl [Hsr Hlr Hrr Hard]
      · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
      (try rw [hro]); (try simp only [↓reduceIte])
      iframe Hcred
      ileft
      isplitr
      · ipureintro; exact ⟨by first | rfl | trivial, Hrn'⟩
      iunfold txnReadOk
      iexists log
      iframe Hcert Hcok Hh
      isplitr
      · ipureintro
        have := Hlog.1.length_le
        exact ⟨by omega, by omega, HFR.trans Hlog.1⟩
      isplitr
      · iapply (readLogOk_if_mono _ γr c logR log Hlog.1) $$ HriO
      isplitr
      · iexact HQf
      simp only [txn.srvRunTxn]
      iexact Hr
  · cases serr with
    | nil => exact absurd rfl Hs0
    | ok sei =>
      ihave #HeE : applyErrIs (GoInterface.ok sei) $$ []
      · iexact HsE
      icases Hg with (⟨⟨resp, err, Hsr, Hlr⟩, Hown0⟩ |
        ⟨%respv, %errv, %log, resp, err, Hsr, Hlr, -, -, -, Hres, Hown⟩)
      · wp_auto
        ihave Hown : iprop(∃ te, traceutil.ownTrace trc te) $$ [Hown0]
        · iexists false; iexact Hown0
        txn_defer_lg
        txn_warn_null
        txn_defer
        txn_close_err
      · wp_auto
        rcases errv with ei | _
        · icases Hres with (⟨%Hnull, -⟩ | ⟨-, #Hr, Hh⟩ | ⟨-, #Hrd, Hh⟩)
          · replace Hnull := Hnull.1
            txn_defer_lg
            txn_warn_null
            txn_defer
            txn_close_err
          · ihave #Hrd := txn.roTxnRespRd_of _ _ _ t _ _ hro $$ Hr
            txn_defer_lg
            txn_warn_rd
            txn_defer
            txn_close_err
          · txn_defer_lg
            txn_warn_rd
            txn_defer
            txn_close_err
        · icases Hres with (⟨%Hnull, -⟩ | ⟨-, #Hr, Hh⟩ | ⟨-, #Hrd, Hh⟩)
          · replace Hnull := Hnull.1
            txn_defer_lg
            txn_warn_null
            txn_defer
            txn_close_err
          · ihave #Hrd := txn.roTxnRespRd_of _ _ _ t _ _ hro $$ Hr
            txn_defer_lg
            txn_warn_rd
            txn_defer
            txn_close_err
          · txn_defer_lg
            txn_warn_rd
            txn_defer
            txn_close_err))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem EtcdServer.Txn.wp_proof
    (hRO : txn.IsTxnReadonly.spec (GF := GF) (hG := hG))
    (hTS : traceutil.Tracer.Start.spec (GF := GF) (hG := hG))
    (hWA : trace.WithAttributes.spec (GF := GF) (hG := hG))
    (hGC : TxnRequest.GetCompare.spec (GF := GF) (hG := hG))
    (hFCK : firstCompareKey.spec (GF := GF) (hG := hG))
    (hAS : «attribute».String.spec (GF := GF) (hG := hG))
    (hGS : TxnRequest.GetSuccess.spec (GF := GF) (hG := hG))
    (hFOK : firstOpKey.spec (GF := GF) (hG := hG))
    (hFOT : firstOpType.spec (GF := GF) (hG := hG))
    (hFOL : firstOpLease.spec (GF := GF) (hG := hG))
    (hAI64 : «attribute».Int64.spec (GF := GF) (hG := hG))
    (hAI : «attribute».Int.spec (GF := GF) (hG := hG))
    (hGF : TxnRequest.GetFailure.spec (GF := GF) (hG := hG))
    (hAB : «attribute».Bool.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hET : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hSer : txn.IsTxnSerializable.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hCTA : apply.CheckTxnAuth.spec (GF := GF) (hG := hG))
    (hWarn : txn.WarnOfExpensiveReadOnlyTxnRequest.spec (GF := GF) (hG := hG))
    (hLong : traceutil.Trace.LogIfLong.spec (GF := GF) (hG := hG))
    (hFB : strconv.FormatBool.spec (GF := GF) (hG := hG))
    (hSec : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hWL : prometheus.HistogramVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hTxn : txn.Txn.spec (GF := GF) (hG := hG))
    (hDS : EtcdServer.doSerialize.spec (GF := GF) (hG := hG))
    (hWV : context.WithValue.spec (GF := GF) (hG := hG))
    (hRR : EtcdServer.raftRequest.spec (GF := GF) (hG := hG))
    (hSize : proto.Size.spec (GF := GF) (hG := hG)) :
    EtcdServer.Txn.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr c ctx cd r t Q Qr ot te F
  wp_start as ⟨#Hsrv, #Hrd, Hlt, Hcred, Hcall, #Hctx, #Hct, Hto, #Hrt, %Hgets, #HF, Hnp⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hrd' := Hrd
  iunfold isServerRead at Hrd'
  icases Hrd' with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAt at Hw
  icases Hw with ⟨#Hread, #HisRead, #Hkvf, #HisKV, #Hrvf, #Hrv, #Hlef, #Hle, #Hauf, #Hau, #Hlgf,
    %Hlgn, #Hwad, #Hterm, #Hsmall, ⟨%log₀', #Hc0', %Hl0'⟩, #Hainv, #Hkvi, -⟩
  -- the floor (the vertical slice's unit V2), as `Range`'s
  ihave ⟨%log₀, #Hc0, %HL0⟩ := idxCert_join E.γ.idx log₀' F $$ [$Hc0' $HF]
  have Hl0 : 2 ≤ log₀.length := Nat.le_trans Hl0' HL0.1.length_le
  iunfold srvRdCall at Hcall
  icases Hcall with ⟨Hsr, Hlr, #Hcal, Hrr, Hard⟩
  ihave #Hsrv' := Hsrv
  iunfold isServerReq at Hsrv'
  icases Hsrv' with ⟨%v, #Hv⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨-, -, -, -, -, -, #Hfgf, #Hfg, -⟩
  iunfold isFeatureGate at Hfg
  icases Hfg with ⟨%fi, %Hfi, #HEn⟩
  ihave #Hle' := Hle
  ihave #HleA := apply.isApplyLessorAny_of _ _ _ _ _ $$ Hle
  iunfold apply.isApplyLessor at Hle'
  icases Hle' with ⟨#HtLe, -⟩
  ihave #HisRead' := HisRead
  iunfold isReadNotify at HisRead'
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨⟨%hist, #Hhist, %Hhl⟩, -, -, ⟨%tr, #Htr⟩, ⟨-, -, -, -, -, -, -, -, -, %Hleaf⟩⟩, -⟩
  ihave #Papply : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  ihave #Ptxn : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn $$ []
  · iPkgInit
  ihave #HaInit : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Papply
  icases HaInit with ⟨-, -, #Hvars⟩
  ihave #Hrt' := Hrt
  iunfold txn.txnRequestIs at Hrt'
  icases Hrt' with ⟨%Hrn, #Hf⟩
  iunfold txn.txnFieldsIs at Hf
  icases Hf with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcs, #Hcm, #Hs, #Hss, #Hsm, #Hfl, #Hfs, #Hfm⟩
  (try wp_auto)
  wp_apply hRO r t $$ []
  · iframe #
  (try wp_auto)
  wp_apply hGC r csl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hFCK csl cps t.cmps $$ [] as %k1 -
  · iframe #
  (try wp_auto)
  wp_apply hAS as %a1 -
  (try wp_auto)
  wp_apply hGS r ssl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hFOK ssl sps t.thenOps $$ [] as %k2 -
  · iframe #
  (try wp_auto)
  wp_apply hAS as %a2 -
  (try wp_auto)
  wp_apply hGS r ssl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hFOT ssl sps t.thenOps $$ [] as %k3 -
  · iframe #
  (try wp_auto)
  wp_apply hAS as %a3 -
  (try wp_auto)
  wp_apply hGS r ssl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hFOL ssl sps t.thenOps $$ [] as %k4 -
  · iframe #
  (try wp_auto)
  wp_apply hAI64 as %a4 -
  (try wp_auto)
  wp_apply hGC r csl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hAI as %a5 -
  (try wp_auto)
  wp_apply hGS r ssl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hAI as %a6 -
  (try wp_auto)
  wp_apply hGF r fsl $$ []
  · iframe #; ipureintro; exact Hrn
  (try wp_auto)
  wp_apply hAI as %a7 -
  (try wp_auto)
  wp_apply hAB as %a8 -
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
  wp_apply hTS tr ctx cd _ _ $$ [] as %ctx1 %sp ⟨⟨%vs1, #Hctx1t, Hctx1w⟩, #Hctr1, #Hsp⟩
  · iframe #; iunfold mvcc.txnCtx; iright; iexact Hctx
  ihave #Hctx1 := Hctx1w $$ Hctx
  iunfold trace.isSpan at Hsp
  icases Hsp with ⟨%si, %Hsi, #HEnd, -, -⟩
  subst Hsi
  (try wp_auto)
  wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgn
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl' ⟨Hfl, Hflc⟩
  (try wp_auto)
  wp_apply hET ctx1 _ ot te w.lg _ _ $$ [Hto Hfl Hflc]
    as %ctx2 %trc ⟨⟨%Htrc, -⟩, Hown0, #Hct2, %vs2, #Hctx2, Hctx2w⟩
  · iframe #
    isplitr
    · iapply Hctr1 $$ Hct
    iframe Hto
    iunfold traceutil.ownFields
    iexists _
    iframe Hfl Hflc
    ipureintro
    exact traceutil.fieldsWf_cons_bool _ _ _ traceutil.fieldsWf_nil
  ihave #Hctx2i := Hctx2w $$ Hctx1
  (try wp_auto)
  cases hro : txn.txnReadonly t
  · -- a write: through raft, as `Put`
    (try wp_auto)
    wp_apply time.wp_Now as %now -
    (try wp_auto)
    wp_apply hWV ctx2 ⟨go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey.ty, _⟩ _ $$ [] as %c3 ⟨%Hc3, -, #Hc3w, -⟩
    · iframe #; ipureintro; right; right; left; rfl
    ihave ⟨%ctx3, %vs3, %Hc3e, #Hctx3⟩ := Hc3w $$ %_ Hctx2i
    subst Hc3e
    (try wp_auto)
    ihave ⟨Hirr, %Hirrn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$a1»
    iStructNamed Hirr
    ipersist ID
    ipersist Range
    ipersist Put
    ipersist DeleteRange
    ipersist Txn
    ipersist Compaction
    ipersist LeaseGrant
    ipersist LeaseRevoke
    ipersist Alarm
    ipersist LeaseCheckpoint
    ipersist AuthEnable
    ipersist AuthDisable
    ipersist AuthStatus
    ipersist Authenticate
    ipersist AuthUserAdd
    ipersist AuthUserDelete
    ipersist AuthUserGet
    ipersist AuthUserChangePassword
    ipersist AuthUserGrantRole
    ipersist AuthUserRevokeRole
    ipersist AuthUserList
    ipersist AuthRoleList
    ipersist AuthRoleAdd
    ipersist AuthRoleDelete
    ipersist AuthRoleGet
    ipersist AuthRoleGrantPermission
    ipersist AuthRoleRevokePermission
    ipersist ClusterVersionSet
    ipersist ClusterMemberAttrSet
    ipersist DowngradeInfoSet
    ipersist DowngradeVersionTest
    ihave #HirrNo : irrNoHdrIs «$a1_ptr» (irrTxn t) $$ []
    · iunfold irrNoHdrIs
      simp only [irrTxn, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField]
      isplitr
      · ipureintro; exact Hirrn
      isplitr
      · have h0 : (W64 0 : w64) = 0 := by decide
        rw [h0]; iexact ID
      repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
      iexists _; iframe #; try (ipureintro; simp)
    (try wp_auto)
    -- (2026-10-20, linkv-txn stage A) the token of the transaction's result
    imod kvResTok_alloc (GF := GF) with ⟨%γc, Htok⟩
    wp_apply hRR s E ρ ctx3 _ «$a1_ptr» (irrTxn t) (fun L => kvRes γc Q (kvStateOf (kvModel ρ.kv L)))
        F rfl
        $$ [Hlt Hard Hcred Header Hnp] as %resp %err ⟨Hlt, Hard, Hres⟩
    · iframe # Hlt Hard Hcred
      isplitl [Hnp]
      · (try isimp only [hro, Bool.false_eq_true, ↓reduceIte] at Hnp)
        iapply txnPermit_reqPropOk ρ.kv t Q γc $$ Hnp
      iexists _; iexact Header
    (try wp_auto)
    icases Hres with (⟨%Herr, %hm, %rq', %lb, %Hwire, Hok, %Lq, #HLq, %HLlb, #HQq⟩ | ⟨%Hre, #HaE, Hfail⟩)
    · subst Herr
      iunfold appliedOk at Hok
      icases Hok with ⟨%x, %x', %oc, %skip, %Hstep0, Hans, #Hcert, HMint, #Hwit, #Hcok⟩
      obtain ⟨Hstep, Hfl, Hxlb, Hskip⟩ := Hstep0
      have Hk : apply.dispatchKind rq' = .txn := by
        rw [Hwire.2.2.1]
        simp [apply.dispatchKind, apply.withHeader, irrTxn, apply.irrEmpty]
      have Hfl' := Hfl rfl (by unfold apply.isFloorKind; rw [Hk])
      iunfold apply.dispatchAnswer at Hans
      rw [Hk] at *
      icases Hans with ⟨%t', %pr, %Htp, Hpo⟩
      obtain ⟨Ht', Hresp⟩ := Htp
      subst Hresp
      ihave %Hap := apply.txnAnswerIs_nil _ _ _ _ _ $$ Hpo
      obtain ⟨log', rfl⟩ := Hap
      simp only [apply.txnAnswerIs]
      icases Hpo with ⟨Hpo, Hhdr⟩
      simp only [apply.txnOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte] at *
      icases Hpo with ⟨#Hpo, Hns⟩
      ihave %Hprn : ⌜pr ≠ null⌝ $$ []
      · ihave #Hr := Hpo
        iunfold txn.txnResponseIs at Hr
        icases Hr with ⟨%Hn, -⟩
        ipureintro; exact Hn
      wp_auto_lc 1
      -- the transaction's result, with its token
      imod kvRes_take γc Q _ ⊤ CoPset.subseteq_top $$ HQq Htok Hlc1 with HQ
      (try wp_auto)
      wp_apply HEnd
      (try wp_auto)
      iapply HΦ
      iframe Hlt
      isplitl [Hsr Hlr Hrr Hard]
      · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
      ileft
      isplitr
      · ipureintro; exact ⟨by first | rfl | trivial, Hprn⟩
      iunfold txnAppliedOk
      iexists hm, rq', t', x, x', log', skip
      simp only [apply.txnOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
      iframe Hhdr Hcert Hpo HMint Hwit Hcok
      isplitr
      rotate_left
      · rw [Hxlb, ← HLlb]; iexact HQ
      ipureintro
      refine ⟨Hwire, Ht', fun hz => ?_, Hstep, Hfl' log' false rfl, Hskip⟩
      have := Hwire.2.2.2 hz
      subst this
      simp [apply.withHeader, irrTxn] at Ht'
      exact Ht'.symm
    · obtain ⟨rfl, Hne⟩ := Hre
      (try wp_auto)
      rcases err with ei | _
      · (try wp_auto)
        wp_apply HEnd
        (try wp_auto)
        iapply HΦ
        iframe Hlt
        isplitl [Hsr Hlr Hrr Hard]
        · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
        simp only [Bool.false_eq_true, ↓reduceIte]
        iright
        isplitr
        · ipureintro; exact ⟨by first | rfl | trivial, Hne⟩
        iframe HaE
        iunfold txnErrOk
        iexact Hfail
      · exact absurd rfl Hne
  · -- read-only: as `Range`, through `doSerialize`
    have Hg := Hgets hro
    ipersist s
    ipersist r
    ipersist ctx
    (try wp_auto)
    wp_apply hSer r t $$ []
    · iframe #
    cases hs : txn.txnSerializable t
    · (try wp_auto)
      iunfold srvReadReader at Hrr
      icases Hrr with ⟨%rd, #Hrd0, Hrr⟩
      icombine Hread Hrd0 gives %Hrdeq
      subst Hrdeq
      imod saved_pred_alloc Qr DFrac.discard trivial with ⟨%g, #Hg⟩
      ihave #Hdep : kvDep (GF := GF) γr.kv Qr $$ [Hnp]
      · simp only [hro, ↓reduceIte]; iexact Hnp
      wp_apply HisRead' $$ %ctx2 %_ %c %g %Qr [Hrr]
        as %rerr ⟨Hrr, #HrE, Hri⟩
      · iframe #; iframe Hrr
      ihave Hrr : srvReadReader s γr $$ [Hrr]
      · iunfold srvReadReader; iexists _; iframe Hread Hrr
      (try wp_auto)
      wp_apply hStep trc false _ slice.nil $$ [$Hown0] as Hown0
      · iapply traceutil.ownFields_nil
      (try wp_auto)
      cases rerr with
      | ok rei =>
        wp_auto
        wp_apply HEnd
        (try wp_auto)
        iapply HΦ
        iframe Hlt
        isplitl [Hsr Hlr Hrr Hard]
        · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
        (try rw [hro]); (try simp only [↓reduceIte])
        iframe Hcred
        iright
        iframe HrE
        ipureintro; intro h; cases h
      | nil =>
        ihave #Hri' := Hri $$ %rfl
        icases Hri' with ⟨-, #Hsv⟩
        imod readServed_logR s E γr c g Qr log₀ $$ Hainv Hsv Hg Hc0
          with ⟨%logR, #HcR, %HpR, #HrlR, #HwR⟩
        ihave #HwO : (if txn.txnSerializable t then iprop(True) else
            ∃ g' : GName, readWitAt γr Qr g' logR : IProp GF) $$ []
        · rw [hs]; simp only [Bool.false_eq_true, ↓reduceIte]; iexists g; iexact HwR
        have HlR : 2 ≤ logR.length := Nat.le_trans Hl0 HpR.length_le
        have HFR : F <+: logR := HL0.2.trans HpR
        ihave #HriO : (if txn.txnSerializable t then iprop(True) else readLogOk γr c logR : IProp GF) $$ []
        · rw [hs]; simp only [Bool.false_eq_true, ↓reduceIte]; iexact HrlR
        wp_auto
        txn_tail
    · (try wp_auto)
      have HFR : F <+: log₀ := HL0.2
      generalize log₀ = logR at Hl0 HFR ⊢
      ihave #HriO : (if txn.txnSerializable t then iprop(True) else readLogOk γr c logR : IProp GF) $$ []
      · rw [hs]; simp only [↓reduceIte]; itrivial
      ihave #HwO : (if txn.txnSerializable t then iprop(True) else
          ∃ g' : GName, readWitAt γr Qr g' logR : IProp GF) $$ []
      · rw [hs]; simp only [↓reduceIte]; itrivial
      txn_tail

end proof

end EtcdGrove
end Perennial
