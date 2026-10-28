/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Range.lean`. Lean-first (no Rocq
counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Range
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVRead
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
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest__String
public import Spec.google_golang_org.protobuf.proto.Size
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Range
public import Spec.strconv.FormatBool
public import Spec.time.Duration__Seconds
public import Spec.github_com.prometheus.client_golang.prometheus.HistogramVec__WithLabelValues
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposerLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

theorem rangeResult_show (resp : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64) (crev : Int)
    (o : OpFull) (wt : Bool) :
    txn.rangeResult (GF := GF) resp err log rev crev o wt ⊢ rangeRespShow resp := by
  iunfold txn.rangeResult
  iunfold rangeRespShow
  iintro (⟨%H, -⟩ | ⟨%H, -⟩ | ⟨-, %kvs, %more, #Hr, -⟩ | ⟨%H, -⟩)
  · ileft; ipureintro; exact H.2
  · ileft; ipureintro; exact H.2.2.2.1
  · iunfold txn.rangeResponseIs at Hr
    icases Hr with ⟨-, %h, %sl, %ps, #Hh, -, #Hrv, #Hk, -⟩
    iright
    iexists h, sl, rev
    iframe #
  · ileft; ipureintro; exact H.2.2

/-- What `WarnOfExpensiveReadOnlyRangeRequest` needs of a range's answer (unit P4, 2026-10-14):
no response, or one whose `Kvs` it reads and whose `proto.Size` returns lent the header's id
fields (`rangeHdr`: a response comes with no error). -/
theorem rangeResult_warn (hSize : proto.Size.spec (GF := GF) (hG := hG))
    (resp : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64) (crev : Int) (o : OpFull)
    (wt : Bool) :
    txn.rangeResult (GF := GF) resp err log rev crev o wt ⊢
      ⌜resp = null⌝ ∨
        (∃ sl : GoSlice, structFieldRef etcdserverpb.RangeResponse go!"Kvs" resp ↦□ sl) ∗
        txn.sizeOk (interface.mkOk (go.GoType.PointerType etcdserverpb.RangeResponse.ty) #resp)
          (txn.rangeHdr resp err) := by
  iunfold txn.rangeResult
  iintro (⟨%H, -⟩ | ⟨%H, -⟩ | ⟨%H, %kvs, %more, #Hr, -⟩ | ⟨%H, -⟩)
  · ileft; ipureintro; exact H.2
  · ileft; ipureintro; exact H.2.2.2.1
  · iright
    ihave #Hr' := Hr
    iunfold txn.rangeResponseIs at Hr'
    icases Hr' with ⟨-, %h, %sl, %ps, -, -, -, #Hk, -⟩
    isplitl []
    · iexists sl; iexact Hk
    iunfold txn.sizeOk
    iintro !> %Φ !> ⟨#Hp, HP⟩ HΦ
    iunfold txn.rangeHdr at HP
    ihave Hh := HP $$ %H.2.1
    wp_apply (hSize.2.1 resp _ kvs more _) $$ [$Hp $Hr $Hh] as %n ⟨-, Hh⟩
    iapply HΦ
    iunfold txn.rangeHdr
    iintro -
    iexact Hh
  · ileft; ipureintro; exact H.2.2

instance readIndexOk_persistent_r (γr : ReadNames) (c : w64) :
    Persistent (readIndexOk (GF := GF) γr c) := by
  unfold readIndexOk; infer_instance

/-- A range's answer without error has a response. -/
theorem rangeResult_nil_ne (resp : Loc) (log : mvcc.Log) (rev : w64) (crev : Int) (o : OpFull)
    (wt : Bool) :
    txn.rangeResult (GF := GF) resp GoInterface.nil log rev crev o wt ⊢ ⌜resp ≠ null⌝ := by
  iunfold txn.rangeResult
  iintro (⟨-, %ef, -, %He⟩ | ⟨-, #He⟩ | ⟨-, %kvs, %more, #Hr, -⟩ | ⟨-, %ec, -, %He⟩)
  · cases He
  · ihave %Hn := mvcc.errorfIs_ne_nil _ $$ He
    exact absurd rfl Hn
  · iunfold txn.rangeResponseIs at Hr
    icases Hr with ⟨%Hn, -⟩
    ipureintro; exact Hn
  · cases He

/-- A range's error: no response, and one the gRPC layer can take (mvcc's `ErrFutureRev`, or
the context's `fmt.Errorf` error, by the leaf fact of `*errors.errorString`, or (M2, S1) mvcc's
`ErrCompacted`). -/
theorem rangeResult_errIs [_root_.Perennial.errors.Assumptions] (resp : Loc) (err : GoInterface)
    (log : mvcc.Log) (rev : w64) (crev : Int) (o : OpFull) (wt : Bool) (hne : err ≠ GoInterface.nil)
    (hleaf : ∀ x : Loc, errLeaf ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩) :
    errVarLeaf (GF := GF) go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ⊢
      errVarLeaf (GF := GF) go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted -∗
      txn.rangeResult resp err log rev crev o wt -∗ ⌜resp = null⌝ ∗ applyErrIs err := by
  iintro #Hv #Hvc
  iunfold txn.rangeResult
  iintro (⟨%H, %ef, #Hef, %He⟩ | ⟨%H, #He⟩ | ⟨%H, -⟩ | ⟨%H, %ec, #Hec, %He⟩)
  · isplitr
    · ipureintro; exact H.2
    iapply errVar_applyErrIs _ _ $$ Hv
    iexists ef; iframe Hef; ipureintro; exact He
  · isplitr
    · ipureintro; exact H.2.2.2.1
    iapply applyErrIs_errorf _ hleaf $$ He
  · exact absurd H.2.1 hne
  · isplitr
    · ipureintro; exact H.2.2
    iapply errVar_applyErrIs _ _ $$ Hvc
    iexists ec; iframe Hec; ipureintro; exact He

set_option hygiene false in
/-- The deferred closure from `LogIfLong` on, then the span's `End`. -/
local macro "range_defer_c" : tactic => `(tactic| (
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
/-- The deferred closure from the trace's fields on. -/
local macro "range_defer_b" : tactic => `(tactic| (
  wp_join with [resp trace Hown]
  · iunfold rangeRespShow at Hshow
    icases Hshow with (%Hn | ⟨%h, %sl, %rv', #HKvs, #Hhd, #Hrv⟩)
    · exact absurd Hn Hif
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨Hfs, -⟩
    (try wp_auto)
    icases Hown with ⟨%teA, HownA⟩
    wp_apply hAdd trc teA _ _ _ $$ [HownA Hfs] as ⟨HownA, -⟩
    · iframe HownA Hfs
      ipureintro
      exact traceutil.fieldsWf_cons_int _ _ _ (.int _) _
        (traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil)
    ihave Hown : iprop(∃ te, traceutil.ownTrace trc te) $$ [HownA]
    · iexists teA; iexact HownA
    wp_join_done
  range_defer_c))

set_option hygiene false in
/-- The deferred trace and metrics closure, then the span's `End` (at any return). -/
local macro "range_defer" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgn
  (try wp_auto)
  wp_apply (hWarn _ _ _ _ respv _ (txn.rangeHdr respv _)) $$ [Hhdr] as Hhdr
  · isplitr; · ipureintro; exact Hlgn
    isplitr; · iexact Hstr
    iframe Hhdr
    iapply rangeResult_warn hSize _ _ _ _ _ _ _ $$ Hres
  (try wp_auto)
  range_defer_b))

set_option hygiene false in
/-- From `doSerialize` on (`HriO`: the read index if linearizable). -/
local macro "range_tail" : tactic => `(tactic| (
  wp_apply (hDS s E ρ γr ctx2 _ _ _
    iprop(resp_ptr ↦ (null : Loc) ∗ err_ptr ↦ GoInterface.nil ∗ mvcc.storeReader E.s E.γ ∗
      srvLgReader s)
    iprop(∃ (respv : Loc) (errv : GoInterface) (log : mvcc.Log) (crev : Int), resp_ptr ↦ respv ∗
      err_ptr ↦ errv ∗ mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ mvcc.idxCert E.γ.idx log ∗
      mvcc.certOk E.γ log ∗ ⌜logR <+: log ∧ log.length + 0 + 3 ≤ 2 ^ 63 ∧ log ≠ []⌝ ∗
      txn.rangeResult respv errv log (W64 ((log.length : Int) - 1)) crev o true ∗
      txn.rangeHdr respv errv ∗ (∃ te, traceutil.ownTrace trc te))
    (fun info => apply.rangeClass E.authMode info o) trc false)
      $$ [resp err Hsr Hlr Hown0 Hard] as %serr Hds
  · iframe #
    isplitr
    · iintro %a %info %dq !> %Φ' ⟨Ha, Hard⟩ HΦ'
      wp_auto
      rw [Haui]
      (try wp_auto)
      wp_bind (App (App (App (Val _) (Val #a)) (Val #ksl)) (Val #esl))
      iapply HIRP $$ [Ha Hard]
      · iframe Ha Hks Hes Hard; ipureintro; exact Hkb
      inext
      iintro %perr ⟨Ha, -, -, Hard, #HpE0, -, #Hpv⟩
      ihave #HpE := authApplyErrIs_apply perr $$ HpE0
      wp_auto
      iapply HΦ'
      iframe Ha Hard HpE
      iintro %Hpn
      subst Hpn
      ihave %Hel := ownSlice_len _ _ _ $$ Hes
      unfold apply.rangeClass
      iexists e
      isplitl []
      · ipureintro; rw [Ho]; simp only [txn.rangeOpOf.proj_base]
        exact apply.authEndOf_rangeEndOf esl e Hel.1
      · rw [Ho]; simp only [txn.rangeOpOf.proj_key]
        iapply (apply.classRes_of_permVerdict E.authMode info k e .read) $$ Hpv
    isplitr
    · iintro !> %Φ' ⟨⟨Hresp, Herr, Hsr, Hlr⟩, Hown0⟩ HΦ'
      wp_auto
      wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
      · iframe #; iframe Hlr; ipureintro; exact Hlgn
      (try wp_auto)
      wp_apply hKV s w.kv $$ []
      · iframe #
      (try wp_auto)
      imod ownToks_0 (GF := GF) E.γ.revs with Hnone
      wp_apply (hRange ctx2 _ false w.lg w.kv E.s E.γ r o true 0 logR (some trc) false)
          $$ [Hsr Hnone Hown0]
        as %respv %trv %errv ⟨Hsr, -, %Htrv, Hown, %Hteq, %log, %rv, %crev, #Hcert, #Hrok, -, %Hlog, #Hres, Hhdr, -⟩
      · iframe # Hsr Hnone
        isplitl [Hown0]
        · simp only [traceutil.ownTraceOpt]; iexact Hown0
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr
        · itrivial
        isplitr
        · ipureintro; exact Hlgn
        isplitr
        · ipureintro; exact Hvst
        iintro !> %log' - #Hc'
        iunfold storeSmall at Hsmall
        ihave #Hs' := mvcc.idxCert_sealed _ _ $$ Hc'
        ihave %Hs := Hsmall $$ %log' Hs'
        ipureintro; intro _; exact Hs
      obtain ⟨Hl1, Hl2, Hl3, rfl, -⟩ := Hlog
      have htv := Hteq trc rfl rfl
      subst htv
      iapply HΦ'
      iexists respv, errv, log
      iframe
      iframe #
      ipureintro; exact ⟨Hl1, Hl2, Hl3⟩
    iframe
  icases Hds with ⟨Hard, (⟨%Hs0, ⟨%infoc, #Hcls⟩, %respv, %errv, %log, %crev, resp, err, Hsr, Hlr, #Hcert, #Hrok, %Hlog, #Hres, Hhdr, Hown⟩ |
    ⟨%Hs0, #HsE, Hg⟩)⟩
  · subst Hs0
    ihave #Hshow := rangeResult_show _ _ _ _ _ _ _ $$ Hres
    rcases errv with ei | _
    · range_defer
      ihave ⟨%Hrn0, #HeE⟩ := rangeResult_errIs _ _ _ _ _ _ _ (by intro h; cases h) Hleaf $$ HFut HCmp Hres
      iapply HΦ
      isplitl [Hsr Hlr Hrr Hard]
      · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
      iright
      iframe HeE
      ipureintro; exact ⟨Hrn0, by intro h; cases h⟩
    · wp_auto_lc 6
      ihave HQf : iprop(|={⊤}=> (if o.base.serializable then iprop(True) else
          ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModel γr.kv L = log⌝ ∗ □ Q L)) $$
          [Hlc1 Hlc2 Hlc3 Hlc4 Hlc5 Hlc6]
      · cases hso : o.base.serializable
        · simp only [hso, Bool.false_eq_true, ↓reduceIte]
          icases HwO with ⟨%g', #Hw'⟩
          ihave #Hw'' := readWitAt_mono γr Q g' logR log Hlog.1 $$ Hw'
          iapply readWit_fire s E γr Q g' log $$ Hainv Hkvi Hw'' Hrok
          iapply lc_join6 $$ Hlc1 Hlc2 Hlc3 Hlc4 Hlc5 Hlc6
        · simp only [hso, ↓reduceIte]
          imodintro; itrivial
      imod HQf with #HQf
      range_defer
      ihave %Hrn1 := rangeResult_nil_ne _ _ _ _ _ _ $$ Hres
      iapply HΦ
      isplitl [Hsr Hlr Hrr Hard]
      · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hrn1⟩
      isplitl [Hcls]
      · iexists infoc; iexact Hcls
      iunfold rangeReadOk
      ihave #Hres2 : iprop(∃ crev' : Int,
          txn.rangeResult respv GoInterface.nil log (W64 ((log.length : Int) - 1)) crev' o true) $$ []
      · iexists crev; iexact Hres
      iexists log
      iframe Hcert Hrok Hres2
      isplitr
      · ipureintro
        have := Hlog.1.length_le
        exact ⟨by omega, by omega, HFR.trans Hlog.1⟩
      isplitr
      · iapply (readLogOk_if_mono _ γr c logR log Hlog.1) $$ HriO
      isplitr
      · iexact HQf
      iunfold txn.rangeHdr at Hhdr
      iapply Hhdr
      ipureintro; rfl
  · cases serr with
    | nil => exact absurd rfl Hs0
    | ok sei =>
      icases Hg with (⟨⟨resp, err, Hsr, Hlr⟩, Hown0⟩ |
        ⟨%respv, %errv, %log, %crev, resp, err, Hsr, Hlr, #Hcert, #Hrok, %Hlog, #Hres, Hhdr, Hown⟩)
      · wp_auto
        ihave Hown : iprop(∃ te, traceutil.ownTrace trc te) $$ [Hown0]
        · iexists false; iexact Hown0
        wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
        · iframe #; iframe Hlr; ipureintro; exact Hlgn
        (try wp_auto)
        wp_apply (hWarn _ _ _ _ null _ iprop(True)) $$ []
        · isplitr; · ipureintro; exact Hlgn
          isplitr; · iexact Hstr
          isplitr; · itrivial
          ileft; ipureintro; rfl
        (try wp_auto)
        range_defer_c
        iapply HΦ
        isplitl [Hsr Hlr Hrr Hard]
        · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
        iright
        iframe HsE
        ipureintro; exact ⟨rfl, by intro h; cases h⟩
      · ihave #Hshow := rangeResult_show _ _ _ _ _ _ _ $$ Hres
        wp_auto
        range_defer
        iapply HΦ
        isplitl [Hsr Hlr Hrr Hard]
        · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
        iright
        iframe HsE
        ipureintro; exact ⟨rfl, by intro h; cases h⟩))

set_option hygiene false in
/-- `range_tail` with auth on (E3s): the check at the reader's lower bound (`HIRP` a
`permCheck3Lb`), the read at the mode-`on` model. -/
local macro "range_tailOn" : tactic => `(tactic| (
  wp_apply (hDS s E ρ γr ctx2 _ _ _
    iprop(resp_ptr ↦ (null : Loc) ∗ err_ptr ↦ GoInterface.nil ∗ mvcc.storeReader E.s E.γ ∗
      srvLgReader s)
    iprop(∃ (respv : Loc) (errv : GoInterface) (log : mvcc.Log) (crev : Int), resp_ptr ↦ respv ∗
      err_ptr ↦ errv ∗ mvcc.storeReader E.s E.γ ∗ srvLgReader s ∗ mvcc.idxCert E.γ.idx log ∗
      mvcc.certOk E.γ log ∗ ⌜logR <+: log ∧ log.length + 0 + 3 ≤ 2 ^ 63 ∧ log ≠ []⌝ ∗
      txn.rangeResult respv errv log (W64 ((log.length : Int) - 1)) crev o true ∗
      txn.rangeHdr respv errv ∗ (∃ te, traceutil.ownTrace trc te))
    (fun info => apply.rangeClassFrom E.authMode nA info o) trc false)
      $$ [resp err Hsr Hlr Hown0 Hard] as %serr Hds
  · iframe #
    isplitr
    · iintro %a %info %dq !> %Φ' ⟨Ha, Hard⟩ HΦ'
      wp_auto
      rw [Haui]
      (try wp_auto)
      wp_bind (App (App (App (Val _) (Val #a)) (Val #ksl)) (Val #esl))
      iapply HIRP $$ [Ha Hard]
      · iframe Ha Hks Hes Hard; ipureintro; exact Hkb
      inext
      iintro %perr ⟨Ha, -, -, Hard, #HpE0, #Hpv⟩
      ihave #HpE := authApplyErrIs_apply perr $$ HpE0
      wp_auto
      iapply HΦ'
      iframe Ha Hard HpE
      iintro %Hpn
      subst Hpn
      ihave %Hel := ownSlice_len _ _ _ $$ Hes
      unfold apply.rangeClassFrom
      iexists e
      isplitl []
      · ipureintro; rw [Ho]; simp only [txn.rangeOpOf.proj_base]
        exact apply.authEndOf_rangeEndOf esl e Hel.1
      · rw [Ho, hM]; simp only [txn.rangeOpOf.proj_key]
        iexact Hpv
    isplitr
    · iintro !> %Φ' ⟨⟨Hresp, Herr, Hsr, Hlr⟩, Hown0⟩ HΦ'
      wp_auto
      wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
      · iframe #; iframe Hlr; ipureintro; exact Hlgn
      (try wp_auto)
      wp_apply hKV s w.kv $$ []
      · iframe #
      (try wp_auto)
      imod ownToks_0 (GF := GF) E.γ.revs with Hnone
      wp_apply (hRange ctx2 _ false w.lg w.kv E.s E.γ r o true 0 logR (some trc) false)
          $$ [Hsr Hnone Hown0]
        as %respv %trv %errv ⟨Hsr, -, %Htrv, Hown, %Hteq, %log, %rv, %crev, #Hcert, #Hrok, -, %Hlog, #Hres, Hhdr, -⟩
      · iframe # Hsr Hnone
        isplitl [Hown0]
        · simp only [traceutil.ownTraceOpt]; iexact Hown0
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr
        · itrivial
        isplitr
        · ipureintro; exact Hlgn
        isplitr
        · ipureintro; exact Hvst
        iintro !> %log' - #Hc'
        iunfold storeSmall at Hsmall
        ihave #Hs' := mvcc.idxCert_sealed _ _ $$ Hc'
        ihave %Hs := Hsmall $$ %log' Hs'
        ipureintro; intro _; exact Hs
      obtain ⟨Hl1, Hl2, Hl3, rfl, -⟩ := Hlog
      have htv := Hteq trc rfl rfl
      subst htv
      iapply HΦ'
      iexists respv, errv, log
      iframe
      iframe #
      ipureintro; exact ⟨Hl1, Hl2, Hl3⟩
    iframe
  icases Hds with ⟨Hard, (⟨%Hs0, ⟨%infoc, #Hcls⟩, %respv, %errv, %log, %crev, resp, err, Hsr, Hlr, #Hcert, #Hrok, %Hlog, #Hres, Hhdr, Hown⟩ |
    ⟨%Hs0, #HsE, Hg⟩)⟩
  · subst Hs0
    ihave #Hshow := rangeResult_show _ _ _ _ _ _ _ $$ Hres
    rcases errv with ei | _
    · range_defer
      ihave ⟨%Hrn0, #HeE⟩ := rangeResult_errIs _ _ _ _ _ _ _ (by intro h; cases h) Hleaf $$ HFut HCmp Hres
      iapply HΦ
      isplitl [Hsr Hlr Hrr Hard]
      · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
      iright
      iframe HeE
      ipureintro; exact ⟨Hrn0, by intro h; cases h⟩
    · wp_auto_lc 6
      ihave HQf : iprop(|={⊤}=> (if o.base.serializable then iprop(True) else
          ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModelM true γr.kv L = log⌝ ∗ □ Q L)) $$
          [Hlc1 Hlc2 Hlc3 Hlc4 Hlc5 Hlc6]
      · cases hso : o.base.serializable
        · simp only [hso, Bool.false_eq_true, ↓reduceIte]
          icases HwO with ⟨%g', #Hw'⟩
          ihave #Hw'' := readWitAt_mono γr Q g' logR log Hlog.1 $$ Hw'
          iapply readWit_fireOn s E γr Q g' log $$ Hainv Hkvi Hw'' Hrok
          iapply lc_join6 $$ Hlc1 Hlc2 Hlc3 Hlc4 Hlc5 Hlc6
        · simp only [hso, ↓reduceIte]
          imodintro; itrivial
      imod HQf with #HQf
      range_defer
      ihave %Hrn1 := rangeResult_nil_ne _ _ _ _ _ _ $$ Hres
      iapply HΦ
      isplitl [Hsr Hlr Hrr Hard]
      · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hrn1⟩
      isplitl [Hcls]
      · iexists infoc, nA
        iframe Hcls
        isplitr
        · ipureintro; exact HnA
        rw [hM]; iexact Hfl
      iunfold rangeReadOkM
      ihave #Hres2 : iprop(∃ crev' : Int,
          txn.rangeResult respv GoInterface.nil log (W64 ((log.length : Int) - 1)) crev' o true) $$ []
      · iexists crev; iexact Hres
      iexists log
      iframe Hcert Hrok Hres2
      isplitr
      · ipureintro
        have := Hlog.1.length_le
        exact ⟨by omega, by omega, HFR.trans Hlog.1⟩
      isplitr
      · iapply (readLogOk_if_mono _ γr c logR log Hlog.1) $$ HriO
      isplitr
      · iexact HQf
      iunfold txn.rangeHdr at Hhdr
      iapply Hhdr
      ipureintro; rfl
  · cases serr with
    | nil => exact absurd rfl Hs0
    | ok sei =>
      icases Hg with (⟨⟨resp, err, Hsr, Hlr⟩, Hown0⟩ |
        ⟨%respv, %errv, %log, %crev, resp, err, Hsr, Hlr, #Hcert, #Hrok, %Hlog, #Hres, Hhdr, Hown⟩)
      · wp_auto
        ihave Hown : iprop(∃ te, traceutil.ownTrace trc te) $$ [Hown0]
        · iexists false; iexact Hown0
        wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
        · iframe #; iframe Hlr; ipureintro; exact Hlgn
        (try wp_auto)
        wp_apply (hWarn _ _ _ _ null _ iprop(True)) $$ []
        · isplitr; · ipureintro; exact Hlgn
          isplitr; · iexact Hstr
          isplitr; · itrivial
          ileft; ipureintro; rfl
        (try wp_auto)
        range_defer_c
        iapply HΦ
        isplitl [Hsr Hlr Hrr Hard]
        · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
        iright
        iframe HsE
        ipureintro; exact ⟨rfl, by intro h; cases h⟩
      · ihave #Hshow := rangeResult_show _ _ _ _ _ _ _ $$ Hres
        wp_auto
        range_defer
        iapply HΦ
        isplitl [Hsr Hlr Hrr Hard]
        · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
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
    (hDS : EtcdServer.doSerialize.spec (GF := GF) (hG := hG))
    (hRStr : RangeRequest.String.spec (GF := GF) (hG := hG))
    (hSize : proto.Size.spec (GF := GF) (hG := hG)) :
    EtcdServer.Range.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr c ctx cd r o ot te Q F
  wp_start as ⟨#Hsrv, #Hrd, Hcall, #Hctx, #Hct, Hto, #Hr, %Hvst, #Hdep, #HF⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hrd' := Hrd
  iunfold isServerRead at Hrd'
  icases Hrd' with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAt at Hw
  icases Hw with ⟨#Hread, #HisRead, #Hkvf, #HisKV, #Hrvf, #Hrv, #Hlef, #Hle, #Hauf, #Hau, #Hlgf,
    %Hlgn, #Hwad, #Hterm, #Hsmall, ⟨%log₀', #Hc0', %Hl0'⟩, #Hainv, #Hkvi, -⟩
  -- the floor (the vertical slice's unit V2): the read opens at a log extending both the
  -- server's initial log and the caller's floor `F`
  ihave ⟨%log₀, #Hc0, %HL0⟩ := idxCert_join E.γ.idx log₀' F $$ [$Hc0' $HF]
  have Hl0 : 2 ≤ log₀.length := Nat.le_trans Hl0' HL0.1.length_le
  iunfold srvRdCall at Hcall
  icases Hcall with ⟨Hsr, Hlr, #Hcal, Hrr, Hard⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨⟨%hist, #Hhist, %Hhl⟩, -, -, ⟨%tr, #Htr⟩, ⟨-, -, -, -, -, -, -, -, -, %Hleaf⟩⟩, -⟩
  ihave #Papply : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  ihave #HaInit : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Papply
  icases HaInit with ⟨-, -, ⟨-, -, -, -, #HFut, #HCmp, -⟩⟩
  ihave #Hstr : txn.stringerOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #r) $$ []
  · ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    iunfold txn.stringerOk
    iexists _
    isplitr; · ipureintro; rfl
    iintro !> %Φ' !> - HΦ'
    wp_apply (hRStr r o) $$ [] as %str -
    · iframe #
    iapply HΦ'
    itrivial
  ihave #Hr' := Hr
  iunfold txn.rangeRequestIs at Hr'
  icases Hr' with ⟨%Hrn, %ksl, %esl, %k, %e, %rev0, %limit, %order, %target, %ser, %ko, %co, %minM,
    %maxM, %minC, %maxC, #HK, #Hks, #HE, #Hes, #Hlim, #Hrev, -, -, #Hser, #Hko, #Hco, -, -, -, -, %Ho, %Hkb⟩
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
  wp_apply hTS tr ctx cd _ _ $$ [] as %ctx1 %sp ⟨⟨%vs1, #Hctx1t, Hctx1w⟩, #Hctr1, #Hsp⟩
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
  iintro %fsl ⟨Hfl, Hflc⟩
  (try wp_auto)
  wp_apply hET ctx1 _ ot te w.lg _ _ $$ [Hto Hfl Hflc]
    as %ctx2 %trc ⟨⟨%Htrc, -⟩, Hown0, #Hct2, %vs2, #Hctx2, -⟩
  · iframe #
    isplitr
    · iapply Hctr1 $$ Hct
    iframe Hto
    iunfold traceutil.ownFields
    iexists _
    iframe Hfl Hflc
    ipureintro
    exact traceutil.fieldsWf_cons_string _ _ _
      (traceutil.fieldsWf_cons_string _ _ _ traceutil.fieldsWf_nil)
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
  iunfold isReadNotify at HisRead'
  have Hser : o.base.serializable = ser := by subst Ho; rfl
  -- `if !r.Serializable { err = s.read.LinearizableReadNotify(ctx); trace.Step(..); if err != nil
  -- { return nil, err } }`, joined (`wp_join`): falling through, at a log `logR` the read opens at
  -- (the read index's if linearizable, the floor's `log₀` if serializable), or returning the read
  -- index's error; the rest of `Range` (`range_tail`) is verified once, not once per mode
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ logR : mvcc.Log, ⌜2 ≤ logR.length ∧ F <+: logR⌝ ∗
        mvcc.idxCert E.γ.idx logR ∗
        (if o.base.serializable then iprop(True) else readLogOk γr c logR) ∗
        (if o.base.serializable then iprop(True) else ∃ g' : GName, readWitAt γr Q g' logR) ∗
        err_ptr ↦ GoInterface.nil ∗ trace_ptr ↦ trc ∗ srvReadReader s γr ∗
        traceutil.ownTrace trc false) ∨
      (∃ rei : GoInterfaceOk, ⌜v = returnVal (PairV #Loc.null #(GoInterface.ok rei))⌝ ∗
        err_ptr ↦ GoInterface.ok rei ∗ trace_ptr ↦ trc ∗ srvReadReader s γr ∗
        traceutil.ownTrace trc false ∗ applyErrIs (GoInterface.ok rei))))
    at next with [err Hrr Hown0 trace]
  · cases ser
    · -- linearizable: the read index first
      (try wp_auto)
      iunfold srvReadReader at Hrr
      icases Hrr with ⟨%rd, #Hrd0, Hrr⟩
      icombine Hread Hrd0 gives %Hrdeq
      subst Hrdeq
      imod saved_pred_alloc Q DFrac.discard trivial with ⟨%g, #Hg⟩
      wp_apply HisRead' $$ %ctx2 %_ %c %g %Q [Hrr] as %rerr ⟨Hrr, #HrE, Hri⟩
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
        iright
        iexists rei
        isplitr
        · ipureintro; rfl
        iframe err trace Hrr Hown0 HrE
      | nil =>
        ihave #Hri' := Hri $$ %rfl
        icases Hri' with ⟨-, #Hsv⟩
        imod readServed_logR s E γr c g Q log₀ $$ Hainv Hsv Hg Hc0
          with ⟨%logR, #HcR, %HpR, #HrlR, #HwR⟩
        wp_auto
        ileft
        isplitr
        · ipureintro; rfl
        iexists logR
        isplitr
        · ipureintro; exact ⟨Nat.le_trans Hl0 HpR.length_le, HL0.2.trans HpR⟩
        iframe HcR err trace Hrr Hown0
        isplitr
        · rw [Hser]; simp only [Bool.false_eq_true, ↓reduceIte]; iexact HrlR
        rw [Hser]; simp only [Bool.false_eq_true, ↓reduceIte]; iexists g; iexact HwR
    · (try wp_auto)
      ileft
      isplitr
      · ipureintro; rfl
      iexists log₀
      isplitr
      · ipureintro; exact ⟨Hl0, HL0.2⟩
      iframe Hc0 err trace Hrr Hown0
      isplitr
      · rw [Hser]; simp only [↓reduceIte]; itrivial
      rw [Hser]; simp only [↓reduceIte]; itrivial
  iintro (⟨%Hv, %logR, %HlF, #HcR, #HriO, #HwO, err, trace, Hrr, Hown0⟩ |
    ⟨%rei, %Hv, err, trace, Hrr, Hown0, #HrE⟩)
  · subst Hv
    obtain ⟨HlR, HFR⟩ := HlF
    wp_auto
    range_tail
  · -- the read index's error: return
    subst Hv
    wp_auto
    ihave Hown : iprop(∃ te, traceutil.ownTrace trc te) $$ [Hown0]
    · iexists false; iexact Hown0
    wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
    · iframe #; iframe Hlr; ipureintro; exact Hlgn
    (try wp_auto)
    wp_apply (hWarn _ _ _ _ null _ iprop(True)) $$ []
    · isplitr; · ipureintro; exact Hlgn
      isplitr; · iexact Hstr
      isplitr; · itrivial
      ileft; ipureintro; rfl
    (try wp_auto)
    range_defer_c
    iapply HΦ
    isplitl [Hsr Hlr Hrr Hard]
    · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
    iright
    iframe HrE
    ipureintro; exact ⟨rfl, by intro h; cases h⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **`Range` with auth on** (`Range.specOn`; the auth plan's E3s): `wp_proof`'s, with the auth
check at the reader's lower bound and the read at the mode-`on` model. -/
theorem EtcdServer.Range.wp_proofOn
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
    (hDS : EtcdServer.doSerialize.specM (GF := GF) (hG := hG) true)
    (hRStr : RangeRequest.String.spec (GF := GF) (hG := hG))
    (hSize : proto.Size.spec (GF := GF) (hG := hG)) :
    EtcdServer.Range.specOn (GF := GF) (hG := hG) := by
  intro s E ρ γr c ctx cd r o ot te Q F n γa hM
  wp_start as ⟨#Hsrv, #Hrd, #HaLb, #Hpub, Hcall, #Hctx, #Hct, Hto, #Hr, %Hvst, #Hdep, #HF⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hrd' := Hrd
  iunfold isServerReadM at Hrd'
  icases Hrd' with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨#Hread, #HisRead, #Hkvf, #HisKV, #Hrvf, #Hrv, #Hlef, #Hle, #Hauf, #Hau, #Hlgf,
    %Hlgn, #Hwad, #Hterm, #Hsmall, ⟨%log₀', #Hc0', %Hl0'⟩, #Hainv, #Hkvi, -⟩
  -- the floor (the vertical slice's unit V2): the read opens at a log extending both the
  -- server's initial log and the caller's floor `F`
  ihave ⟨%log₀, #Hc0, %HL0⟩ := idxCert_join E.γ.idx log₀' F $$ [$Hc0' $HF]
  have Hl0 : 2 ≤ log₀.length := Nat.le_trans Hl0' HL0.1.length_le
  iunfold srvRdCall at Hcall
  icases Hcall with ⟨Hsr, Hlr, #Hcal, Hrr, Hard⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨⟨%hist, #Hhist, %Hhl⟩, -, -, ⟨%tr, #Htr⟩, ⟨-, -, -, -, -, -, -, -, -, %Hleaf⟩⟩, -⟩
  ihave #Papply : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  ihave #HaInit : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Papply
  icases HaInit with ⟨-, -, ⟨-, -, -, -, #HFut, #HCmp, -⟩⟩
  ihave #Hstr : txn.stringerOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #r) $$ []
  · ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    iunfold txn.stringerOk
    iexists _
    isplitr; · ipureintro; rfl
    iintro !> %Φ' !> - HΦ'
    wp_apply (hRStr r o) $$ [] as %str -
    · iframe #
    iapply HΦ'
    itrivial
  ihave #Hr' := Hr
  iunfold txn.rangeRequestIs at Hr'
  icases Hr' with ⟨%Hrn, %ksl, %esl, %k, %e, %rev0, %limit, %order, %target, %ser, %ko, %co, %minM,
    %maxM, %minC, %maxC, #HK, #Hks, #HE, #Hes, #Hlim, #Hrev, -, -, #Hser, #Hko, #Hco, -, -, -, -, %Ho, %Hkb⟩
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
  wp_apply hTS tr ctx cd _ _ $$ [] as %ctx1 %sp ⟨⟨%vs1, #Hctx1t, Hctx1w⟩, #Hctr1, #Hsp⟩
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
  iintro %fsl ⟨Hfl, Hflc⟩
  (try wp_auto)
  wp_apply hET ctx1 _ ot te w.lg _ _ $$ [Hto Hfl Hflc]
    as %ctx2 %trc ⟨⟨%Htrc, -⟩, Hown0, #Hct2, %vs2, #Hctx2, -⟩
  · iframe #
    isplitr
    · iapply Hctr1 $$ Hct
    iframe Hto
    iunfold traceutil.ownFields
    iexists _
    iframe Hfl Hflc
    ipureintro
    exact traceutil.fieldsWf_cons_string _ _ _
      (traceutil.fieldsWf_cons_string _ _ _ traceutil.fieldsWf_nil)
  (try wp_auto)
  wp_apply time.wp_Now as %start -
  (try wp_auto)
  ipersist s
  ipersist r
  ipersist ctx
  -- (E3s) the store's range check at the reader's lower bound `n`
  iunfold srvAuthLb at HaLb
  icases HaLb with ⟨%au, #Hauf2, #HLb⟩
  icombine Hauf Hauf2 gives %Hau2
  subst Hau2
  ihave #HLb' : iprop(□ ∀ n : Nat, auth.authPubLbM (.on γa) n -∗
      apply.isAuthStoreRangeLb w.auth E.RD (.on γa) n) $$ []
  · have hLb : authStoreLbM (GF := GF) E.authMode w.auth E.RD = iprop(□ ∀ n : Nat,
        auth.authPubLbM (.on γa) n -∗ apply.isAuthStoreRangeLb w.auth E.RD (.on γa) n) := by
      rw [hM]; rfl
    rw [← hLb]; iexact HLb
  ihave #Hpub' : auth.authPubLbM (GF := GF) (.on γa) n $$ []
  · rw [← hM]; iexact Hpub
  ihave #HisRead' := HisRead
  iunfold isReadNotify at HisRead'
  have Hser : o.base.serializable = ser := by subst Ho; rfl
  -- `if !r.Serializable { err = s.read.LinearizableReadNotify(ctx); trace.Step(..); if err != nil
  -- { return nil, err } }`, joined (`wp_join`): falling through, at a log `logR` the read opens at
  -- (the read index's if linearizable, the floor's `log₀` if serializable), or returning the read
  -- index's error; the rest of `Range` (`range_tail`) is verified once, not once per mode
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ logR : mvcc.Log, ⌜2 ≤ logR.length ∧ F <+: logR⌝ ∗
        mvcc.idxCert E.γ.idx logR ∗
        (if o.base.serializable then iprop(True) else readLogOk γr c logR) ∗
        (if o.base.serializable then iprop(True) else ∃ g' : GName, readWitAt γr Q g' logR) ∗
        err_ptr ↦ GoInterface.nil ∗ trace_ptr ↦ trc ∗ srvReadReader s γr ∗
        traceutil.ownTrace trc false ∗
        (∃ nA : Nat, ⌜n ≤ nA⌝ ∗ auth.authPubLbM (.on γa) nA ∗
          (if o.base.serializable then iprop(True) else authFloorAt (.on γa) γr c nA))) ∨
      (∃ rei : GoInterfaceOk, ⌜v = returnVal (PairV #Loc.null #(GoInterface.ok rei))⌝ ∗
        err_ptr ↦ GoInterface.ok rei ∗ trace_ptr ↦ trc ∗ srvReadReader s γr ∗
        traceutil.ownTrace trc false ∗ applyErrIs (GoInterface.ok rei))))
    at next with [err Hrr Hown0 trace]
  · cases ser
    · -- linearizable: the read index first
      (try wp_auto)
      iunfold srvReadReader at Hrr
      icases Hrr with ⟨%rd, #Hrd0, Hrr⟩
      icombine Hread Hrd0 gives %Hrdeq
      subst Hrdeq
      imod saved_pred_alloc Q DFrac.discard trivial with ⟨%g, #Hg⟩
      wp_apply HisRead' $$ %ctx2 %_ %c %g %Q [Hrr] as %rerr ⟨Hrr, #HrE, Hri⟩
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
        iright
        iexists rei
        isplitr
        · ipureintro; rfl
        iframe err trace Hrr Hown0 HrE
      | nil =>
        ihave #Hri' := Hri $$ %rfl
        icases Hri' with ⟨-, #Hsv⟩
        imod readServed_logRM true s E γr c g Q log₀ $$ Hainv Hsv Hg Hc0
          with ⟨%logR, #HcR, %HpR, #HrlR, #HwR, #HpF⟩
        -- (E3u) the check's floor: the auth state at the applied log through the read index
        ihave ⟨%nA, %HnA, #HnAlb, #Hfl⟩ := authFloor_of_pubFrom E γr γa c n hM $$ Hpub' HpF
        wp_auto
        ileft
        isplitr
        · ipureintro; rfl
        iexists logR
        isplitr
        · ipureintro; exact ⟨Nat.le_trans Hl0 HpR.length_le, HL0.2.trans HpR⟩
        iframe HcR err trace Hrr Hown0
        isplitr
        · rw [Hser]; simp only [Bool.false_eq_true, ↓reduceIte]; iexact HrlR
        isplitr
        · rw [Hser]; simp only [Bool.false_eq_true, ↓reduceIte]; iexists g; iexact HwR
        iexists nA
        iframe HnAlb
        isplitr
        · ipureintro; exact HnA
        rw [Hser]; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hfl
    · (try wp_auto)
      ileft
      isplitr
      · ipureintro; rfl
      iexists log₀
      isplitr
      · ipureintro; exact ⟨Hl0, HL0.2⟩
      iframe Hc0 err trace Hrr Hown0
      isplitr
      · rw [Hser]; simp only [↓reduceIte]; itrivial
      isplitr
      · rw [Hser]; simp only [↓reduceIte]; itrivial
      iexists n
      iframe Hpub'
      isplitr
      · ipureintro; exact Nat.le_refl _
      rw [Hser]; simp only [↓reduceIte]; itrivial
  iintro (⟨%Hv, %logR, %HlF, #HcR, #HriO, #HwO, err, trace, Hrr, Hown0, %nA, %HnA, #HnAlb, #Hfl⟩ |
    ⟨%rei, %Hv, err, trace, Hrr, Hown0, #HrE⟩)
  · subst Hv
    obtain ⟨HlR, HFR⟩ := HlF
    -- (E3s, E3u) the store's range check at the bound `nA ≥ n`
    ihave #Hau' := HLb' $$ %nA HnAlb
    iunfold apply.isAuthStoreRangeLb at Hau'
    icases Hau' with ⟨%aui, %Haui, #HIRP⟩
    iunfold apply.permCheck3Lb at HIRP
    wp_auto
    range_tailOn
  · -- the read index's error: return
    subst Hv
    wp_auto
    ihave Hown : iprop(∃ te, traceutil.ownTrace trc te) $$ [Hown0]
    · iexists false; iexact Hown0
    wp_apply hLg s w.lg $$ [Hlr] as ⟨-, Hlr⟩
    · iframe #; iframe Hlr; ipureintro; exact Hlgn
    (try wp_auto)
    wp_apply (hWarn _ _ _ _ null _ iprop(True)) $$ []
    · isplitr; · ipureintro; exact Hlgn
      isplitr; · iexact Hstr
      isplitr; · itrivial
      ileft; ipureintro; rfl
    (try wp_auto)
    range_defer_c
    iapply HΦ
    isplitl [Hsr Hlr Hrr Hard]
    · iunfold srvRdCall; iframe Hsr Hlr Hcal Hrr Hard
    iright
    iframe HrE
    ipureintro; exact ⟨rfl, by intro h; cases h⟩

end proof

end EtcdGrove
end Perennial
