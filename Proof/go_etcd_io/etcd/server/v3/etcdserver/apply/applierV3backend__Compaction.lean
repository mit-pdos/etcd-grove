/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart). Written for
etcd-io/etcd#22476 (`notes/pr-verify/etcd-22476.md`).

The range read `a.options.KV.Range(ctx, []byte("compaction"), nil, mvcc.RangeOptions{})` goes
through the store's promoted `ReadView` (a `readView`); `readView.Range`'s spec takes an
`isContext`, which `EnsureTrace(context.TODO(), ...)`'s context is not (its `Done()` is `nil`):
`readView_Range_todoNow` re-proves that read from `readView.Range`'s own callees at such a
context (`rangeCtx true`), at the current revision (`Rev: 0`), where it has no error and a result.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Compaction
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3
  go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- At the current revision (`ro.Rev = 0`, not `CountOnly`), a range read's outcome at a
compaction revision `crev` of the log (`crev < log.length`) with a result is no error and that
result, at the log's last revision. -/
theorem rangeOutcomeC_now (r : Loc) (err : GoInterface) (log : mvcc.Log) (crev : Int)
    (endNil : Bool) (k e : GoString) (ro : RangeOptions)
    (hne : log ≠ []) (hb : (log.length : Int) < 2 ^ 63) (hc : crev < log.length) (hro : ro.Rev' = W64 0) (hco : ro.CountOnly' = false)
    (hr : r ≠ null) :
    mvcc.rangeOutcomeC (GF := GF) r err log (W64 ((log.length : Int) - 1)) crev endNil k e ro ⊢
      ⌜err = GoInterface.nil⌝ ∗ ∃ (kvs : GoSlice) (cnt : w64),
        r ↦ ({ KVs' := kvs, Rev' := W64 ((log.length : Int) - 1), Count' := cnt } : RangeResult) := by
  have hlen : 0 < log.length := by
    cases log with
    | nil => exact absurd rfl hne
    | cons => simp
  have hrev : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by
    word
  iintro H
  iunfold mvcc.rangeOutcomeC at H
  icases H with (⟨%Hc, -, -⟩ | ⟨-, H⟩)
  · exfalso
    have hrr : mvcc.rangeRev (W64 ((log.length : Int) - 1)) ro.Rev' = W64 ((log.length : Int) - 1) := by
      unfold mvcc.rangeRev; rw [hro]; simp
    rw [hrr] at Hc
    omega
  iunfold mvcc.rangeOutcome at H
  icases H with (⟨%Hf, -, -⟩ | ⟨-, -, %Hn, -⟩ | ⟨-, %He, H⟩)
  · exfalso
    have h0 : sint.Z (W64 0) = 0 := by simp
    rw [hro, h0] at Hf; omega
  · exact absurd Hn hr
  rw [hco]
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases H with ⟨%kvs, Hr, -⟩
  isplitr
  · ipureintro; exact He
  iexists kvs, _
  iexact Hr

/-- **`rv.Range(ctx, key, end, ro)` at the current revision, at a context never canceled**
(`rangeCtx true`: `context.TODO()`'s or derived from it), not `CountOnly`: no error, and a result
at the last revision of a certified log, whose compaction revision is at least the caller's lower
bound `c` and a revision of the log. (`readView.Range`'s proof, at `rangeCtx true` instead of an
`isContext`, from its callees' specs.) -/
theorem readView_Range_todoNow
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hRange : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (rv s : Loc) (γ : mvcc.StoreNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions) (c : Int)
    (hro : ro.Rev' = W64 0) (hco : ro.CountOnly' = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.isReadView rv s γ ∗ mvcc.storeReaderC s γ ∗ mvcc.crevLb γ.idx c ∗
        mvcc.rangeCtx true ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
      (App (App (App (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Range"))
        (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
    {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
        mvcc.storeReaderC s γ ∗ ⌜err = GoInterface.nil⌝ ∗
        ∃ (log : mvcc.Log) (crev : Int) (kvs : GoSlice) (cnt : w64),
          mvcc.idxCert γ.idx log ∗ mvcc.crevLb γ.idx crev ∗
          ⌜log ≠ [] ∧ c ≤ crev ∧ crev < log.length⌝ ∗
          r ↦ ({ KVs' := kvs, Rev' := W64 ((log.length : Int) - 1), Count' := cnt } : RangeResult) }} := by
  wp_start as ⟨#Hrv, Hrd, #Hclb, #Hctx, #Hkey, #Hend⟩
  iunfold mvcc.isReadView at Hrv
  iNamed Hrv
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  imod ownToks_0 (GF := GF) γ.revs with Hnone
  imod mvcc.idxCert_nil (GF := GF) γ.idx with #Hc0
  wp_apply (hRead s γ _ t 0 [] true c iprop(True)) $$ [$Hs $Hrd $Hnone $Hc0 $Hclb $Htrc]
    as %mw ⟨%log, %rev, %crev, Htx, -, #Hlbc, #Hrok, %Hp⟩
  · isplitr
    · iintro !>; itrivial
    ipureintro; exact Ht
  (try wp_auto)
  ihave Htx : mvcc.isTxn mw s γ t (.read log rev) crev iprop(True) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  wp_apply (hRange t mw s γ (.read log rev) ctx cd true key endk k e ro crev iprop(True))
    $$ [$Htx $Hctx $Hkey $Hend] as %r %err ⟨%Hrn, Htx, Hout⟩
  (try wp_auto)
  simp only [mvcc.isTxn, mvcc.TxnKind.readLog, mvcc.TxnKind.readRev]
  iunfold mvcc.isTxnRead at Htx
  iNamed Htx
  ihave #HtrT := Htr
  iunfold mvcc.storeTxnReadIs at HtrT
  iNamedSuffix HtrT "T"
  ihave Htx : mvcc.isTxnRead mw s γ t log rev crev iprop(True) $$ [Hmw Htrw Hrd Hmu HrevMu Hti Htrc]
  · iunfold mvcc.isTxnRead
    iexists trw, tr, ti, rt, ranges
    iframe
    iframe #
  ihave Htx' : mvcc.isTxn mw s γ t (.read log rev) crev iprop(True) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave Htx' := mvcc.isTxn_toEnd _ _ _ _ crev iprop(True) $$ Htx'
  ihave Hep : mvcc.txnEndPre γ (.read log rev) $$ []
  · simp only [mvcc.txnEndPre]; itrivial
  wp_apply (hEnd t mw s γ (.read log rev) crev iprop(True)) $$ [$Htx' $Hep] as ⟨Hrd, -, -, -⟩
  (try wp_auto)
  subst HrevT
  have hb : (log.length : Int) < 2 ^ 63 := by have := Hp.2.1; omega
  ihave ⟨%He, %kvs, %cnt, Hr⟩ := rangeOutcomeC_now r err log crev _ k e ro HneT hb HcrevT.2 hro hco
    (Hrn rfl) $$ Hout
  iapply HΦ
  iframe Hrd
  isplitr
  · ipureintro; exact He
  iexists log, crev, kvs, cnt
  iframe HcertT Hlbc Hr
  ipureintro
  exact ⟨HneT, Hp.2.2, HcrevT.2⟩

theorem apply.applierV3backend.Compaction.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hCompact : mvcc.store.Compact.spec (GF := GF) (hG := hG))
    (hTTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hRange : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Compaction.spec (GF := GF) (hG := hG) := by
  intro E p cr rev c Pre Q Post log hcmp hc
  wp_start as ⟨#Hb, #Hcr, Hrd, Hstop, Hright, #Hcert, %Hlog, Hcs⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, #Hkv, #Hhook, -⟩
  iStructNamed Hopts
  iunfold apply.isApplyKV at Hkv
  icases Hkv with ⟨#HisKV, %rv, #HRV, #Hrv⟩
  iunfold txn.isKV at HisKV
  icases HisKV with ⟨%Hkveq, #Hst, %Hwq⟩
  iunfold apply.compactionIs at Hcr
  icases Hcr with ⟨%Hcrn, #Hrev⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  wp_auto
  wp_apply hTODO
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfsl, Hfslc⟩
  (try wp_auto)
  wp_apply (hEnsure todoCtxVal mvcc.neverCd none false opts.Logger' _ _) $$ [Hfsl Hfslc]
    as %ctx' %trace ⟨⟨%Ht, -⟩, Htrc, #Hct', %vs, #Hctx', -⟩
  · iframe #
    isplitr
    · iapply mvcc.txnCtx_todo
    isplitr
    · iapply traceutil.ctxTraceIs_todo
    isplitr
    · simp only [traceutil.ownTraceOpt]; itrivial
    iunfold traceutil.ownFields
    iexists _
    iframe Hfsl Hfslc
    ipureintro
    exact traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil
  (try wp_auto)
  -- `a.options.KV.Compact(trace, compaction.Revision)`: the store's
  rw [Hkveq]
  (try wp_auto)
  wp_apply (hCompact E.s E.γ trace rev c E.P E.f Pre Q Post log false Ht hcmp hc)
    $$ [$Hst $Hstop $Hright $Hcert $Hhook $Hcs $Htrc] as %ch %err ⟨Htrc, Hres⟩
  · ipureintro; exact Hlog
  icases Hres with (⟨⟨%Herr, %Hcr⟩, Hright, #Hlb, HPost, Hch⟩ | ⟨%Hle, ⟨%ec, #Hec, %Herr⟩, Hright, HPre, Hch⟩ |
    ⟨⟨%Hlt, %Hchn⟩, ⟨%ef, #Hef, %Herr⟩, -, Hright, HPre⟩)
  rotate_left
  · -- `ErrCompacted`
    subst Herr
    (try wp_auto)
    iapply HΦ
    iframe Hrd
    iright
    iframe Hright HPre
    isplitr
    · ipureintro; exact ⟨rfl, rfl, by simp⟩
    iright; iexact Hch
  · -- `ErrFutureRev`
    subst Herr
    (try wp_auto)
    iapply HΦ
    iframe Hrd
    iright
    iframe Hright HPre
    isplitr
    · ipureintro; exact ⟨rfl, rfl, by simp⟩
    ileft; ipureintro; exact Hchn
  subst Herr
  (try wp_auto)
  -- `a.options.KV.Range(ctx, []byte("compaction"), nil, mvcc.RangeOptions{})`: the store's
  -- `ReadView`'s, at a context never canceled, at the current revision
  wp_apply wp_string_to_bytes as %ksl ⟨Hksl, -⟩
  imod ownSlice_persist _ _ _ $$ Hksl with #Hksl
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave #Hnd : mvcc.neverDone (GF := GF)
      { Values := vs, Deadline := none, Done_gn := { doneGn := 0, closedGn := 0 }, PDone := iprop(False) } $$ []
  · iunfold mvcc.neverDone; imodintro; iintro H; iexact H
  ihave ⟨%td, %Htd, #Hrc⟩ : (∃ td : Bool, ⌜true = true → td = true⌝ ∗ mvcc.rangeCtx (GF := GF) td ctx'
      { Values := vs, Deadline := none, Done_gn := { doneGn := 0, closedGn := 0 }, PDone := iprop(False) })
      $$ []
  · iapply (mvcc.txnCtx_rangeCtx true ctx' _) $$ Hctx'
    simp only [↓reduceIte]
    iexact Hnd
  obtain rfl : td = true := Htd rfl
  (try wp_auto)
  (try rw [Hkveq])
  (try wp_auto)
  wp_method_call
  (try wp_auto)
  wp_apply (readView_Range_todoNow hTTODO hRead hRange hEnd rv E.s E.γ ctx' _ ksl slice.nil _ _ _
      (sint.Z rev) rfl rfl) $$ [$Hrd]
    as %rr %rerr ⟨Hrd, %Hrerr, %log', %crev, %kvs, %cnt, #Hcert', #Hlb', %Hlog', Hrr⟩
  · iframe #
  subst Hrerr
  (try wp_auto)
  irename «$r0» => Hhdr
  irename : ((_ : Loc) ↦ ({ state' := _, Header' := _, unknownFields' := _, sizeCache' := _ } :
    etcdserverpb.CompactionResponse)) => Hresp
  ihave %Hrn := typedPointsto_not_null $$ Hresp
  iStructNamedSuffix Hresp "R"
  iStructNamedSuffix Hhdr "H"
  iapply HΦ
  iframe Hrd
  ileft
  iframe Hright Hlb HPost Hch
  isplitr
  · ipureintro; exact ⟨rfl, Hcr, Hrn, Ht⟩
  isplitl [Htrc]
  · iexists false; iexact Htrc
  iexists _, log'
  iframe HeaderR RevisionH Hcert'
  ipureintro
  exact ⟨Hlog'.1, by have := Hlog'.2.1; have := Hlog'.2.2; omega⟩

end proof

end EtcdGrove
end Perennial
