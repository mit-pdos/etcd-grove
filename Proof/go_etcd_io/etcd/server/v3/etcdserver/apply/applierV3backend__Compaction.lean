/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Compaction
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Compact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.readView__Range
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.KVView
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `store.Compact.spec` at a KV over the store (`kvOver_compact_wp`). -/
private theorem kvOver_Compact (hCompact : mvcc.store.Compact.spec (GF := GF) (hG := hG))
    (ty : go.GoType) (v : val) (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev : w64) (c : Int)
    (P : IProp GF) (f : val) (Pre Q Post : IProp GF) (log : mvcc.Log) (te : Bool)
    (ht : trace ≠ null) (hc : mvcc.storeCmp γ) (hc1 : -1 ≤ c) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.kvOver (interface.mkOk ty v) s ∗
        mvcc.isStore s γ ∗ mvcc.compactRightR s γ c ∗
        mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length⌝ ∗
        mvcc.hookIs γ P f ∗
        mvcc.csContract P f Pre Q Post ∗ traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗
        mvcc.kbWTSupplyM γ.kb }}
      (App (App (Val #(methods ty go!"Compact" v)) (Val #trace)) (Val #rev))
    {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); traceutil.ownTrace trace te ∗
        mvcc.storeRT γ ∗ mvcc.hookIs γ P f ∗
        ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.compactRightR s γ (sint.Z rev) ∗
          mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗ mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
        (⌜sint.Z rev ≤ c⌝ ∗
          (∃ ec : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□
            GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
          mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True))) }} := by
  iintro %Φ ⟨#Hpkg, #Hk, #Hs, Hr, #Hc, %Hl, Hhi, Hcs, Htrc, Hrt, #Hsup⟩ HΦ
  iapply mvcc.kvOver_compact_wp ty v s trace rev
  iframe Hk
  iapply (hCompact s γ trace rev c P f Pre Q Post log te ht hc hc1) $$ [Hr Hhi Hcs Htrc Hrt] HΦ
  iframe Hr Hhi Hcs Htrc Hrt; iframe #; ipureintro; exact Hl

/-- `readView.Range.spec` at a KV over the store (`kvOver_range_wp`, through the store's
`ReadView`). -/
private theorem kvOver_Range (hRange : mvcc.readView.Range.spec (GF := GF) (hG := hG))
    (ty : go.GoType) (v : val) (s rv : Loc) (γ : mvcc.StoreNames)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool) (key endk : GoSlice)
    (k e : GoString) (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) (c : Int) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.kvOver (interface.mkOk ty v) s ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.mvcc.store go!"ReadView" s ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty)
            #rv : GoInterface) ∗
        mvcc.isReadView rv s γ ∗ mvcc.storeReaderC s γ ∗ mvcc.crevLb γ.idx c ∗
        mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
      (App (App (App (App (Val #(methods ty go!"Range" v)) (Val #(GoInterface.ok ctx))) (Val #key))
        (Val #endk)) (Val #ro))
    {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
        ⌜todo = true → r ≠ null⌝ ∗ mvcc.storeReaderC s γ ∗
        ∃ (log : mvcc.Log) (rev : w64) (crev : Int), mvcc.idxCert γ.idx log ∗ mvcc.crevLb γ.idx crev ∗
          ⌜log ≠ [] ∧ rev = W64 ((log.length : Int) - 1) ∧ c ≤ crev ∧ -1 ≤ crev⌝ ∗
          mvcc.rangeOutcomeC r err log rev crev (decide (endk = slice.nil)) k e ro }} := by
  iintro %Φ ⟨#Hpkg, #Hk, #HrvA, #Hrv, Hrd, #Hc, #Hctx, #Hkey, #Hend⟩ HΦ
  iapply mvcc.kvOver_range_wp ty v s rv (GoInterface.ok ctx) key endk ro
  iframe Hk HrvA
  iapply (hRange rv s γ ctx cd todo key endk k e ro c) $$ [Hrd] HΦ
  iframe Hrd; iframe #

/-- A range's result that is not `nil` is owned (whichever outcome; `CountOnly` false). -/
private theorem rangeOutcomeC_res (r : Loc) (err : GoInterface) (log : mvcc.Log) (rev : w64) (c : Int)
    (en : Bool) (k e : GoString) (ro : go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions)
    (hro : ro.CountOnly' = false) (hr : r ≠ null) :
    mvcc.rangeOutcomeC (GF := GF) r err log rev c en k e ro ⊢
      ∃ v : go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult, r ↦ v := by
  unfold mvcc.rangeOutcomeC mvcc.rangeOutcome
  simp only [hro, Bool.false_eq_true, ↓reduceIte]
  iintro (⟨-, -, H⟩ | ⟨-, (⟨-, -, H⟩ | ⟨-, -, %Hn, -⟩ | ⟨-, -, %kvs, H, -⟩)⟩)
  · iexists _; iexact H
  · iexists _; iexact H
  · exact absurd Hn hr
  · iexists _; iexact H

theorem apply.applierV3backend.Compaction.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hCompact : mvcc.store.Compact.spec (GF := GF) (hG := hG))
    (hRange : mvcc.readView.Range.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Compaction.spec (GF := GF) (hG := hG) := by
  intro E p cr rev log crev Pre Q Post info
  wp_start as ⟨#Hb, #Hcr, %Hadm, Hpre, Hc⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  ihave #Hok' := Hok
  iunfold apply.backendOptsOk at Hok'
  icases Hok' with ⟨%Hlg, #Hkv, #Hhk, -⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkvo, -, Hcs⟩
  iunfold apply.compactionIs at Hcr
  icases Hcr with ⟨%Hcrn, #Hrev⟩
  iStructNamed Hopts
  wp_auto
  ihave ⟨Hresp0, %Hrespn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  wp_apply hTODO
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfl, Hflc⟩
  wp_auto
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_apply hEnsure todoCtxVal mvcc.neverCd none false opts.Logger' _ _ $$ [Hfl Hflc]
    as %ctx2 %trc ⟨⟨%Htrcnn, -⟩, Htrc, #Hct2, -, %vs2, #Hctx2t, -⟩
  · isplitr
    · iapply mvcc.txnCtx_todo
    isplitr
    · iapply traceutil.ctxTraceIs_todo
    isplitr
    · unfold traceutil.ownTraceOpt; itrivial
    iunfold traceutil.ownFields
    iexists _
    iframe Hfl Hflc
    ipureintro
    exact traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil
  -- `a.kv.Compact(trace, rev)`: the store's (`store.Compact.spec`), its precondition from the
  -- apply thread's KV and compaction resources (`cmp_store_pre`)
  iunfold apply.isApplyKV at Hkv
  icases Hkv with ⟨#Hkv, %rv, #HrvA, #Hrv⟩
  ihave ⟨#Hko, #Hs⟩ := txn.isKV_kvOver _ E.s E.γ $$ Hkv
  ihave %Hkvok := mvcc.kvOver_ok _ E.s $$ Hko
  obtain ⟨kty, kvv, Hkveq⟩ := Hkvok
  ihave %Hcge := apply.cmpOwn_ge E crev $$ Hc
  ihave ⟨Hr, %Hc1, #Hcert, Hhi, Hrt, #Hsup, Hback⟩ :=
    apply.cmp_store_pre E log crev Hadm.1 $$ [$Hkvo $Hc $Hhk]
  rw [Hkveq]
  simp only [interface.mkOk]
  ihave #Hmi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  wp_apply (kvOver_Compact hCompact kty kvv E.s E.γ trc rev crev E.P E.f Pre Q Post log false
      Htrcnn Hadm.1 Hc1) $$ [$Hr $Hhi $Hcs $Htrc $Hrt] as %ch %err ⟨Htrc, Hrt, Hhi, Hout⟩
  · iframe #; ipureintro; exact Hadm.2
  icases Hout with (⟨%Herr, Hr, #Hlb, HPost, -⟩ | ⟨%Hle, ⟨%ec, #Hec, %Herr⟩, Hr, HPre, -⟩)
  · -- compacted: `KV.Range(context.TODO(), "compaction", nil, {})` for the header
    obtain ⟨Herr, Hlt⟩ := Herr
    subst Herr
    wp_auto
    -- the context `EnsureTrace` returned is never done (`TODO`'s, with the trace)
    ihave #Hnd : mvcc.neverDone
        ({ Values := vs2, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(False) } :
          context.ContextDesc (IProp GF)) $$ []
    · unfold mvcc.neverDone; imodintro; iintro H; iexact H
    ihave #Hnd' : iprop(if true = true then mvcc.neverDone
        ({ Values := vs2, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(False) } :
          context.ContextDesc (IProp GF)) else iprop(True)) $$ []
    · simp only [↓reduceIte]; iexact Hnd
    ihave ⟨%td, %Htd, #Hrc⟩ := mvcc.txnCtx_rangeCtx true ctx2 _ $$ Hctx2t Hnd'
    have htd : td = true := Htd rfl
    subst htd
    ihave Hkvo := Hback $$ Hr [] Hhi Hrt
    · ipureintro; omega
    icases Hkvo with ⟨Hkvo, Hc⟩
    iunfold apply.kvOwn at Hkvo
    icases Hkvo with ⟨Hsr, Hkvo⟩
    ihave Hsr := mvcc.storeReader_toC E.s E.γ $$ Hsr
    wp_apply wp_string_to_bytes as %ksl ⟨Hks, -⟩
    imod ownSlice_persist _ _ _ $$ Hks with #Hks
    ihave #Hes : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod mvcc.crevLb_neg E.γ.idx with #Hlb0
    wp_apply (kvOver_Range hRange kty kvv E.s rv E.γ ctx2 _ true ksl slice.nil _ []
        (zero_val go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) (-1)) $$ [$Hsr]
      as %rr %rerr ⟨%Hrrn, Hsr, %rlog, %rrev, %rcrev, -, -, -, Hrout⟩
    · iframe #
    ihave ⟨%rv0, Hrr⟩ := rangeOutcomeC_res rr rerr rlog rrev rcrev _ _ _ _ rfl (Hrrn rfl) $$ Hrout
    ihave Hsr := mvcc.storeReader_of E.s E.γ $$ Hsr
    wp_auto
    iapply HΦ
    isplitl [Hsr Hkvo]
    · iunfold apply.kvOwn; iframe Hsr Hkvo
    isplitl [HPost]
    · ileft; iexact HPost
    have hra : apply.cmpRevAfter crev rev = sint.Z rev := by
      unfold apply.cmpRevAfter; simp [Hlt]
    rw [hra]
    iframe Hc
    simp only [apply.cmpAnswerIs, apply.chainCompacts, ↓reduceIte]
    ileft
    isplitr
    · ipureintro; simp [Hlt]
    isplitr [Htrc]
    · iunfold apply.cmpRespOk
      isplitr
      · ipureintro; exact Hrespn
      iexists _
      iframe Hresp0
      iexists _
      iframe «$r0»
    · iunfold apply.traceRes; iright; iexists false; iexact Htrc
  · -- `ErrCompacted`: no response, no trace
    subst Herr
    wp_auto
    ihave Hkvo := Hback $$ Hr %Hc1 Hhi Hrt
    icases Hkvo with ⟨Hkvo, Hc⟩
    ihave #Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hai with ⟨-, -, #Hev⟩
    ihave #HeC : applyErrIs (GoInterface.ok ec) $$ []
    · icases Hev with ⟨-, -, -, -, -, #HeL, -⟩
      iapply errVar_applyErrIs _ (GoInterface.ok ec) $$ HeL
      iexists ec; iframe Hec; ipureintro; rfl
    iapply HΦ
    iframe Hkvo
    isplitr [Hc]
    · iright; iexact HPre
    have hra : apply.cmpRevAfter crev rev = crev := by
      unfold apply.cmpRevAfter; split <;> omega
    rw [hra]
    iframe Hc
    simp only [apply.cmpAnswerIs, apply.chainCompacts, ↓reduceIte]
    iright
    iframe HeC
    ipureintro
    refine ⟨Hle, ?_, ?_, ?_⟩ <;> simp

end proof

end EtcdGrove
end Perennial
