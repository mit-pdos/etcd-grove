/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Txn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.IsTxnReadonly
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__StepWithFunction
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.compareToPath
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__AddField
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkTxn
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewReadOnlyTxnWrite
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.txn
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__End
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.FrozenSpecs

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite
@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]


/-- A branch of gets runs with no change. -/
theorem txn.srvOps_gets_nil (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), (∀ op ∈ ops, opIsGet op = true) →
      (srvOps s0 r s ops).1 = []
  | _, [], _ => rfl
  | s, op :: ops, h => by
    cases op with
    | get o =>
      rw [srvOps_cons, srvOp_get]
      simp only [List.nil_append, applyChanges_nil']
      exact txn.srvOps_gets_nil s0 r s ops (fun op hop => h op (by simp [hop]))
    | _ => have := h _ (List.mem_cons.2 (Or.inl rfl)); simp [opIsGet] at this

/-- A branch of gets meets the run's premises when each get does at the state. -/
theorem txn.opsOk_gets (w : Bool) (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) :
    ∀ ops : List TxnOp, (∀ op ∈ ops, opIsGet op = true) →
      (∀ o, TxnOp.get o ∈ ops → GetOk s o) → OpsOk w s0 r s ops
  | [], _, _ => by simp [OpsOk]
  | op :: ops, h, hok => by
    cases op with
    | get o =>
      simp only [OpsOk, OpOk]
      refine ⟨hok o (by simp), ?_⟩
      rw [srvOp_get, applyChanges_nil']
      exact txn.opsOk_gets w s0 r s ops (fun op hop => h op (by simp [hop]))
        (fun o' ho' => hok o' (by simp [ho']))
    | _ => have := h _ (List.mem_cons.2 (Or.inl rfl)); simp [opIsGet] at this

/-- **The read-only run's premises** at a read log: the gets within the model (`txnGetsOk`).
(Until D19c's move, 2026-10-18, also the log small, the sort's premise: `executeTxn` now takes
it apart, `TxnPre`'s `LogSmall`.) -/
theorem txn.readTxn_opsOk (t : TxnModel) (log : mvcc.Log)
    (hro : txnReadonly t = true) (hg : txnGetsOk t) (w : Bool) (r : w64) :
    OpsOk w (mvcc.stateAfter log) r (mvcc.stateAfter log)
      (t.branch (txnOk (mvcc.stateAfter log) t)) := by
  apply txn.opsOk_gets w _ r _ _ (readonly_branch t hro _)
  intro o ho
  have hmem : TxnOp.get o ∈ t.thenOps ++ t.elseOps := by
    unfold TxnModel.branch at ho
    split at ho <;> simp [ho]
  obtain ⟨h0, hcut, hv⟩ := hg o hmem
  exact ⟨h0, hv, hcut⟩

/-- `Txn` at the sole writer (`specSole`). -/
theorem txn.Txn_sole
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hRO : txn.IsTxnReadonly.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hStepF : traceutil.Trace.StepWithFunction.spec (GF := GF) (hG := hG))
    (hPath : txn.compareToPath.spec (GF := GF) (hG := hG))
    (hAdd : traceutil.Trace.AddField.spec (GF := GF) (hG := hG))
    (hCheck : txn.checkTxn.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (hWWrite : mvcc.watchableStore.Write.spec (GF := GF) (hG := hG))
    (hNewRo : mvcc.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (htxn : txn.txn.spec (GF := GF) (hG := hG))
    (hRoEnd : mvcc.txnReadWrite.End.spec (GF := GF) (hG := hG))
    (hWEnd : mvcc.watchableStoreTxnWrite.End.spec (GF := GF) (hG := hG)) :
    txn.Txn.specSole (GF := GF) (hG := hG) := by
  have hEndF := mvcc.metricsTxnWrite.End.spec_frozen hEnd
  have hRoEnd := mvcc.txnReadWrite.End.spec_frozen hRoEnd
  intro ctx cd lg rt shared kv le skip s γ log t P Pre Q Post f L ot te F
  wp_start as ⟨#Hkv, Hrd, Hsw, #HF, Hwt, #Hle, #Hrt, #Hctx, #Hct, Hto, #Hnd, #Hknown, Hu, %Hpre, #Hcok, Hcs, #Hhook⟩
  iunfold mvcc.csContract at Hcs
  icases Hcs with ⟨HPre, #Htr, Hupd⟩
  iunfold txn.kvWriter at Hsw
  icases Hsw with ⟨Hsw, Hwl, Hfrag⟩
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave %Hkvok := txn.isKV_ok kv s γ $$ Hkv
  obtain ⟨kty, kvv, rfl⟩ := Hkvok
  ihave ⟨#Hko, #Hs⟩ := txn.isKV_kvOver _ s γ $$ Hkv
  wp_auto
  wp_apply (hEnsure ctx cd ot te lg _ _) $$ [$Hctx $Hct $Hto]
    as %ctx' %trace ⟨⟨%Htr, %Hteq⟩, Htrc, #Hct', %vs, #Hctx', -⟩
  · iapply traceutil.ownFields_nil
  wp_apply (hRO rt t) $$ [$Hrt]
  generalize hw : (!txnReadonly t) = isW
  wp_join iprop(∃ md : w32, mode_ptr ↦ md ∗ txnModeWriteWithSharedBuffer_ptr ↦ shared)
    at (if: _ then _ else _) with [mode txnModeWriteWithSharedBuffer] as ⟨%md, mode, sh⟩
  · cases isW <;> (try cases shared) <;>
      (try simp only [SharedBufReadTxMode, ConcurrentReadTxMode]) <;> wp_auto <;>
      (isplitl []; · itrivial) <;> iexists _ <;> iframe
  have hlen3 : log.length + 3 ≤ 2 ^ 63 := by have := Hpre.1; omega
  wp_bind (App (App (Val #(methods kty _ kvv)) _) _)
  iapply mvcc.kvOver_read_wp kty kvv s md trace
  iframe Hko
  wp_apply (txn.soleWriter_Read_floor hRead s γ md trace log false F hlen3 Htr) $$ [$Hs $Hrd $Hsw $Htrc $HF]
    as %mw ⟨%rev, Htx, Hsw, %HFl⟩
  -- `compareToPath` in the trace's step
  icases mvcc.isTxnRead_trace_acc mw s γ trace log rev $$ Htx with ⟨⟨%te1, Htrc⟩, Hback⟩
  wp_apply (hStepF trace te1 _ _ slice.nil
      iprop(∃ sl : GoSlice, txnPath_ptr ↦ sl ∗
        sl ↦* txnPath (mvcc.stateAfter log) t ∗ ownSliceCap Bool sl (DFrac.own 1) ∗
        ((∃ te, traceutil.ownTrace trace te) -∗ mvcc.isTxnRead mw s γ trace log rev) ∗
        txnRead_ptr ↦ (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface) ∗
        rt_ptr ↦ rt))
    $$ [$Htrc Hback txnPath txnRead rt] as ⟨⟨%sl, txnPath, Hsl, Hcap, Hback, txnRead, rt⟩, %te2, Htrc⟩
  · isplitl []
    · iapply traceutil.ownFields_nil
    iintro Htrc
    ihave Htx := Hback $$ [Htrc]
    · iexists te1; iexact Htrc
    wp_auto
    wp_apply (hPath trace mw s γ log rev rt t) $$ [$Htx $Hrt] as %sl ⟨Htx, Hsl, Hcap⟩
    icases mvcc.isTxnRead_trace_acc mw s γ trace log rev $$ Htx with ⟨⟨%te3, Htrc⟩, Hback⟩
    isplitl []; · itrivial
    isplitl [txnPath Hsl Hcap Hback txnRead rt]
    · iexists sl
      iframe
    iexists te3; iexact Htrc
  ihave Htx := Hback $$ [Htrc]
  · iexists te2; iexact Htrc
  wp_join with [trace Htx]
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨Hfs, -⟩
    wp_auto
    icases mvcc.isTxnRead_trace_acc mw s γ trace log rev $$ Htx with ⟨⟨%te4, Htrc⟩, Hback⟩
    wp_apply (hAdd trace te4 _ _ _) $$ [$Htrc $Hfs] as ⟨Htrc, -⟩
    · ipureintro
      exact traceutil.fieldsWf_cons_bool _ _ _ traceutil.fieldsWf_nil
    ihave Htx := Hback $$ [Htrc]
    · iexists te4; iexact Htrc
    try wp_join_done
  ipersist Hsl
  ihave Hu : (⌜true = false⌝ ∨ EtcdGrove.lease.lessorUser γ.leases L
      (mvcc.leaseItemsOf (mvcc.stateAfter log))) $$ [Hu]
  · iright; iexact Hu
  wp_apply (hCheck trace mw s γ log rev rt t le γ.leases sl [] L _ true (fun h => by cases h))
    $$ [$Htx $Hrt $Hle $Hu] as %n %err ⟨Htx, Hu, Hres⟩
  · isplitl []
    · ipureintro; exact Htr
    rw [List.append_nil]; iexact Hsl
  icases Hu with (Hf | Hu)
  · iexfalso; iexact Hf
  icases Hres with (⟨%Hok, #Hleases⟩ | ⟨%Herr, #Hce⟩)
  rotate_left
  · -- a check failed: the read transaction ended, nothing written
    obtain ⟨Hne, rfl, Hnp⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      ihave Htx : mvcc.isTxn mw s γ trace (.read log rev) $$ [Htx]
      · simp only [mvcc.isTxn]; iexact Htx
      ihave Htx := mvcc.isTxn_toEnd _ _ _ _ $$ Htx
      ihave Hep : mvcc.txnEndPre γ (.read log rev) $$ []
      · simp only [mvcc.txnEndPre]; itrivial
      wp_apply (hEndF trace mw s γ (.read log rev)) $$ [$Htx $Hep] as ⟨Hrd, -, %te9, Htrc⟩
      iapply HΦ
      iframe Hrd
      ileft
      iframe Hce HPre Hu
      isplitr
      · ipureintro; exact ⟨rfl, rfl, Hne, Hnp⟩
      isplitl [Hsw Hwl Hfrag]
      · iunfold txn.kvWriter; iframe Hsw Hwl Hfrag
      iexists trace, te9
      iframe Htrc
      ipureintro; exact Hteq
  obtain ⟨rfl, -, Hign⟩ := Hok
  ihave %Hlok := txn.leasesOk_paths L _ _ $$ Hleases
  wp_auto
  icases mvcc.isTxnRead_trace_acc mw s γ trace log rev $$ Htx with ⟨⟨%te4, Htrc⟩, Hback⟩
  wp_apply (hStep trace te4 _ _) $$ [$Htrc] as Htrc
  · iapply traceutil.ownFields_nil
  ihave Htx := Hback $$ [Htrc]
  · iexists te4; iexact Htrc
  have hoks := opsOk_strong _ _ _ _ Hpre.2.1 Hign
  have hlen4 : log.length + 4 ≤ 2 ^ 63 := Hpre.1
  ihave #Hnd' : mvcc.neverDone { cd with Values := vs } $$ []
  · iunfold mvcc.neverDone at Hnd; iunfold mvcc.neverDone; iexact Hnd
  cases isW
  · -- a read-only request: the read transaction, wrapped
    have hro : txnReadonly t = true := by simpa using hw
    wp_auto
    wp_apply (hNewRo trace mw s γ log rev) $$ [$Htx] as %trw Hro
    ihave Htv := (txnViewIs_ro trw s γ log rev).2 $$ Hro
    ihave Htw := txnWriteIs_of_view _ s γ true log [] _ ⟨rfl, rev, rfl⟩ $$ Htv
    have htxn' := htxn trace ctx' { cd with Values := vs } true lg s γ
      (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw) true log rt t sl skip L
    simp only [Bool.not_true, ↓reduceIte] at htxn'
    wp_apply htxn'
      $$ [$Htw $Hctx' $Hct' $Hnd' $Hrt $Hsl $Hleases] as %resp %err Hres
    · isplitl []; · itrivial
      isplitl []; · ileft; itrivial
      ipureintro; exact ⟨hoks, fun _ => Hpre.2.2, fun _ => hro, fun h => absurd h (by simp)⟩
    icases Hres with (⟨%Herr, Htw, #Hresp, Hhdr, -, -⟩ | ⟨%Hc, -⟩)
    rotate_left
    · cases Hc
    subst Herr
    icases txnWriteIs_kind _ s γ true log _ $$ Htw with ⟨%kind, Hv, %Hk⟩
    obtain ⟨hkis, -, -, -, -⟩ := Hk
    unfold KindIs at hkis
    simp only [↓reduceIte] at hkis
    obtain ⟨hch, rev', rfl⟩ := hkis
    ihave Hro := (txnViewIs_ro trw s γ log rev').1 $$ Hv
    wp_apply (hRoEnd trace trw s γ log rev') $$ [$Hro] as ⟨Hrd, %te5, Htrc⟩
    ihave #Hresp2 := Hresp
    iunfold txnResponseIs at Hresp2
    icases Hresp2 with ⟨%Hrn, #Hf⟩
    iunfold txnRespFieldsIs at Hf
    icases Hf with ⟨%h, #Hh, %Hhn, #Hrev, -, #Hrs⟩
    iunfold respsIs at Hrs
    icases Hrs with ⟨%rsl, %rps, #Hrsl, #Hrps, -⟩
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨Hfs, -⟩
    wp_auto
    wp_apply (hAdd trace te5 _ _ _) $$ [$Htrc $Hfs] as ⟨Htrc, -⟩
    · ipureintro
      exact traceutil.fieldsWf_cons_int _ _ _ (.int _) _
        (traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil)
    iapply HΦ
    iframe Hrd
    iright
    simp only [srvRunTxn]
    rw [hch]
    rw [stateAfter_commitLog]
    simp only [mvcc.applyChanges, List.foldl_nil]
    iframe Hu
    isplitl []
    · ipureintro; simp [Htr, HFl]; exact ⟨Hign, Hlok⟩
    isplitl [Htrc]
    · iexists te5; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    simp only [mvcc.commitLog, ↓reduceIte]
    iframe Hresp Hhdr
    isplitl [Hsw Hwl Hfrag]
    · iunfold txn.kvWriter; iframe Hsw Hwl Hfrag
    isplitl []
    · iexact Hknown
    simp only [hro, ↓reduceIte]
    iexact HPre
  · -- a write: the read ends, the write transaction opens at the sole writer's log
    have hro : txnReadonly t = false := by simpa using hw
    wp_auto
    ihave Htx : mvcc.isTxn mw s γ trace (.read log rev) $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    ihave Htx := mvcc.isTxn_toEnd _ _ _ _ $$ Htx
    ihave Hep : mvcc.txnEndPre γ (.read log rev) $$ []
    · simp only [mvcc.txnEndPre]; itrivial
    wp_apply (hEndF trace mw s γ (.read log rev)) $$ [$Htx $Hep] as ⟨Hrd, -, %te6, Htrc⟩
    icases soleWriter_split γ log hlen4 $$ Hsw with ⟨Htok, Hsw⟩
    iunfold soleWriterOpen at Hsw
    icases Hsw with ⟨#Hc, Htoks, %Hl2⟩
    have hsb : soleBudget log - 1 + 1 = soleBudget log := by unfold soleBudget; omega
    -- the writer's hook: the hook's facts and the writer's fragment (D22 receiver epochs, S5b)
    ihave HhookW : mvcc.hookIs γ P f $$ [Hfrag]
    · iapply (mvcc.hookIs_split γ P f).2; iframe Hhook Hfrag
    wp_apply (txn.kv_Write hWrite hWWrite kty kvv s γ trace P Pre Q f te6 (soleBudget log - 1) log)
      $$ [$Hkv $Hrd $Htok $Hwt $Htoks $Hwl $HhookW $HPre $Htr $Htrc]
      as %tyX %vX ⟨%ilog, %mw', Htx, Hte, Htoks, -, HQ, HhookW⟩
    · ipureintro; exact ⟨fun _ => ⟨hsb, hlen4⟩, Htr⟩
    ihave ⟨Hte, #Hw⟩ := txn.twEnd_wrap s γ tyX vX mw' ilog $$ Hte
    -- the caller's update (the writes are the model's): the lock's invariant back for `End`
    imod Hupd $$ HQ with ⟨HP, HPost⟩
    ihave ⟨%Hpin, Htoks, -, Htx⟩ := isTxnWrite_pinned γ log ilog [] mw' s (W64 0) (W64 0) (W64 0)
      (soleBudget log - 1) $$ [$Htoks $Hc $Htx]
    have hil := pinned_sole log ilog hlen4 Hpin
    subst ilog
    ihave Htx : mvcc.isTxn mw' s γ trace (.write log [] (W64 0) (W64 0) (W64 0)) $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    icases txnViewIs_wrap tyX vX mw' s γ (.write log [] (W64 0) (W64 0) (W64 0)) $$ Hw
      with ⟨-, Hvb⟩
    ihave Htv := Hvb $$ Htx
    ihave Htw := txnWriteIs_of_view _ s γ false log [] _ ⟨_, _, _, rfl⟩ $$ Htv
    have htxn' := htxn trace ctx' { cd with Values := vs } true lg s γ
      (interface.mkOk tyX vX) false log rt t sl skip L
    simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true] at htxn'
    iunfold EtcdGrove.lease.lessorUser at Hu
    icases Hu with ⟨Hown, Hrdo, Hrvk⟩
    wp_apply htxn'
      $$ [$Htw $Hctx' $Hct' $Hnd' $Hrt $Hsl $Hleases $Hknown Hown] as %resp %err Hres
    · isplitl [Hown]
      · iright; iexact Hown
      ipureintro; exact ⟨hoks, fun h => h.elim, fun h => h.elim, fun h => absurd h (by simp)⟩
    icases Hres with (⟨%Herr, Htw, #Hresp, Hhdr, #Hk2, Hown⟩ | ⟨%Hc, -⟩)
    rotate_left
    · cases Hc
    subst Herr
    icases txnWriteIs_kind _ s γ false log _ $$ Htw with ⟨%kind, Hv, %Hk⟩
    obtain ⟨hkis, -, -, -, -⟩ := Hk
    obtain ⟨p1, p2, p3, rfl⟩ := hkis
    icases txnViewIs_wrap tyX vX mw' s γ (.write log _ p1 p2 p3) $$ Hw with ⟨Hva, -⟩
    ihave Htx := Hva $$ Hv
    simp only [mvcc.isTxn]
    wp_apply (txn.tw_End hEnd hWEnd tyX vX s γ trace mw' log _ p1 p2 p3 (soleBudget log - 1) P f)
      $$ [$Htx $Hte $Htoks HP HhookW] as ⟨Hrd, ⟨%te5, Htrc⟩, #Hc', Htok, Htoks, Hwl, HhookW⟩
    · iframe HP HhookW
      isplitl []
      · ipureintro; exact fun _ => hsb
      simp only [hro, Bool.false_eq_true, ↓reduceIte]; isimp only [hro, Bool.false_eq_true, ↓reduceIte, srvRunTxn] at Hcok; iapply Hcok; ipureintro; exact Hign
    icases (mvcc.hookIs_split γ P f).1 $$ HhookW with ⟨-, Hfrag⟩
    ihave Hsw := soleWriter_close γ log _ hlen4 $$ [Htoks Hc' Htok]
    · iframe Hc' Htok; iunfold soleWriterOpen; iframe Hc Htoks; ipureintro; exact Hl2
    ihave Hsw : txn.kvWriter s γ (mvcc.commitLog log _) $$ [Hsw Hwl Hfrag]
    · iunfold txn.kvWriter; iframe Hsw Hwl Hfrag
    ihave #Hresp2 := Hresp
    iunfold txnResponseIs at Hresp2
    icases Hresp2 with ⟨%Hrn, #Hf⟩
    iunfold txnRespFieldsIs at Hf
    icases Hf with ⟨%h, #Hh, %Hhn, #Hrev, -, #Hrs⟩
    iunfold respsIs at Hrs
    icases Hrs with ⟨%rsl, %rps, #Hrsl, #Hrps, -⟩
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨Hfs, -⟩
    wp_auto
    wp_apply (hAdd trace te5 _ _ _) $$ [$Htrc $Hfs] as ⟨Htrc, -⟩
    · ipureintro
      exact traceutil.fieldsWf_cons_int _ _ _ (.int _) _
        (traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil)
    icases Hown with (Hf | Hown)
    · iexfalso; iexact Hf
    iapply HΦ
    iframe Hrd
    iright
    isplitl []
    · ipureintro; exact ⟨rfl, Htr, HFl, fun h => (by rw [hro] at h; cases h), Hign, Hlok⟩
    isplitl [Htrc]
    · iexists te5; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    rw [stateAfter_commitLog]
    simp only [srvRunTxn]
    iframe Hresp Hsw Hk2 Hhdr
    isplitl [Hown Hrdo Hrvk]
    · iunfold EtcdGrove.lease.lessorUser; iframe Hown Hrdo Hrvk
    simp only [hro, Bool.false_eq_true, ↓reduceIte]
    iexact HPost

/-- `Txn` at a reader (`specRead`). -/
theorem txn.Txn_read
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hRO : txn.IsTxnReadonly.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hStepF : traceutil.Trace.StepWithFunction.spec (GF := GF) (hG := hG))
    (hPath : txn.compareToPath.spec (GF := GF) (hG := hG))
    (hAdd : traceutil.Trace.AddField.spec (GF := GF) (hG := hG))
    (hCheck : txn.checkTxn.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (_hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (hNewRo : mvcc.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (htxn : txn.txn.spec (GF := GF) (hG := hG))
    (hRoEnd : mvcc.txnReadWrite.End.spec (GF := GF) (hG := hG)) :
    txn.Txn.specRead (GF := GF) (hG := hG) := by
  have hEnd := mvcc.metricsTxnWrite.End.spec_frozen hEnd
  have hRoEnd := mvcc.txnReadWrite.End.spec_frozen hRoEnd
  intro ctx cd lg rt shared kv le skip s γ m log₀ t ot te
  wp_start as ⟨#Hkv, Hrd, Htoks, #Hc0, #Hle, #Hrt, #Hctx, #Hct, Hto, %Hpre, #Hsmall⟩
  obtain ⟨Hlg, hro, hgets⟩ := Hpre
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave %Hkvok := txn.isKV_ok kv s γ $$ Hkv
  obtain ⟨kty, kvv, rfl⟩ := Hkvok
  wp_auto
  wp_apply (hEnsure ctx cd ot te lg _ _) $$ [$Hctx $Hct $Hto]
    as %ctx' %trace ⟨⟨%Htr, %Hteq⟩, Htrc, #Hct', %vs, #Hctx', -⟩
  · iapply traceutil.ownFields_nil
  wp_apply (hRO rt t) $$ [$Hrt]
  rw [hro]
  wp_join iprop(∃ md : w32, mode_ptr ↦ md ∗ txnModeWriteWithSharedBuffer_ptr ↦ shared)
    at (if: _ then _ else _) with [mode txnModeWriteWithSharedBuffer] as ⟨%md, mode, sh⟩
  · (try cases shared) <;>
      (try simp only [SharedBufReadTxMode, ConcurrentReadTxMode]) <;> wp_auto <;>
      (isplitl []; · itrivial) <;> iexists _ <;> iframe
  wp_apply (txn.kv_Read hRead kty kvv s γ md trace m log₀ false) $$ [$Hkv $Hrd $Htoks $Hc0 $Htrc] as %mw ⟨%log, %rev, Htx, Htoks, #Hcok, %Hpin⟩
  · ipureintro; exact Htr
  icases isTxnRead_pure mw s γ log rev $$ Htx with ⟨Htx, %Hlog⟩
  icases isTxnRead_cert mw s γ log rev $$ Htx with ⟨Htx, #Hcert⟩
  have hpin' : log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 := ⟨Hpin.1, Hpin.2⟩
  ihave %Hsm := Hsmall $$ %log %hpin' Hcert
  -- `compareToPath` in the trace's step
  icases mvcc.isTxnRead_trace_acc mw s γ trace log rev $$ Htx with ⟨⟨%te1, Htrc⟩, Hback⟩
  wp_apply (hStepF trace te1 _ _ slice.nil
      iprop(∃ sl : GoSlice, txnPath_ptr ↦ sl ∗
        sl ↦* txnPath (mvcc.stateAfter log) t ∗ ownSliceCap Bool sl (DFrac.own 1) ∗
        ((∃ te, traceutil.ownTrace trace te) -∗ mvcc.isTxnRead mw s γ trace log rev) ∗
        txnRead_ptr ↦ (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface) ∗
        rt_ptr ↦ rt))
    $$ [$Htrc Hback txnPath txnRead rt] as ⟨⟨%sl, txnPath, Hsl, Hcap, Hback, txnRead, rt⟩, %te2, Htrc⟩
  · isplitl []
    · iapply traceutil.ownFields_nil
    iintro Htrc
    ihave Htx := Hback $$ [Htrc]
    · iexists te1; iexact Htrc
    wp_auto
    wp_apply (hPath trace mw s γ log rev rt t) $$ [$Htx $Hrt] as %sl ⟨Htx, Hsl, Hcap⟩
    icases mvcc.isTxnRead_trace_acc mw s γ trace log rev $$ Htx with ⟨⟨%te3, Htrc⟩, Hback⟩
    isplitl []; · itrivial
    isplitl [txnPath Hsl Hcap Hback txnRead rt]
    · iexists sl
      iframe
    iexists te3; iexact Htrc
  ihave Htx := Hback $$ [Htrc]
  · iexists te2; iexact Htrc
  ipersist Hsl
  wp_apply (hCheck trace mw s γ log rev rt t le γ.leases sl [] [] ∅ false (fun _ => hro))
    $$ [$Htx $Hrt $Hle] as %n %err ⟨Htx, -, Hres⟩
  · isplitl []
    · ipureintro; exact Htr
    isplitl []
    · ileft; ipureintro; rfl
    rw [List.append_nil]; iexact Hsl
  icases Hres with (⟨%Hok, #Hleases⟩ | ⟨%Herr, #Hce⟩)
  rotate_left
  · -- a check failed: the read transaction ended
    obtain ⟨Hne, rfl, Hnp⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      ihave Htx : mvcc.isTxn mw s γ trace (.read log rev) $$ [Htx]
      · simp only [mvcc.isTxn]; iexact Htx
      ihave Htx := mvcc.isTxn_toEnd _ _ _ _ $$ Htx
      ihave Hep : mvcc.txnEndPre γ (.read log rev) $$ []
      · simp only [mvcc.txnEndPre]; itrivial
      wp_apply (hEnd trace mw s γ (.read log rev)) $$ [$Htx $Hep] as ⟨Hrd, -, %te9, Htrc⟩
      iapply HΦ
      iframe Hrd Htoks
      iexists log
      iframe Hcert Hcok
      isplitl []
      · ipureintro; exact ⟨Hpin.1, Hpin.2, Hlog.2.1⟩
      ileft
      iframe Hce
      isplitr
      · ipureintro; exact ⟨rfl, rfl, Hne⟩
      iexists trace, te9
      iframe Htrc
      ipureintro; exact Hteq
  obtain ⟨rfl, -, -⟩ := Hok
  wp_auto
  icases mvcc.isTxnRead_trace_acc mw s γ trace log rev $$ Htx with ⟨⟨%te4, Htrc⟩, Hback⟩
  wp_apply (hStep trace te4 _ _) $$ [$Htrc] as Htrc
  · iapply traceutil.ownFields_nil
  ihave Htx := Hback $$ [Htrc]
  · iexists te4; iexact Htrc
  have hoks := txn.readTxn_opsOk t log hro hgets false (W64 (log.length : Int))
  have hnil := txn.srvOps_gets_nil (mvcc.stateAfter log) (W64 (log.length : Int)) (mvcc.stateAfter log)
    _ (readonly_branch t hro (txnOk (mvcc.stateAfter log) t))
  wp_apply (hNewRo trace mw s γ log rev) $$ [$Htx] as %trw Hro
  ihave Htv := (txnViewIs_ro trw s γ log rev).2 $$ Hro
  ihave Htw := txnWriteIs_of_view _ s γ true log [] _ ⟨rfl, rev, rfl⟩ $$ Htv
  have htxn' := htxn trace ctx' { cd with Values := vs } false lg s γ
    (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw) true log rt t sl skip []
  simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true] at htxn'
  wp_apply htxn'
    $$ [$Htw $Hctx' $Hct' $Hrt $Hsl $Hleases] as %resp %err Hres
  · isplitl []; · itrivial
    isplitl []; · ileft; itrivial
    ipureintro
    exact ⟨hoks, fun _ => Hsm, fun _ => hro, fun _ => ⟨trivial, Hlg⟩⟩
  -- the read transaction ends; the response's fields for the trace
  ihave ⟨%pend', Htw, #Hshell, Hout⟩ : (∃ pend' : List mvcc.Change,
      txnWriteIs (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw) s γ trace true log pend' ∗
      txnRespShell resp ∗
      ((⌜err = GoInterface.nil⌝ ∗
        txnResponseIs skip resp (W64 ((log.length : Int) - 1)) t
          (srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).1
          (srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.2 ∗
        respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp)) ∨
       (mvcc.errorfIs err ∗ roTxnRespRd resp ∗
        respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp)))) $$ [Hres]
  · icases Hres with (⟨%Herr, Htw, #Hresp, Hhdr, -⟩ | ⟨-, #He, ⟨%pend', Htw⟩, #Hshell, #Hrd, Hhdr⟩)
    · iexists _
      iframe Htw
      have hwr : (W64 (mvcc.writeRev log
          (srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 : Int) : w64) =
          W64 ((log.length : Int) - 1) := by
        simp only [srvRunTxn, hnil, mvcc.writeRev, ↓reduceIte]
        have := List.length_pos_iff.2 Hlog.2.1
        congr 1; omega
      ihave #Hresp2 := Hresp
      iunfold txnResponseIs at Hresp2
      icases Hresp2 with ⟨%Hrn, #Hf⟩
      iunfold txnRespFieldsIs at Hf
      icases Hf with ⟨%h, #Hh, %Hhn, #Hrev, -, #Hrs⟩
      iunfold respsIs at Hrs
      icases Hrs with ⟨%rsl, %rps, #Hrsl, -, -⟩
      isplitr
      · iunfold txnRespShell
        isplitr
        · ipureintro; exact Hrn
        iexists h, rsl, _
        iframe Hh Hrev Hrsl
      ileft
      isplitr
      · ipureintro; exact Herr
      iframe Hhdr
      rw [← hwr]
      simp only [srvRunTxn]
      iexact Hresp
    · iexists pend'
      iframe Htw Hshell
      iright; iframe He Hrd Hhdr
  icases txnWriteIs_kind _ s γ true log _ $$ Htw with ⟨%kind, Hv, %Hk⟩
  obtain ⟨hkis, -, -, -, -⟩ := Hk
  unfold KindIs at hkis
  simp only [↓reduceIte] at hkis
  obtain ⟨-, rev', rfl⟩ := hkis
  ihave Hro := (txnViewIs_ro trw s γ log rev').1 $$ Hv
  wp_apply (hRoEnd trace trw s γ log rev') $$ [$Hro] as ⟨Hrd, %te5, Htrc⟩
  ihave #Hshell2 := Hshell
  iunfold txnRespShell at Hshell2
  icases Hshell2 with ⟨%Hrn, %h, %rsl, %rv0, #Hh, #Hrev, #Hrsl⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fs ⟨Hfs, -⟩
  wp_auto
  wp_apply (hAdd trace te5 _ _ _) $$ [$Htrc $Hfs] as ⟨Htrc, -⟩
  · ipureintro
    exact traceutil.fieldsWf_cons_int _ _ _ (.int _) _
      (traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil)
  iapply HΦ
  iframe Hrd Htoks
  iexists log
  iframe Hcert Hcok
  isplitl []
  · ipureintro; exact ⟨Hpin.1, Hpin.2, Hlog.2.1⟩
  iright
  icases Hout with (⟨%Herr, #Hresp, Hhdr⟩ | ⟨#He, #Hrd, Hhdr⟩)
  · ileft
    isplitr
    · ipureintro; exact ⟨Herr, Htr⟩
    isplitl [Htrc]
    · iexists te5; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iframe Hresp Hhdr
  · iright
    isplitr
    · ipureintro; exact Htr
    isplitl [Htrc]
    · iexists te5; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iframe He Hrd Hhdr

theorem txn.Txn.wp_proof
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hRO : txn.IsTxnReadonly.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hStepF : traceutil.Trace.StepWithFunction.spec (GF := GF) (hG := hG))
    (hPath : txn.compareToPath.spec (GF := GF) (hG := hG))
    (hAdd : traceutil.Trace.AddField.spec (GF := GF) (hG := hG))
    (hCheck : txn.checkTxn.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (hWWrite : mvcc.watchableStore.Write.spec (GF := GF) (hG := hG))
    (hNewRo : mvcc.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (htxn : txn.txn.spec (GF := GF) (hG := hG))
    (hRoEnd : mvcc.txnReadWrite.End.spec (GF := GF) (hG := hG))
    (hWEnd : mvcc.watchableStoreTxnWrite.End.spec (GF := GF) (hG := hG)) :
    txn.Txn.spec (GF := GF) (hG := hG) :=
  ⟨txn.Txn_sole hEnsure hRO hRead hStepF hPath hAdd hCheck hEnd hStep hWrite hWWrite hNewRo htxn
      hRoEnd hWEnd,
    txn.Txn_read hEnsure hRO hRead hStepF hPath hAdd hCheck hEnd hStep hWrite hNewRo htxn hRoEnd⟩

end proof

end EtcdGrove
end Perennial
