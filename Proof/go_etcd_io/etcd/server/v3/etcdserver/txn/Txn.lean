/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Txn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.SoleWriter
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.IsTxnReadonly
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__StepWithFunction
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.compareToPath
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__AddField
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkTxn
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.txn

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccName)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]


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
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hRO : txn.IsTxnReadonly.spec (GF := GF) (hG := hG))
    (hStepF : traceutil.Trace.StepWithFunction.spec (GF := GF) (hG := hG))
    (hPath : txn.compareToPath.spec (GF := GF) (hG := hG))
    (hAdd : traceutil.Trace.AddField.spec (GF := GF) (hG := hG))
    (hCheck : txn.checkTxn.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hNewRo : mvcc.api.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (htxn : txn.txn.spec (GF := GF) (hG := hG)) :
    txn.Txn.specSole (GF := GF) (hG := hG) := by
  intro ctx cd lg rt shared kv le skip γ log t q B P Pre Q Post f L ot te Qr Qw
  haveI := hpers.1 kv γ
  wp_start as ⟨#Hkv, Htt, Hbk, #Hle, #Hrt, #Hctx, #Hct, Hto, #Hnd, #Hknown, Hu, %Hpre, Hcs, Hau, Hwand⟩
  iunfold txn.kvBackend at Hbk
  icases Hbk with ⟨Hbk, #Hhook⟩
  iunfold txn.csA at Hcs
  icases Hcs with ⟨HPre, Htrun, Hupd⟩
  icases txn.isMvcc_shape hsh kv γ $$ Hkv with ⟨%Hsh, -⟩
  obtain ⟨kty, kvv, rfl, hReadC, hWriteC, -⟩ := Hsh
  ihave Hau := txn.readAU_reach hpers hreach _ γ _ $$ Hkv Hau
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  wp_auto
  wp_apply (hEnsure ctx cd ot te lg _ _) $$ [$Hctx $Hct $Hto]
    as %ctx' %trace ⟨⟨%Htr, %Hteq⟩, Htrc, #Hct', -, %vs, #Hctx', -⟩
  · iapply traceutil.ownFields_nil
  wp_apply (hRO rt t) $$ [$Hrt]
  generalize hw : (!txnReadonly t) = isW
  wp_join iprop(∃ md : w32, mode_ptr ↦ md ∗ txnModeWriteWithSharedBuffer_ptr ↦ shared)
    at (if: _ then _ else _) with [mode txnModeWriteWithSharedBuffer] as ⟨%md, mode, sh⟩
  · cases isW <;> (try cases shared) <;>
      (try simp only [SharedBufReadTxMode, ConcurrentReadTxMode]) <;> wp_auto <;>
      (isplitl []; · itrivial) <;> iexists _ <;> iframe
  wp_apply (hReadC γ md trace false _) $$ [$Hkv $Htt $Htrc $Hau]
    as %tr ⟨Htrc, %σr, Htx, ⟨⟨%Hlog, HQr⟩, %Hreachr⟩⟩
  · ipureintro; exact Htr
  subst Hlog
  icases txn.mvccTxn_shape hsh tr γ trace (.read σr) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tty, tv, rfl, -, -, -, -, -, -, hEndT⟩ := Hsht
  (try wp_auto)
  -- `compareToPath` in the trace's step
  wp_apply (hStepF trace false _ _ slice.nil
      iprop(∃ sl : GoSlice, txnPath_ptr ↦ sl ∗
        sl ↦* txnPath (mvcc.stateAfter σr.log) t ∗ ownSliceCap Bool sl (DFrac.own 1) ∗
        mvcc.api.mvccTxn (interface.mkOk tty tv) γ trace (.read σr) ∗
        txnRead_ptr ↦ (interface.mkOk tty tv : GoInterface) ∗
        rt_ptr ↦ rt))
    $$ [$Htrc Htx txnPath txnRead rt] as ⟨⟨%sl, txnPath, Hsl, Hcap, Htx, txnRead, rt⟩, Htrc⟩
  · isplitl []
    · iapply traceutil.ownFields_nil
    iintro Htrc
    wp_auto
    wp_apply (hPath _ γ trace false σr rt t) $$ [$Htx $Htrc $Hrt] as %sl ⟨Htx, Htrc, Hsl, Hcap⟩
    · ipureintro; exact Hreachr
    isplitl []; · itrivial
    isplitl [txnPath Hsl Hcap Htx txnRead rt]
    · iexists sl
      iframe
    iexact Htrc
  wp_join with [trace Htrc]
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨Hfs, -⟩
    wp_auto
    wp_apply (hAdd trace false _ _ _) $$ [$Htrc $Hfs] as ⟨Htrc, -⟩
    · ipureintro
      exact traceutil.fieldsWf_cons_bool _ _ _ traceutil.fieldsWf_nil
    try wp_join_done
  ipersist Hsl
  ihave Hu : (⌜true = false⌝ ∨ EtcdGrove.lease.lessorUser (mvcc.api.mvccLeases γ) L
      (mvcc.leaseItemsOf (mvcc.stateAfter σr.log))) $$ [Hu]
  · iright; iexact Hu
  wp_apply (hCheck _ γ trace false σr rt t le (mvcc.api.mvccLeases γ) sl [] L _ true (fun h => by cases h))
    $$ [$Htx $Htrc $Hrt $Hle $Hu] as %n %err ⟨Htx, Htrc, Hu, Hres⟩
  · isplitl []
    · ipureintro; exact Htr
    isplitl []
    · ipureintro; exact Hreachr
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
      wp_apply (txn.end_read hEndT γ trace σr) $$ [$Htx] as Htt
      iapply HΦ
      ihave Hbk : txn.kvBackend γ q B P f $$ [Hbk]
      · iunfold txn.kvBackend; iframe Hbk Hhook
      iframe Htt Hbk
      iexists σr
      isplitl []
      · ipureintro; exact ⟨rfl, Hreachr⟩
      ileft
      iframe Hce HPre Hu HQr
      isplitr
      · ipureintro; exact ⟨rfl, rfl, Hne, Hnp⟩
      iexists trace, false
      iframe Htrc
      ipureintro; exact Hteq
  obtain ⟨rfl, -, Hign⟩ := Hok
  ihave %Hlok := txn.leasesOk_paths L _ _ $$ Hleases
  wp_auto
  wp_apply (hStep trace false _ _) $$ [$Htrc] as Htrc
  · iapply traceutil.ownFields_nil
  have hoks := opsOk_strong _ _ _ _ Hpre Hign
  ihave #Hnd' : mvcc.neverDone { cd with Values := vs } $$ []
  · iunfold mvcc.neverDone at Hnd; iunfold mvcc.neverDone; iexact Hnd
  cases isW
  · -- a read-only request: the read transaction, wrapped
    have hro : txnReadonly t = true := by simpa using hw
    wp_auto
    wp_apply (hNewRo _ γ trace σr) $$ [$Htx] as %trw Hro
    icases txn.mvccTxn_shape hsh trw γ trace (.read σr) $$ Hro with ⟨%Hshw, Hro⟩
    obtain ⟨wty, wv, rfl, -, -, -, -, -, -, hEndW⟩ := Hshw
    have htxn' := htxn ctx' { cd with Values := vs } true lg γ trace false (interface.mkOk wty wv) true σr
      rt t sl skip L
    simp only [Bool.not_true, ↓reduceIte, txn.MTxn.append] at htxn'
    wp_apply htxn'
      $$ [$Hro $Htrc $Hctx' $Hct' $Hnd' $Hrt $Hsl $Hleases] as %resp %err ⟨Htrc, Hres⟩
    · isplitl []; · itrivial
      isplitl []; · ileft; itrivial
      ipureintro
      exact ⟨Hreachr, (by simp), hoks, fun _ => hro, fun h => absurd h (by simp)⟩
    icases Hres with (⟨⟨%Herr, %Hch⟩, Hro, #Hresp, Hhdr, -, -⟩ | ⟨%Hc, -⟩)
    rotate_left
    · cases Hc
    subst Herr
    (try wp_auto)
    wp_apply (txn.end_read hEndW γ trace σr) $$ [$Hro] as Htt
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
    wp_apply (hAdd trace false _ _ _) $$ [$Htrc $Hfs] as ⟨Htrc, -⟩
    · ipureintro
      exact traceutil.fieldsWf_cons_int _ _ _ (.int _) _
        (traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil)
    have hch : txn.txnChs σr.log t = [] := Hch trivial
    iapply HΦ
    ihave Hbk : txn.kvBackend γ q B P f $$ [Hbk]
    · iunfold txn.kvBackend; iframe Hbk Hhook
    iframe Htt Hbk
    iexists σr
    isplitl []
    · ipureintro; exact ⟨rfl, Hreachr⟩
    iright
    rw [hch]
    simp only [mvcc.commitLog, ↓reduceIte]
    simp only [srvRunTxn]
    iframe Hu Hresp Hhdr Hknown
    isplitl []
    · ipureintro; refine ⟨?_, Htr, ?_, Hign, Hlok⟩ <;> simp
    isplitl [Htrc]
    · iexists false; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    simp only [hro, ↓reduceIte]
    iframe HPre HQr
  · -- a write: the read ends, the write transaction opens at the sole writer's log
    have hro : txnReadonly t = false := by simpa using hw
    wp_auto
    wp_apply (txn.end_read hEndT γ trace σr) $$ [$Htx] as Htt
    rw [hro]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ihave Hbeg := Hwand $$ %σr HQr
    iunfold txn.txnBeginAU at Hbeg
    ihave Hbeg := txn.beginAU_reach hpers hreach _ γ _ $$ Hkv Hbeg
    wp_apply (hWriteC γ trace false q B P Pre Q f _) $$ [$Hkv $Htt $Htrc $Hbk $Hhook $HPre $Htrun $Hbeg]
      as %tw ⟨Htrc, Hbk, ⟨%σw, Htw, ⟨%Hreachw, %Hlogw, Hcommit⟩⟩, HQ⟩
    · ipureintro; exact Htr
    icases txn.mvccTxn_shape hsh tw γ trace (.write σw []) $$ Htw with ⟨%Hshw, Htw⟩
    obtain ⟨wty, wv, rfl, -, -, -, -, -, -, hEndW⟩ := Hshw
    -- the caller's update (the writes are the model's): the lock's invariant back for `End`
    imod Hupd $$ HQ with ⟨HP, HPost⟩
    have htxn' := htxn ctx' { cd with Values := vs } true lg γ trace false (interface.mkOk wty wv) false σw
      rt t sl skip L
    simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true, txn.MTxn.append, List.nil_append] at htxn'
    rw [Hlogw] at htxn'
    iunfold EtcdGrove.lease.lessorUser at Hu
    icases Hu with ⟨Hown, Hrdo, Hrvk⟩
    (try wp_auto)
    wp_apply htxn'
      $$ [$Htw $Htrc $Hctx' $Hct' $Hnd' $Hrt $Hsl $Hleases $Hknown Hown] as %resp %err ⟨Htrc, Hres⟩
    · isplitl [Hown]
      · iright; iexact Hown
      ipureintro
      exact ⟨Hreachw.1, fun _ => Hreachw.2, hoks, fun h => h.elim, fun h => absurd h (by simp)⟩
    icases Hres with (⟨⟨%Herr, -⟩, Htw, #Hresp, Hhdr, #Hk2, Hown⟩ | ⟨%Hc, -⟩)
    rotate_left
    · cases Hc
    subst Herr
    (try wp_auto)
    wp_apply (txn.end_write hEndW γ trace σw _ q B P (Qw σw)) $$ [$Htw $Hbk $HP Hcommit]
      as ⟨Htt, Hbk, HQw⟩
    · iexact Hcommit
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
    wp_apply (hAdd trace false _ _ _) $$ [$Htrc $Hfs] as ⟨Htrc, -⟩
    · ipureintro
      exact traceutil.fieldsWf_cons_int _ _ _ (.int _) _
        (traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil)
    icases Hown with (Hf | Hown)
    · iexfalso; iexact Hf
    iapply HΦ
    ihave Hbk : txn.kvBackend γ q B P f $$ [Hbk]
    · iunfold txn.kvBackend; iframe Hbk Hhook
    iframe Htt Hbk
    iexists σr
    isplitl []
    · ipureintro; exact ⟨rfl, Hreachr⟩
    iright
    isplitl []
    · ipureintro; refine ⟨?_, Htr, ?_, Hign, Hlok⟩ <;> simp
    isplitl [Htrc]
    · iexists false; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    rw [stateAfter_commitLog]
    simp only [srvRunTxn]
    iframe Hresp Hk2 Hhdr
    isplitl [Hown Hrdo Hrvk]
    · iunfold EtcdGrove.lease.lessorUser; iframe Hown Hrdo Hrvk
    try simp only [hro, Bool.false_eq_true, ↓reduceIte]
    iframe HPost
    iexists σw
    iframe HQw
    ipureintro; exact Hlogw

/-- `Txn` at a reader (`specRead`). -/
theorem txn.Txn_read
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hRO : txn.IsTxnReadonly.spec (GF := GF) (hG := hG))
    (hStepF : traceutil.Trace.StepWithFunction.spec (GF := GF) (hG := hG))
    (hPath : txn.compareToPath.spec (GF := GF) (hG := hG))
    (hAdd : traceutil.Trace.AddField.spec (GF := GF) (hG := hG))
    (hCheck : txn.checkTxn.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hNewRo : mvcc.api.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (htxn : txn.txn.spec (GF := GF) (hG := hG)) :
    txn.Txn.specRead (GF := GF) (hG := hG) := by
  intro ctx cd lg rt shared kv le skip γ t ot te Q
  haveI := hpers.1 kv γ
  wp_start as ⟨#Hkv, Htt, #Hle, #Hrt, #Hctx, #Hct, Hto, %Hpre, Hau⟩
  obtain ⟨Hlg, hro, hgets⟩ := Hpre
  icases txn.isMvcc_shape hsh kv γ $$ Hkv with ⟨%Hsh, -⟩
  obtain ⟨kty, kvv, rfl, hReadC, -⟩ := Hsh
  ihave Hau := txn.readAU_reach hpers hreach _ γ Q $$ Hkv Hau
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  wp_auto
  wp_apply (hEnsure ctx cd ot te lg _ _) $$ [$Hctx $Hct $Hto]
    as %ctx' %trace ⟨⟨%Htr, %Hteq⟩, Htrc, #Hct', -, %vs, #Hctx', -⟩
  · iapply traceutil.ownFields_nil
  wp_apply (hRO rt t) $$ [$Hrt]
  rw [hro]
  wp_join iprop(∃ md : w32, mode_ptr ↦ md ∗ txnModeWriteWithSharedBuffer_ptr ↦ shared)
    at (if: _ then _ else _) with [mode txnModeWriteWithSharedBuffer] as ⟨%md, mode, sh⟩
  · (try cases shared) <;>
      (try simp only [SharedBufReadTxMode, ConcurrentReadTxMode]) <;> wp_auto <;>
      (isplitl []; · itrivial) <;> iexists _ <;> iframe
  wp_apply (hReadC γ md trace false _) $$ [$Hkv $Htt $Htrc $Hau]
    as %tr ⟨Htrc, %σr, Htx, HQ, %Hreachr⟩
  · ipureintro; exact Htr
  icases txn.mvccTxn_shape hsh tr γ trace (.read σr) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tty, tv, rfl, -, -, -, -, -, -, hEndT⟩ := Hsht
  (try wp_auto)
  -- `compareToPath` in the trace's step
  wp_apply (hStepF trace false _ _ slice.nil
      iprop(∃ sl : GoSlice, txnPath_ptr ↦ sl ∗
        sl ↦* txnPath (mvcc.stateAfter σr.log) t ∗ ownSliceCap Bool sl (DFrac.own 1) ∗
        mvcc.api.mvccTxn (interface.mkOk tty tv) γ trace (.read σr) ∗
        txnRead_ptr ↦ (interface.mkOk tty tv : GoInterface) ∗
        rt_ptr ↦ rt))
    $$ [$Htrc Htx txnPath txnRead rt] as ⟨⟨%sl, txnPath, Hsl, Hcap, Htx, txnRead, rt⟩, Htrc⟩
  · isplitl []
    · iapply traceutil.ownFields_nil
    iintro Htrc
    wp_auto
    wp_apply (hPath _ γ trace false σr rt t) $$ [$Htx $Htrc $Hrt] as %sl ⟨Htx, Htrc, Hsl, Hcap⟩
    · ipureintro; exact Hreachr
    isplitl []; · itrivial
    isplitl [txnPath Hsl Hcap Htx txnRead rt]
    · iexists sl
      iframe
    iexact Htrc
  ipersist Hsl
  wp_apply (hCheck _ γ trace false σr rt t le (mvcc.api.mvccLeases γ) sl [] [] ∅ false (fun _ => hro))
    $$ [$Htx $Htrc $Hrt $Hle] as %n %err ⟨Htx, Htrc, -, Hres⟩
  · isplitl []
    · ipureintro; exact Htr
    isplitl []
    · ipureintro; exact Hreachr
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
      wp_apply (txn.end_read hEndT γ trace σr) $$ [$Htx] as Htt
      iapply HΦ
      iframe Htt
      iexists σr
      iframe HQ
      isplitl []
      · ipureintro; exact Hreachr
      ileft
      iframe Hce
      isplitr
      · ipureintro; exact ⟨rfl, rfl, Hne⟩
      iexists trace, false
      iframe Htrc
      ipureintro; exact Hteq
  obtain ⟨rfl, -, -⟩ := Hok
  wp_auto
  wp_apply (hStep trace false _ _) $$ [$Htrc] as Htrc
  · iapply traceutil.ownFields_nil
  have hoks := txn.readTxn_opsOk t σr.log hro hgets false (W64 (σr.log.length : Int))
  have hnil := txn.srvOps_gets_nil (mvcc.stateAfter σr.log) (W64 (σr.log.length : Int))
    (mvcc.stateAfter σr.log) _ (readonly_branch t hro (txnOk (mvcc.stateAfter σr.log) t))
  wp_apply (hNewRo _ γ trace σr) $$ [$Htx] as %trw Hro
  icases txn.mvccTxn_shape hsh trw γ trace (.read σr) $$ Hro with ⟨%Hshw, Hro⟩
  obtain ⟨wty, wv, rfl, -, -, -, -, -, -, hEndW⟩ := Hshw
  have htxn' := htxn ctx' { cd with Values := vs } false lg γ trace false (interface.mkOk wty wv) true σr
    rt t sl skip []
  simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true, txn.MTxn.append] at htxn'
  wp_apply htxn'
    $$ [$Hro $Htrc $Hctx' $Hct' $Hrt $Hsl $Hleases] as %resp %err ⟨Htrc, Hres⟩
  · isplitl []; · itrivial
    isplitl []; · ileft; itrivial
    ipureintro
    exact ⟨Hreachr, (by simp), hoks, fun _ => hro, fun _ => ⟨trivial, Hlg⟩⟩
  -- the read transaction ends; the response's fields for the trace
  ihave ⟨Hro, #Hshell, Hout⟩ : (mvcc.api.mvccTxn (interface.mkOk wty wv) γ trace (.read σr) ∗
      txnRespShell resp ∗
      ((⌜err = GoInterface.nil⌝ ∗
        txnResponseIs skip resp (W64 (σr.rev : Int)) t
          (srvRunTxn (W64 (σr.log.length : Int)) (mvcc.stateAfter σr.log) t).1
          (srvRunTxn (W64 (σr.log.length : Int)) (mvcc.stateAfter σr.log) t).2.2 ∗
        respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp)) ∨
       (mvcc.errorfIs err ∗ roTxnRespRd resp ∗
        respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp)))) $$ [Hres]
  · icases Hres with (⟨⟨%Herr, -⟩, Hro, #Hresp, Hhdr, -⟩ | ⟨-, #He, Hro, #Hshell, #Hrd, Hhdr⟩)
    · iframe Hro
      have hwr : (W64 (mvcc.writeRev σr.log (txn.txnChs σr.log t) : Int) : w64) =
          W64 (σr.rev : Int) := by
        simp only [txn.txnChs, srvRunTxn, hnil, mvcc.writeRev, ↓reduceIte, mvcc.api.MvccState.rev]
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
    · iframe Hro Hshell
      iright; iframe He Hrd Hhdr
  wp_apply (txn.end_read hEndW γ trace σr) $$ [$Hro] as Htt
  ihave #Hshell2 := Hshell
  iunfold txnRespShell at Hshell2
  icases Hshell2 with ⟨%Hrn, %h, %rsl, %rv0, #Hh, #Hrev, #Hrsl⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fs ⟨Hfs, -⟩
  wp_auto
  wp_apply (hAdd trace false _ _ _) $$ [$Htrc $Hfs] as ⟨Htrc, -⟩
  · ipureintro
    exact traceutil.fieldsWf_cons_int _ _ _ (.int _) _
      (traceutil.fieldsWf_cons_int _ _ _ (.int64 _) _ traceutil.fieldsWf_nil)
  iapply HΦ
  iframe Htt
  iexists σr
  iframe HQ
  isplitl []
  · ipureintro; exact Hreachr
  icases Hout with (⟨%Herr, #Hresp, Hhdr⟩ | ⟨#He, #Hrd, Hhdr⟩)
  · iright; ileft
    isplitr
    · ipureintro; exact ⟨Herr, Htr⟩
    isplitl [Htrc]
    · iexists false; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iframe Hresp Hhdr
  · iright; iright
    isplitr
    · ipureintro; exact Htr
    isplitl [Htrc]
    · iexists false; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iframe He Hrd Hhdr

theorem txn.Txn.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hRO : txn.IsTxnReadonly.spec (GF := GF) (hG := hG))
    (hStepF : traceutil.Trace.StepWithFunction.spec (GF := GF) (hG := hG))
    (hPath : txn.compareToPath.spec (GF := GF) (hG := hG))
    (hAdd : traceutil.Trace.AddField.spec (GF := GF) (hG := hG))
    (hCheck : txn.checkTxn.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hNewRo : mvcc.api.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (htxn : txn.txn.spec (GF := GF) (hG := hG)) :
    txn.Txn.spec (GF := GF) (hG := hG) :=
  ⟨txn.Txn_sole hsh hpers hreach hEnsure hRO hStepF hPath hAdd hCheck hStep hNewRo htxn,
    txn.Txn_read hsh hpers hreach hEnsure hRO hStepF hPath hAdd hCheck hStep hNewRo htxn⟩

end proof

end EtcdGrove
end Perennial
