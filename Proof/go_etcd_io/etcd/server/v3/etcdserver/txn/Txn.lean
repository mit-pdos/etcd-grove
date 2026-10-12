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

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

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
    (hNewRo : mvcc.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (htxn : txn.txn.spec (GF := GF) (hG := hG))
    (hRoEnd : mvcc.txnReadWrite.End.spec (GF := GF) (hG := hG)) :
    txn.Txn.spec (GF := GF) (hG := hG) := by
  intro ctx cd lg rt shared kv le skip s γ log t P Pre Q Post f
  wp_start as ⟨#Hkv, Hrd, Hsw, #Hle, #Hrt, #Hctx, #Hnd, #Hknown, %Hpre, Hcs, #Hhook⟩
  iunfold mvcc.csContract at Hcs
  icases Hcs with ⟨HPre, #Htr, Hupd⟩
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  iunfold txn.isKV at Hkv
  icases Hkv with ⟨%Hkv, #Hs⟩
  subst Hkv
  wp_auto
  wp_apply (hEnsure ctx cd lg _ _) $$ [$Hctx] as %ctx' %tr ⟨%Htr, %vs, #Hctx'⟩
  wp_apply (hRO rt t) $$ [$Hrt]
  generalize hw : (!txnReadonly t) = isW
  wp_join iprop(∃ md : w32, mode_ptr ↦ md ∗ txnModeWriteWithSharedBuffer_ptr ↦ shared)
    at (if: _ then _ else _) with [mode txnModeWriteWithSharedBuffer] as ⟨%md, mode, sh⟩
  · cases isW <;> (try cases shared) <;>
      (try simp only [SharedBufReadTxMode, ConcurrentReadTxMode]) <;> wp_auto <;>
      (isplitl []; · itrivial) <;> iexists _ <;> iframe
  have hlen3 : log.length + 3 ≤ 2 ^ 63 := by have := Hpre.1; omega
  wp_apply (txn.soleWriter_Read hRead s γ md tr log hlen3) $$ [$Hs $Hrd $Hsw] as %mw ⟨%rev, Htx, Hsw⟩
  -- `compareToPath` in the trace's step
  wp_apply (hStepF tr _ _ slice.nil
      (fun x => iprop(⌜x = #()⌝ ∗ ∃ sl : GoSlice, txnPath_ptr ↦ sl ∗
        sl ↦* txnPath (mvcc.stateAfter log) t ∗ ownSliceCap Bool sl (DFrac.own 1) ∗
        mvcc.isTxnRead mw s γ log rev ∗
        txnRead_ptr ↦ (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface) ∗
        rt_ptr ↦ rt)))
    $$ [Htx txnPath txnRead rt] as %rv ⟨%Hrv, %sl, txnPath, Hsl, Hcap, Htx, txnRead, rt⟩
  · isplitl []
    · ipureintro; exact Htr
    wp_auto
    wp_apply (hPath mw s γ log rev rt t) $$ [$Htx $Hrt] as %sl ⟨Htx, Hsl, Hcap⟩
    isplitl []; · itrivial
    iexists sl
    iframe
  wp_join with [trace]
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨-, -⟩
    wp_auto
    wp_apply (hAdd tr _) $$ []
    · ipureintro; exact Htr
    try wp_join_done
  ipersist Hsl
  wp_apply (hCheck tr mw s γ log rev rt t le γ.leases sl []) $$ [$Htx $Hrt $Hle] as %n %err ⟨Htx, Hres⟩
  · isplitl []
    · ipureintro; exact Htr
    rw [List.append_nil]; iexact Hsl
  icases Hres with (⟨%Hok, #Hleases⟩ | ⟨%Herr, #Hce⟩)
  rotate_left
  · -- a check failed: the read transaction ended, nothing written
    obtain ⟨Hne, rfl⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      ihave Htx : mvcc.isTxn mw s γ (.read log rev) $$ [Htx]
      · simp only [mvcc.isTxn]; iexact Htx
      ihave Hep : mvcc.txnEndPre γ (.read log rev) $$ []
      · simp only [mvcc.txnEndPre]; itrivial
      wp_apply (hEnd mw s γ (.read log rev)) $$ [$Htx $Hep] as ⟨Hrd, -⟩
      iapply HΦ
      iframe Hrd
      ileft
      iframe Hce Hsw HPre
      ipureintro; exact ⟨rfl, rfl, Hne⟩
  obtain ⟨rfl, -, Hign⟩ := Hok
  wp_auto
  wp_apply (hStep tr _ _)
  have hoks := opsOk_strong _ _ _ _ Hpre.2.1 Hign
  have hlen4 : log.length + 4 ≤ 2 ^ 63 := Hpre.1
  ihave #Hnd' : mvcc.neverDone { cd with Values := vs } $$ []
  · iunfold mvcc.neverDone at Hnd; iunfold mvcc.neverDone; iexact Hnd
  cases isW
  · -- a read-only request: the read transaction, wrapped
    have hro : txnReadonly t = true := by simpa using hw
    wp_auto
    wp_apply (hNewRo mw s γ log rev) $$ [$Htx] as %trw Hro
    ihave Htv := (txnViewIs_ro trw s γ log rev).2 $$ Hro
    ihave Htw := txnWriteIs_of_view _ s γ true log [] _ ⟨rfl, rev, rfl⟩ $$ Htv
    have htxn' := htxn ctx' { cd with Values := vs } lg s γ
      (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw) true log rt t sl skip
    simp only [Bool.not_true] at htxn'
    wp_apply htxn'
      $$ [$Htw $Hctx' $Hnd' $Hrt $Hsl $Hleases $Hknown] as %resp %err ⟨%Herr, Htw, #Hresp, #Hk2⟩
    · ipureintro; exact ⟨hoks, Hpre.2.2, fun _ => hro⟩
    subst Herr
    icases txnWriteIs_kind _ s γ true log _ $$ Htw with ⟨%kind, Hv, %Hk⟩
    obtain ⟨hkis, -, -, -, -⟩ := Hk
    unfold KindIs at hkis
    simp only [↓reduceIte] at hkis
    obtain ⟨hch, rev', rfl⟩ := hkis
    ihave Hro := (txnViewIs_ro trw s γ log rev').1 $$ Hv
    wp_apply (hRoEnd trw s γ log rev') $$ [$Hro] as Hrd
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
    iintro %fs ⟨-, -⟩
    wp_auto
    wp_apply (hAdd tr _) $$ []
    · ipureintro; exact Htr
    iapply HΦ
    iframe Hrd
    iright
    simp only [srvRunTxn]
    rw [hch]
    isplitl []
    · ipureintro; simp [Htr]
    simp only [mvcc.commitLog, ↓reduceIte]
    iframe Hsw Hresp
    isplitl []
    · iexact Hknown
    simp only [hro, ↓reduceIte]
    iexact HPre
  · -- a write: the read ends, the write transaction opens at the sole writer's log
    have hro : txnReadonly t = false := by simpa using hw
    wp_auto
    ihave Htx : mvcc.isTxn mw s γ (.read log rev) $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    ihave Hep : mvcc.txnEndPre γ (.read log rev) $$ []
    · simp only [mvcc.txnEndPre]; itrivial
    wp_apply (hEnd mw s γ (.read log rev)) $$ [$Htx $Hep] as ⟨Hrd, -⟩
    icases soleWriter_split γ log hlen4 $$ Hsw with ⟨Htok, Hsw⟩
    wp_apply (hWrite s γ tr P Pre Q f) $$ [$Hs $Hrd $Htok $Hhook $HPre $Htr]
      as %mw' ⟨⟨%ilog, Htx⟩, HQ⟩
    -- the caller's update (the writes are the model's): the lock's invariant back for `End`
    imod Hupd $$ HQ with ⟨HP, HPost⟩
    iunfold soleWriterOpen at Hsw
    icases Hsw with ⟨#Hc, Htoks⟩
    ihave ⟨%Hpin, Htoks, -, Htx⟩ := isTxnWrite_pinned γ log ilog [] mw' s (W64 0) (W64 0) (W64 0)
      (soleBudget log - 1) $$ [$Htoks $Hc $Htx]
    have hil := pinned_sole log ilog hlen4 Hpin
    subst ilog
    ihave Htx : mvcc.isTxn mw' s γ (.write log [] (W64 0) (W64 0) (W64 0)) $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    ihave Htv := (txnViewIs_mw mw' s γ _).2 $$ Htx
    ihave Htw := txnWriteIs_of_view _ s γ false log [] _ ⟨_, _, _, rfl⟩ $$ Htv
    have htxn' := htxn ctx' { cd with Values := vs } lg s γ
      (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw') false log rt t sl skip
    simp only [Bool.not_false] at htxn'
    wp_apply htxn'
      $$ [$Htw $Hctx' $Hnd' $Hrt $Hsl $Hleases $Hknown] as %resp %err ⟨%Herr, Htw, #Hresp, #Hk2⟩
    · ipureintro; exact ⟨hoks, Hpre.2.2, fun h => by cases h⟩
    subst Herr
    icases txnWriteIs_kind _ s γ false log _ $$ Htw with ⟨%kind, Hv, %Hk⟩
    obtain ⟨hkis, -, -, -, -⟩ := Hk
    obtain ⟨p1, p2, p3, rfl⟩ := hkis
    ihave Htx := (txnViewIs_mw mw' s γ _).1 $$ Hv
    wp_apply (hEnd mw' s γ _) $$ [$Htx Hhook HP] as ⟨Hrd, Hpost⟩
    · iapply mvcc.txnEndPre_write; iframe Hhook HP
    ihave Hsw := soleWriter_close_end γ log _ p1 p2 p3 hlen4 $$ [Htoks Hpost]
    · iframe Hpost; iunfold soleWriterOpen; iframe Hc Htoks
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
    iintro %fs ⟨-, -⟩
    wp_auto
    wp_apply (hAdd tr _) $$ []
    · ipureintro; exact Htr
    iapply HΦ
    iframe Hrd
    iright
    isplitl []
    · ipureintro; exact ⟨rfl, Htr, fun h => by rw [hro] at h; cases h⟩
    rw [stateAfter_commitLog]
    simp only [srvRunTxn]
    iframe Hresp Hsw Hk2
    simp only [hro, Bool.false_eq_true, ↓reduceIte]
    iexact HPost

end proof

end EtcdGrove
end Perennial
