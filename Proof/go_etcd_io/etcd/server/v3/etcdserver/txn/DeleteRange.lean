/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.deleteRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.FrozenSpecs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.DeleteRange.wp_proof
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (hWWrite : mvcc.watchableStore.Write.spec (GF := GF) (hG := hG))
    (hdel : txn.deleteRange.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (hWEnd : mvcc.watchableStoreTxnWrite.End.spec (GF := GF) (hG := hG)) :
    txn.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro ctx cd nd lg kv s γ dr o m log₀ P Pre Q Post f ot te Lw
  wp_start as ⟨#Hkv, Hrd, Htok, Hwt, Htoks, #Hc0, Hwl, %Hsole, #Hdr, #Hctx, #Hct, Hto, #Hnd, #Hcok, Hcs, Hhook⟩
  iunfold mvcc.csContract at Hcs
  icases Hcs with ⟨Hpre, #Htr, Hupd⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Hdr0 := Hdr
  iunfold txn.deleteRangeRequestIs at Hdr0
  icases Hdr0 with ⟨%Hdnn, %ksl, %esl, %k, %e, %pk, #Hk, #Hks, #He, #Hes, #Hpk, %Ho, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [$Hks] as -
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [$Hes] as -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfsl, Hfslc⟩
  (try wp_auto)
  wp_apply (hEnsure ctx cd ot te lg _ _) $$ [$Hctx $Hct $Hto Hfsl Hfslc]
    as %ctx' %trace ⟨⟨%Ht, %Hteq⟩, Htrc, #Hct', %vs, #Hctx', -⟩
  · iunfold traceutil.ownFields
    iexists _
    iframe Hfsl Hfslc
    ipureintro
    exact traceutil.fieldsWf_cons_string _ _ _
      (traceutil.fieldsWf_cons_string _ _ _ traceutil.fieldsWf_nil)
  (try wp_auto)
  -- `kv.Write(trace)`: the store's, or the watchable store's (unit N4)
  ihave %Hkvok := txn.isKV_ok kv s γ $$ Hkv
  obtain ⟨kty, kvv, rfl⟩ := Hkvok
  (try wp_auto)
  wp_apply (txn.kv_Write hWrite hWWrite kty kvv s γ trace P Pre Q f false m Lw)
    $$ [$Hkv $Hrd $Htok $Hwt $Htoks $Hwl $Hhook $Hpre $Htr $Htrc]
    as %tyX %vX ⟨%ilog, %mw, Htx, Hte, Htoks, %Hil, HQ, Hhook⟩
  · ipureintro; exact ⟨fun h => Hsole h, Ht⟩
  ihave ⟨Hte, #Hw⟩ := txn.twEnd_wrap s γ tyX vX mw ilog $$ Hte
  have hsole : γ.watchQ = true → m + 1 = txn.soleBudget ilog := by
    intro h; rw [Hil h]; exact (Hsole h).1
  -- the caller's update (the writes are the model's): the lock's invariant back for `End`
  imod Hupd $$ HQ with ⟨HP, HPost⟩
  (try wp_auto)
  -- the pin of the transaction's committed log
  ihave ⟨%Hpin, Htoks, -, Htx⟩ := txn.isTxnWrite_pinned γ log₀ ilog [] mw s (W64 0) (W64 0) (W64 0) m
    $$ [$Htoks $Hc0 $Htx]
  ihave ⟨%Hfx, Htx⟩ := txn.isTxnWrite_facts mw s γ ilog [] (W64 0) (W64 0) (W64 0) $$ Htx
  -- `deleteRange(ctx, txnWrite, dr)`
  wp_apply (hdel trace ctx' { cd with Values := vs } nd mw s γ ilog [] (W64 0) (W64 0) (W64 0) dr o
      tyX vX) $$ [$Hctx' $Htx $Hw $Hdr] as %resp %err Hout
  · cases nd
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    · simp only [↓reduceIte, mvcc.neverDone] at *; iexact Hnd
  rw [txn.pendState_nil]
  simp only [List.nil_append]
  icases Hout with (⟨%Herr, ⟨%deletes', Htx⟩, #Hresp, Hhdr⟩ | ⟨%Hne, Htx⟩)
  · -- deleted: the deferred `End` commits (if something was deleted)
    (try wp_auto)
    wp_apply (txn.tw_End hEnd hWEnd tyX vX s γ trace mw ilog
        (txn.delChanges (mvcc.stateAfter ilog) o) (W64 0) deletes' (W64 0) m P f)
      $$ [$Htx $Hte $Htoks HP Hhook] as ⟨Hrd, ⟨%te', Htrc⟩, #Hc, Htok, Htoks, Hwl, Hhook⟩
    · iframe HP Hhook
      isplitl []
      · ipureintro; exact hsole
      iapply Hcok; ipureintro; exact Hpin
    (try wp_auto)
    iapply HΦ
    iframe Hrd Hhook Htoks
    isplitl []
    · ipureintro; exact Ht
    iframe HPost
    isplitl [Htrc]
    · iexists te'; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iexists ilog
    isplitl []
    · ipureintro; exact ⟨Hpin, Hfx.1⟩
    ileft
    iframe Hresp Hhdr Hc Htok Hwl
    ipureintro; exact Herr
  · -- the range read's context error: nothing written, the token back
    (try wp_auto)
    wp_apply (txn.tw_End hEnd hWEnd tyX vX s γ trace mw ilog [] (W64 0) (W64 0) (W64 0) m P f)
      $$ [$Htx $Hte $Htoks HP Hhook] as ⟨Hrd, ⟨%te', Htrc⟩, #Hc, Htok, Htoks, Hwl, Hhook⟩
    · iframe HP Hhook
      isplitl []
      · ipureintro; exact hsole
      iunfold mvcc.certOkNext; ileft; ipureintro; rfl
    simp only [mvcc.commitLog, ↓reduceIte]
    (try wp_auto)
    iapply HΦ
    iframe Hrd Hhook Htoks
    isplitl []
    · ipureintro; exact Ht
    iframe HPost
    isplitl [Htrc]
    · iexists te'; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iexists ilog
    isplitl []
    · ipureintro; exact ⟨Hpin, Hfx.1⟩
    iright
    iframe Htok Hc Hwl
    ipureintro; exact Hne

end proof

end EtcdGrove
end Perennial
