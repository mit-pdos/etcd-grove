/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.deleteRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End

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
    (hdel : txn.deleteRange.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    txn.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro ctx cd nd lg kv s γ dr o m log₀ P Pre Q Post f
  wp_start as ⟨#Hkv, Hrd, Htok, Htoks, #Hc0, #Hdr, #Hctx, #Hnd, %Hbig, Hcs, #Hhook⟩
  iunfold mvcc.csContract at Hcs
  icases Hcs with ⟨Hpre, #Htr, Hupd⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Hdr0 := Hdr
  iunfold txn.deleteRangeRequestIs at Hdr0
  icases Hdr0 with ⟨%Hdnn, %ksl, %esl, %k, %e, %pk, #Hk, #Hks, #He, #Hes, #Hpk, %Ho⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [$Hks] as -
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [$Hes] as -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfsl, -⟩
  (try wp_auto)
  wp_apply (hEnsure ctx cd lg _ _) $$ [$Hctx] as %ctx' %t ⟨%Ht, %vs, #Hctx'⟩
  (try wp_auto)
  -- `kv.Write(trace)`: the store's
  iunfold txn.isKV at Hkv
  icases Hkv with ⟨%Hkv, #Hs⟩
  subst Hkv
  (try wp_auto)
  wp_apply (hWrite s γ t P Pre Q f) $$ [$Hs $Hrd $Htok $Hhook $Hpre $Htr] as %mw ⟨⟨%ilog, Htx⟩, HQ⟩
  · ipureintro; exact Ht
  -- the caller's update (the writes are the model's): the lock's invariant back for `End`
  imod Hupd $$ HQ with ⟨HP, HPost⟩
  (try wp_auto)
  -- the pin of the transaction's committed log
  ihave ⟨%Hpin, Htoks, -, Htx⟩ := txn.isTxnWrite_pinned γ log₀ ilog [] mw s (W64 0) (W64 0) (W64 0) m
    $$ [$Htoks $Hc0 $Htx]
  ihave ⟨%Hfx, Htx⟩ := txn.isTxnWrite_facts mw s γ ilog [] (W64 0) (W64 0) (W64 0) $$ Htx
  -- `deleteRange(ctx, txnWrite, dr)`
  have hb : ([] : List mvcc.Change).length + (rangeIn (txn.pendState ilog []) o).length < 2 ^ 63 := by
    rw [txn.pendState_nil, rangeIn]
    have := List.length_filter_le (fun v => inRange o.key o.base.rangeEnd v.key) (mvcc.stateAfter ilog)
    have := Hbig ilog Hpin
    simp only [List.length_nil]; omega
  wp_apply (hdel ctx' { cd with Values := vs } nd mw s γ ilog [] (W64 0) (W64 0) (W64 0) dr o)
    $$ [$Hctx' $Htx $Hdr] as %resp %err Hout
  · isplitl [Hnd]
    · cases nd
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      · simp only [↓reduceIte, mvcc.neverDone] at *; iexact Hnd
    ipureintro; exact hb
  rw [txn.pendState_nil]
  simp only [List.nil_append]
  icases Hout with (⟨%Herr, ⟨%deletes', Htx⟩, #Hresp, Hhdr⟩ | ⟨%Hne, Htx⟩)
  · -- deleted: the deferred `End` commits (if something was deleted)
    ihave Htx : mvcc.isTxn mw s γ (.write ilog (txn.delChanges (mvcc.stateAfter ilog) o) (W64 0)
        deletes' (W64 0)) $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    (try wp_auto)
    wp_apply (hEnd mw s γ _) $$ [$Htx Hhook HP] as ⟨Hrd, Hpost⟩
    · iapply mvcc.txnEndPre_write; iframe Hhook HP
    simp only [mvcc.txnEndPost]
    icases Hpost with ⟨#Hc, Htok⟩
    (try wp_auto)
    iapply HΦ
    iframe Hrd Htoks
    isplitl []
    · ipureintro; exact Ht
    iframe HPost
    iexists ilog
    isplitl []
    · ipureintro; exact ⟨Hpin, Hfx.1⟩
    ileft
    iframe Hresp Hhdr Hc Htok
    ipureintro; exact Herr
  · -- the range read's context error: nothing written, the token back
    ihave Htx : mvcc.isTxn mw s γ (.write ilog [] (W64 0) (W64 0) (W64 0)) $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    (try wp_auto)
    wp_apply (hEnd mw s γ _) $$ [$Htx Hhook HP] as ⟨Hrd, Hpost⟩
    · iapply mvcc.txnEndPre_write; iframe Hhook HP
    simp only [mvcc.txnEndPost, mvcc.commitLog, ↓reduceIte]
    icases Hpost with ⟨#Hc, Htok⟩
    (try wp_auto)
    iapply HΦ
    iframe Hrd Htoks
    isplitl []
    · ipureintro; exact Ht
    iframe HPost
    iexists ilog
    isplitl []
    · ipureintro; exact ⟨Hpin, Hfx.1⟩
    iright
    iframe Htok Hc
    ipureintro; exact Hne

end proof

end EtcdGrove
end Perennial
