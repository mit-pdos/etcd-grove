/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.DeleteRange
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.deleteRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccName)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.DeleteRange.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hdel : txn.deleteRange.spec (GF := GF) (hG := hG)) :
    txn.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro ctx cd nd lg kv γ dr o q B P Pre Q Post f ot te L I R
  haveI := hpers.1 kv γ
  wp_start as ⟨#Hkv, Htt, #Hdr, Hown, #Hctx, #Hct, Hto, #Hnd, Hbk, Hcs, Hau⟩
  iunfold txn.kvBackend at Hbk
  icases Hbk with ⟨Hbk, #Hhook⟩
  iunfold txn.csA at Hcs
  icases Hcs with ⟨Hpre, Htr, Hupd⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Hdr0 := Hdr
  iunfold txn.deleteRangeRequestIs at Hdr0
  icases Hdr0 with ⟨%Hdnn, %ksl, %esl, %k, %e, %pk, #Hk, #Hks, #He, #Hes, #Hpk, %Ho, -⟩
  wp_auto
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
    as %ctx' %trace ⟨⟨%Ht, %Hteq⟩, Htrc, #Hct', -, %vs, #Hctx', -⟩
  · iunfold traceutil.ownFields
    iexists _
    iframe Hfsl Hfslc
    ipureintro
    exact traceutil.fieldsWf_cons_string _ _ _
      (traceutil.fieldsWf_cons_string _ _ _ traceutil.fieldsWf_nil)
  (try wp_auto)
  -- `kv.Write(trace)`
  iunfold txn.delAU at Hau
  ihave Hau := txn.beginAU_reach hpers hreach kv γ _ $$ Hkv Hau
  icases txn.isMvcc_shape hsh kv γ $$ Hkv with ⟨%Hsh, -⟩
  obtain ⟨kty, kvv, rfl, -, hWriteC, -⟩ := Hsh
  (try wp_auto)
  wp_apply (hWriteC γ trace false q B P Pre Q f _) $$ [$Hkv $Htt $Htrc $Hbk $Hhook $Hpre $Htr $Hau]
    as %t ⟨Htrc, Hbk, ⟨%σ₀, Htx, ⟨%Hreach0, %Hitems, Hcommit⟩⟩, HQ⟩
  · ipureintro; exact Ht
  icases txn.mvccTxn_shape hsh t γ trace (.write σ₀ []) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tty, tv, rfl, -, -, -, -, -, -, hEndC⟩ := Hsht
  -- the caller's update (the writes are the model's): the lock's invariant back for `End`
  imod Hupd $$ HQ with ⟨HP, HPost⟩
  (try wp_auto)
  -- `deleteRange(ctx, txnWrite, dr)`
  ihave Hown : EtcdGrove.lease.leaseOwn (mvcc.api.mvccLeases γ) L (mvcc.pendItems σ₀.log []) $$ [Hown]
  · rw [Hitems]; iexact Hown
  wp_apply (hdel ctx' { cd with Values := vs } nd _ γ trace false σ₀ [] dr o L)
    $$ [$Hctx' $Htx $Htrc $Hdr $Hown] as %resp %err ⟨Htrc, Hout⟩
  · isplitl [Hnd]
    · cases nd
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      · simp only [↓reduceIte, mvcc.neverDone] at *; iexact Hnd
    ipureintro; exact Hreach0.1
  rw [txn.pendState_nil]
  simp only [List.nil_append]
  icases Hout with (⟨%Herr, Htx, #Hresp, Hhdr, Hown⟩ | ⟨%Hne, Htx, Hown⟩)
  · -- deleted: the deferred `End` commits (if something was deleted)
    (try wp_auto)
    ihave Hcommit := Hcommit $$ %true
    have hdp : txn.delPend o σ₀ true = txn.delChanges (mvcc.stateAfter σ₀.log) o := rfl
    rw [hdp]
    wp_apply (txn.end_write hEndC γ trace σ₀ _ q B P (R σ₀ true)) $$ [$Htx $Hbk $HP $Hcommit] as ⟨Htt, Hbk, HR⟩
    (try wp_auto)
    iapply HΦ
    ihave Hbk : txn.kvBackend γ q B P f $$ [Hbk]
    · iunfold txn.kvBackend; iframe Hbk Hhook
    iframe Htt Hbk HPost
    isplitl []
    · ipureintro; exact Ht
    isplitl [Htrc]
    · iexists false; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iexists σ₀
    isplitl []
    · ipureintro; exact Hreach0
    ileft
    iframe Hresp Hhdr HR Hown
    ipureintro; exact Herr
  · -- the range read's context error: nothing written
    (try wp_auto)
    ihave Hcommit := Hcommit $$ %false
    have hdp : txn.delPend o σ₀ false = [] := rfl
    rw [hdp]
    wp_apply (txn.end_write hEndC γ trace σ₀ _ q B P (R σ₀ false)) $$ [$Htx $Hbk $HP $Hcommit] as ⟨Htt, Hbk, HR⟩
    (try wp_auto)
    iapply HΦ
    ihave Hbk : txn.kvBackend γ q B P f $$ [Hbk]
    · iunfold txn.kvBackend; iframe Hbk Hhook
    iframe Htt Hbk HPost
    isplitl []
    · ipureintro; exact Ht
    isplitl [Htrc]
    · iexists false; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iexists σ₀
    isplitl []
    · ipureintro; exact Hreach0
    iright
    iframe HR
    isplitl []
    · ipureintro; exact Hne
    rw [← Hitems]
    iexact Hown

end proof

end EtcdGrove
end Perennial
