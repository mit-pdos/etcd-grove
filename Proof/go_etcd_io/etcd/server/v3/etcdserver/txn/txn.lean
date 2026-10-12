/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.newTxnResp
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

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

theorem txn.txn.wp_proof
    (hNew : txn.newTxnResp.spec (GF := GF) (hG := hG))
    (hExec : txn.executeTxn.spec (GF := GF) (hG := hG))
    (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG))
    (hRoRev : mvcc.txnReadWrite.Rev.spec (GF := GF) (hG := hG))
    (hCh : mvcc.metricsTxnWrite.Changes.spec (GF := GF) (hG := hG))
    (hRoCh : mvcc.txnReadWrite.Changes.spec (GF := GF) (hG := hG)) :
    txn.txn.spec (GF := GF) (hG := hG) := by
  intro ctx cd lg s γ tw ro ilog rt t pl skip
  wp_start as ⟨Htw, #Hctx, #Hnd, #Hrt, #Hpl, #Hleases, #Hknown, %Hpre⟩
  ihave %Htwok := txn.txnWriteIs_ok tw s γ ro ilog [] $$ Htw
  obtain ⟨twi, rfl⟩ := Htwok
  ihave #Hpl' : pl ↦*□ (txnPath (mvcc.stateAfter ilog) t ++ []) $$ []
  · rw [List.append_nil]; iexact Hpl
  ihave #Hknown0 : leasesKnown γ.leases (pendState ilog []) $$ []
  · rw [pendState_nil]; iexact Hknown
  wp_auto
  wp_apply (hNew rt t (mvcc.stateAfter ilog) pl []) $$ [$Hrt $Hpl'] as %resp %n ⟨Hskel, %Hn⟩
  iunfold txnSkel at Hskel
  icases Hskel with ⟨%Hrn, %h, #Hh, %Hhn, Hrev, #Hsucc, Hresps⟩
  wp_apply (hExec ctx cd lg s γ (GoInterface.ok twi) ro ilog [] rt t pl [] resp skip)
    $$ [$Htw $Hctx $Hnd $Hrt $Hpl' $Hresps $Hleases $Hknown0] as %n2 %err ⟨%Herr, Htw, #Hrs, #Hknown'⟩
  · ipureintro
    refine ⟨Hpre.1, ?_, ?_⟩
    · simp only [List.length_nil, Nat.zero_add, pendState_nil]; exact Hpre.2.1
    · intro hro op hop
      exact readonly_branch t (Hpre.2.2 hro) _ op hop
  obtain ⟨rfl, -⟩ := Herr
  wp_auto
  try simp only [List.nil_append] at *
  icases txnWriteIs_kind _ s γ ro ilog _ $$ Htw with ⟨%kind, Hv, %Hk⟩
  ihave Htw := txnWriteIs_of_view _ s γ ro ilog _ kind Hk.1 $$ Hv
  have hne : ilog ≠ [] := Hk.2.2.2.1
  have hlen : ilog.length < 2 ^ 63 := Hk.2.2.2.2
  wp_apply (wp_txnWrite_Rev hRev hRoRev twi s γ ro ilog _) $$ [$Htw] as Htw
  wp_apply (wp_txnWrite_Changes hCh hRoCh twi s γ ro ilog _) $$ [$Htw] as %chs ⟨⟨%Hchs, %Hchs0⟩, Htw⟩
  unfold srvRunTxn
  have hps : pendState ilog [] = mvcc.stateAfter ilog := rfl
  rw [hps] at Hchs
  rw [hps]
  generalize hchl : (srvOps (mvcc.stateAfter ilog) (W64 ↑(List.length ilog)) (mvcc.stateAfter ilog)
    (t.branch (txnOk (mvcc.stateAfter ilog) t))).fst = chl at *
  have hpos := List.length_pos_iff.2 hne
  iapply wp_fupd
  wp_join iprop(∃ rv : w64, rev_ptr ↦ rv ∗ ⌜rv = W64 ((mvcc.writeRev ilog chl : Nat) : Int)⌝)
    with [rev] as ⟨%rv, rev, %Hrv⟩
  · have hcl : chl = [] := by
      apply List.length_eq_zero_iff.1; rw [← Hchs, Hif]; rfl
    iexists _; iframe rev; ipureintro
    unfold mvcc.writeRev; simp only [hcl, ↓reduceIte]; word
  · -- changes
    have hcl : chl ≠ [] := by
      intro h; subst h; apply Hif; simp only [List.length_nil] at Hchs
      word
    iexists _; iframe rev; ipureintro
    unfold mvcc.writeRev; simp only [hcl, ↓reduceIte]; word
  subst Hrv
  ipersist Hrev
  imodintro
  iapply HΦ
  isplitl []; · ipureintro; rfl
  iframe Htw
  isplitl []
  · iunfold txnResponseIs
    isplitl []; · ipureintro; exact Hrn
    iunfold txnRespFieldsIs
    iexists h
    iframe Hh Hrev Hsucc
    isplitl []; · ipureintro; exact Hhn
    iexact Hrs
  rw [show pendState ilog chl = mvcc.applyChanges (W64 ↑(List.length ilog)) (mvcc.stateAfter ilog) chl
    from rfl]
  iexact Hknown'

end proof

end EtcdGrove
end Perennial
