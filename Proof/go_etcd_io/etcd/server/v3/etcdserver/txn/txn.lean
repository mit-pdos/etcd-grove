/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.newTxnResp
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnLemmas
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error

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

instance txn.ite_persistent_txn (b : Bool) (P Q : IProp GF) [Persistent P] [Persistent Q] :
    Persistent (if b then P else Q) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

theorem txn.txn.wp_proof
    (hNew : txn.newTxnResp.spec (GF := GF) (hG := hG))
    (hExec : txn.executeTxn.spec (GF := GF) (hG := hG))
    (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG))
    (hRoRev : mvcc.txnReadWrite.Rev.spec (GF := GF) (hG := hG))
    (hCh : mvcc.metricsTxnWrite.Changes.spec (GF := GF) (hG := hG))
    (hRoCh : mvcc.txnReadWrite.Changes.spec (GF := GF) (hG := hG))
    (hZErr : zap.Error.spec (GF := GF) (hG := hG))
    (hLgErr : zap.Logger.Error.spec (GF := GF) (hG := hG)) :
    txn.txn.spec (GF := GF) (hG := hG) := by
  intro ctx cd nd lg s γ tw ro ilog rt t pl skip
  wp_start as ⟨Htw, #Hctx, #Hnd, #Hrt, #Hpl, #Hleases, #Hknown, %Hpre⟩
  ihave %Htwok := txn.txnWriteIs_ok tw s γ ro ilog [] $$ Htw
  obtain ⟨twi, rfl⟩ := Htwok
  ihave #Hpl' : pl ↦*□ (txnPath (mvcc.stateAfter ilog) t ++ []) $$ []
  · rw [List.append_nil]; iexact Hpl
  ihave #Hknown0 : (if ro then iprop(True) else leasesKnown γ.leases (pendState ilog [])) $$ []
  · rw [pendState_nil]; iexact Hknown
  wp_auto
  wp_apply (hNew rt t (mvcc.stateAfter ilog) pl []) $$ [$Hrt $Hpl'] as %resp %n ⟨Hskel, Hhdr, %Hn⟩
  iunfold txnSkel at Hskel
  icases Hskel with ⟨%Hrn, %h, #Hh, %Hhn, Hrev, #Hsucc, Hresps⟩
  ihave #Hrsl : (∃ sl : GoSlice, structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl)
    $$ [Hresps]
  · iunfold respsSkel at Hresps
    icases Hresps with ⟨%sl, %ps, #Hsl, -⟩
    iexists sl; iexact Hsl
  wp_apply (hExec ctx cd nd lg s γ (GoInterface.ok twi) ro ilog [] rt t pl [] resp skip)
    $$ [$Htw $Hctx $Hnd $Hrt $Hpl' $Hresps $Hleases $Hknown0] as %n2 %err Hres
  · ipureintro
    refine ⟨Hpre.1, ?_, ?_, fun h => (Hpre.2.2.2 h).1⟩
    · simp only [List.length_nil, Nat.zero_add, pendState_nil]; exact Hpre.2.1
    · intro hro op hop
      exact readonly_branch t (Hpre.2.2.1 hro) _ op hop
  icases Hres with (⟨%Herr, Htw, #Hrs, #Hknown'⟩ | ⟨%Hndf, #He, %pend', Htw⟩)
  rotate_left
  · -- the context done during a range: logged, the response returned with the error
    obtain ⟨hro, hlg⟩ := Hpre.2.2.2 Hndf
    subst hro
    ihave #He2 := He
    iunfold mvcc.errorfIs at He2
    icases He2 with ⟨%x, %Hx, -⟩
    subst Hx
    ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
    · iPkgInit
    wp_auto
    wp_apply hZErr as %fld -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    wp_auto
    wp_apply hLgErr $$ []
    · iframe #; ipureintro; exact hlg
    icases txnWriteIs_kind _ s γ true ilog _ $$ Htw with ⟨%kind, Hv, %Hk⟩
    ihave Htw := txnWriteIs_of_view _ s γ true ilog _ kind Hk.1 $$ Hv
    wp_apply (wp_txnWrite_Rev hRev hRoRev twi s γ true ilog _) $$ [$Htw] as Htw
    wp_apply (wp_txnWrite_Changes hCh hRoCh twi s γ true ilog _) $$ [$Htw] as %chs ⟨-, Htw⟩
    iapply wp_fupd
    wp_join iprop(∃ rv : w64, rev_ptr ↦ rv) with [rev] as ⟨%rv, rev⟩
    ipersist Hrev
    imodintro
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact Hndf
    iframe He
    isplitl [Htw]
    · iexists _; iexact Htw
    iunfold txnRespShell
    isplitr
    · ipureintro; exact Hrn
    icases Hrsl with ⟨%sl, #Hsl⟩
    iexists h, sl, _
    iframe Hh Hrev Hsl
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
  ileft
  isplitl []; · ipureintro; rfl
  iframe Htw Hhdr
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
