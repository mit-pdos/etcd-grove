/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.newTxnResp
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeTxn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas
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
open mvcc.api (MvccState MTxn MvccName)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.txn.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hNew : txn.newTxnResp.spec (GF := GF) (hG := hG))
    (hExec : txn.executeTxn.spec (GF := GF) (hG := hG))
    (hZErr : zap.Error.spec (GF := GF) (hG := hG))
    (hLgErr : zap.Logger.Error.spec (GF := GF) (hG := hG)) :
    txn.txn.spec (GF := GF) (hG := hG) := by
  intro ctx cd nd lg γ trace te tw ro σ rt t pl skip L k chs
  wp_start as ⟨Htw, Htrc, #Hctx, #Hct, #Hnd, #Hrt, #Hpl, #Hleases, #Hknown, Hown, %Hpre⟩
  obtain ⟨hreach, hpend, hops, hro, hndro⟩ := Hpre
  have hkst : k.state = σ := by cases ro <;> rfl
  have hkr : txn.MTxn.isRead k = ro := by cases ro <;> rfl
  have hkm : txn.mstate k = mvcc.stateAfter σ.log := by cases ro <;> rfl
  have hkp : k.pend = [] := by cases ro <;> rfl
  have hlen2 := txn.reach_len σ hreach.1
  icases txn.mvccTxn_shape hsh tw γ trace k $$ Htw with ⟨%Hsh, Htw⟩
  obtain ⟨tyX, vX, rfl, hRevC, -, -, -, -, hChC, -⟩ := Hsh
  ihave #Hpl' : pl ↦*□ (txnPath (mvcc.stateAfter σ.log) t ++ []) $$ []
  · rw [List.append_nil]; iexact Hpl
  ihave #Hknown0 : (if txn.MTxn.isRead k then iprop(True) else leasesKnown L (mvcc.stateAfter σ.log))
    $$ []
  · rw [hkr]; iexact Hknown
  ihave Hown0 : (⌜txn.MTxn.isRead k = true⌝ ∨
      lease.leaseOwn (mvcc.api.mvccLeases γ) L (mvcc.pendItems σ.log k.pend)) $$ [Hown]
  · rw [hkr, hkp, mvcc.api.pendItems_nil]; iexact Hown
  wp_auto
  wp_apply (hNew rt t (mvcc.stateAfter σ.log) pl []) $$ [$Hrt $Hpl'] as %resp %n ⟨Hskel, Hhdr, %Hn⟩
  iunfold txnSkel at Hskel
  icases Hskel with ⟨%Hrn, %h, #Hh, %Hhn, Hrev, #Hsucc, Hresps⟩
  ihave #Hrsl : (∃ sl : GoSlice, structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl)
    $$ [Hresps]
  · iunfold respsSkel at Hresps
    icases Hresps with ⟨%sl, %ps, #Hsl, -⟩
    iexists sl; iexact Hsl
  have hE := hExec ctx cd nd lg γ trace te (interface.mkOk tyX vX) k rt t pl [] resp skip L
  simp only [hkst, hkm] at hE
  wp_apply hE $$ [$Htw $Htrc $Hctx $Hct $Hnd $Hrt $Hpl' $Hresps $Hleases $Hknown0 $Hown0]
    as %n2 %err Hres
  · ipureintro
    refine ⟨hreach, hops, ?_, fun h => by rw [hkr]; exact (hndro h).1⟩
    intro hr op hop
    rw [hkr] at hr
    exact readonly_branch t (hro hr) _ op hop
  icases Hres with ⟨Htrc, (⟨⟨%Herr, -, %Hrun⟩, Htw, #Hrs, #Hknown', Hown⟩ | ⟨%Hndf, #He, Htw, #Hros⟩)⟩
  rotate_left
  · -- the context done during a range: logged, the response returned with the error
    obtain ⟨hro1, hlg⟩ := hndro Hndf
    subst hro1
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
    wp_apply (hRevC γ trace k) $$ [$Htw] as Htw
    wp_apply (hChC γ trace k) $$ [$Htw] as %chs' ⟨Htw, -⟩
    iapply wp_fupd
    wp_join iprop(∃ rv : w64, rev_ptr ↦ rv) with [rev] as ⟨%rv, rev⟩
    ipersist Hrev
    imodintro
    iapply HΦ
    iframe Htrc
    iright
    isplitr
    · ipureintro; exact Hndf
    iframe He Htw
    isplitr
    · iunfold txnRespShell
      isplitr
      · ipureintro; exact Hrn
      icases Hrsl with ⟨%sl, #Hsl⟩
      iexists h, sl, _
      iframe Hh Hrev Hsl
    isplitr
    · iunfold roTxnRespRd
      isplitr
      · ipureintro; exact Hrn
      iexists h, _, _
      iframe Hh Hrev Hsucc Hros
      ipureintro; exact Hhn
    iexact Hhdr
  subst Herr
  wp_auto
  generalize hchl : (srvOps (mvcc.stateAfter σ.log) (W64 ↑(List.length σ.log)) (mvcc.stateAfter σ.log)
    (t.branch (txnOk (mvcc.stateAfter σ.log) t))).fst = chl at *
  have hchs : chs = chl := by
    simp only [chs, txn.txnChs, srvRunTxn]; exact hchl
  wp_apply (hRevC γ trace (txn.MTxn.append k chl)) $$ [$Htw] as Htw
  wp_apply (hChC γ trace (txn.MTxn.append k chl)) $$ [$Htw] as %chsl ⟨Htw, %Hchs2⟩
  have Hchs := Hchs2.1
  have hpendc : (txn.MTxn.append k chl).pend = chl := by
    cases ro
    · rfl
    · simp only [k, txn.MTxn.append, mvcc.api.MTxn.pend]; exact (Hrun (by rfl)).symm
  rw [hpendc] at Hchs
  rw [txn.MTxn.append_state, hkst]
  iapply wp_fupd
  wp_join iprop(∃ rv : w64, rev_ptr ↦ rv ∗ ⌜rv = W64 ((mvcc.writeRev σ.log chl : Nat) : Int)⌝)
    with [rev] as ⟨%rv, rev, %Hrv⟩
  · have hcl : chl = [] := by
      apply List.length_eq_zero_iff.1; rw [← Hchs, Hif]; rfl
    iexists _; iframe rev; ipureintro
    unfold mvcc.writeRev mvcc.api.MvccState.rev; simp only [hcl, ↓reduceIte]
  · -- changes
    have hcl : chl ≠ [] := by
      intro h0; subst h0; apply Hif; simp only [List.length_nil] at Hchs
      word
    iexists _; iframe rev; ipureintro
    unfold mvcc.writeRev mvcc.api.MvccState.rev; simp only [hcl, ↓reduceIte]
    word
  subst Hrv
  ipersist Hrev
  imodintro
  iapply HΦ
  iframe Htrc
  ileft
  isplitl []
  · ipureintro; refine ⟨rfl, fun h0 => ?_⟩; rw [hchs]; exact Hrun (by rw [hkr]; exact h0)
  rw [hchs]
  iframe Htw Hhdr
  isplitl []
  · unfold srvRunTxn
    rw [hchl]
    iunfold txnResponseIs
    isplitl []; · ipureintro; exact Hrn
    iunfold txnRespFieldsIs
    iexists h
    iframe Hh Hrev Hsucc
    isplitl []; · ipureintro; exact Hhn
    iexact Hrs
  have hm2 : ro = false → txn.mstate (txn.MTxn.append k chl) =
      mvcc.applyChanges (W64 ↑(List.length σ.log)) (mvcc.stateAfter σ.log) chl := by
    intro h0; subst h0; rfl
  isplitl []
  · cases ro
    · rw [← hm2 rfl, ← hkr]; iexact Hknown'
    · simp only [↓reduceIte]; itrivial
  · icases Hown with (%Hf | Hown)
    · ileft; ipureintro; rw [← hkr]; exact Hf
    · iright
      rw [show mvcc.leaseItemsOf (mvcc.applyChanges (W64 ↑(List.length σ.log)) (mvcc.stateAfter σ.log) chl)
          = mvcc.pendItems σ.log (k.pend ++ chl) by rw [hkp]; rfl]
      iexact Hown

end proof

end EtcdGrove
end Perennial
