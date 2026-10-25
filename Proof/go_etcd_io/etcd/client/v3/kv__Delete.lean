/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Delete.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Delete
public import Spec.go_etcd_io.etcd.client.v3.kv__Do
public import Spec.go_etcd_io.etcd.client.v3.OpDelete
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Proof.go_etcd_io.etcd.client.v3.KVMembers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem kv.Delete.wp_members
    (wp_OpDelete : OpDelete.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.specM (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Delete.specM (GF := GF) (hG := hG) := by
  intro api ms ci cd key sl gs Q F
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, %Hnp, #HF, Hrun⟩
  obtain ⟨Hnp, Ht, Hz⟩ := Hnp
  wp_auto
  wp_apply wp_OpDelete key sl gs $$ [] as %opv #Hat
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api ms ci cd opv (opDeleteModel key gs) (W64 0) F Q $$ [Hrun]
    as %r %err Hout
  · iframe #
    unfold doRunM
    iright
    iright
    iframe # Hrun
    ipureintro; exact ⟨Ht, Hz⟩
  ihave Hout' : deleteCallOut (delAns ms F (deleteWireOf (opDeleteModel key gs)) Q) r.del' err
      $$ [Hout]
  · have Heq : doOut (opDeleteModel key gs) (putAns ms F (putWireOf (opDeleteModel key gs)) Q)
        (rangeAns ms (W64 0) F (rangeWireOf (opDeleteModel key gs)) Q)
        (delAns ms F (deleteWireOf (opDeleteModel key gs)) Q) r err =
        deleteCallOut (delAns ms F (deleteWireOf (opDeleteModel key gs)) Q) r.del' err := by
      unfold doOut; rw [Ht]; simp only [show (W64 3 = W64 1) = False by decide,
        show (W64 3 = W64 2) = False by decide, ↓reduceIte]
    rw [← Heq]; iexact Hout
  iunfold deleteCallOut at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    unfold deleteCallOut
    ileft
    iframe Hm
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    unfold deleteCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩


theorem kv.Delete.wp_proof
    (wp_OpDelete : OpDelete.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Delete.spec (GF := GF) (hG := hG) := by
  intro api γ dup ci cd key sl gs Q
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, %Hnp, Hrun⟩
  obtain ⟨Hnp, Ht, Hz, Hw⟩ := Hnp
  wp_auto
  wp_apply wp_OpDelete key sl gs $$ [] as %opv #Hat
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api γ dup ci cd opv (opDeleteModel key gs) Q $$ [Hrun]
    as %r %err Hout
  · iframe #
    unfold doRunOk
    iright
    iright
    iframe # Hrun
    ipureintro; exact ⟨Ht, Hz, Hw⟩
  ihave Hout' : deleteCallOut (delStOk (deleteWireOf (opDeleteModel key gs)) Q) r.del' err
      $$ [Hout]
  · have Heq : doOut (opDeleteModel key gs) (putStOk (putWireOf (opDeleteModel key gs)) Q)
        (rangeStOk (rangeWireOf (opDeleteModel key gs)) Q)
        (delStOk (deleteWireOf (opDeleteModel key gs)) Q) r err =
        deleteCallOut (delStOk (deleteWireOf (opDeleteModel key gs)) Q) r.del' err := by
      unfold doOut; rw [Ht]; simp only [show (W64 3 = W64 1) = False by decide,
        show (W64 3 = W64 2) = False by decide, ↓reduceIte]
    rw [← Heq]; iexact Hout
  iunfold deleteCallOut at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    iapply deleteCallOut_st
    unfold deleteCallOut
    ileft
    iframe Hm
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    iapply deleteCallOut_st
    unfold deleteCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial
