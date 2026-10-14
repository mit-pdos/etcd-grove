/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Get.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Get
public import Spec.go_etcd_io.etcd.client.v3.kv__Do
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.client.v3.ContextError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem kv.Get.wp_proof
    (wp_OpGet : OpGet.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Get.spec (GF := GF) (hG := hG) := by
  intro api addr ci cd key sl gs Spec Q
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, %Hnp, #Hrpc, #Hrun⟩
  obtain ⟨Hnp, Ht, Hs⟩ := Hnp
  wp_auto
  wp_apply wp_OpGet key sl gs $$ [] as %opv #Hat
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api addr ci cd opv (opGetModel key gs) (fun _ _ => iprop(True))
    (fun _ => iprop(True)) Spec Q $$ []
    as %r %err Hout
  · iframe #
    unfold doRunOk
    ileft
    iframe #
    ipureintro; exact ⟨Ht, Hs⟩
  ihave Hout' : rangeCallOut Q r.get' err $$ [Hout]
  · have Heq : doOut (opGetModel key gs) (fun _ => iprop(True)) Q r err =
        rangeCallOut Q r.get' err := by
      unfold doOut; rw [Ht]; simp only [↓reduceIte]
    rw [← Heq]; iexact Hout
  iunfold rangeCallOut at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    unfold rangeCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse'⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    iapply HΦ
    unfold rangeCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial
