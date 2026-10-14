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
  intro api K ci cd key sl gs Q
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, %Hnp, #Hrun⟩
  obtain ⟨Hnp, Ht, Hs⟩ := Hnp
  wp_auto
  wp_apply wp_OpGet key sl gs $$ [] as %opv #Hat
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api K ci cd opv (opGetModel key gs) (fun _ => iprop(True)) Q $$ []
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
  icases Hout' with (⟨%Herr, #Hm⟩ | %Herr)
  · subst Herr
    wp_apply wp_ContextError ci cd GoInterface.nil as %err' %Herr'
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    unfold rangeCallOut
    ileft
    iframe #
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err as %err' %Herr'
    · iframe #; ipureintro; exact fun _ => Hce'
    iapply HΦ
    unfold rangeCallOut
    iright
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial
