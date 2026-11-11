/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/getNewItemFunc.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.getNewItemFunc
public import Spec.reflect.Value__Type
public import Spec.reflect.Type__Elem
public import Spec.reflect.New
public import Spec.reflect.Value__Interface

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver reflectM

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem getNewItemFunc.wp_proof
    (wp_Type : reflect.Value.Type.spec (GF := GF) (hG := hG))
    (wp_Elem : reflect.Type.Elem.spec (GF := GF) (hG := hG))
    (wp_New : reflect.New.spec (GF := GF) (hG := hG))
    (wp_Interface : reflect.Value.Interface.spec (GF := GF) (hG := hG)) :
    getNewItemFunc.spec (GF := GF) (hG := hG) := by
  intro Obj S L pl v
  wp_start as %Hpre
  obtain ⟨hty, hun, hv⟩ := Hpre
  ihave #Pr : isPkgInit (PROP := IProp GF) pkg_id.reflect $$ []
  · iPkgInit
  wp_auto
  have hne : go.GoType.PointerType L.listTy ≠ go.GoType.PointerType
      k8s_io.apimachinery.pkg.apis.«meta».v1.unstructured.UnstructuredList.ty :=
    fun h => hun (by injection h)
  rw [ite_eq_right_iff.mpr (fun h => absurd h hne), decide_eq_false hne]
  wp_auto
  wp_apply (wp_Type v_ptr _ v _ _) $$ [$v] as %rt ⟨v, %hrt⟩
  · ipureintro; exact hv
  iapply wp_fupd
  wp_apply (wp_Elem rt S.objTy) as %et %het
  · ipureintro; exact hrt
  ipersist elem
  imodintro
  iapply HΦ
  iunfold newItemOk
  iintro !> %Ψ HΨ
  wp_auto
  wp_apply (wp_New et S.objTy) as %w %q ⟨%hwq, Hn⟩
  · ipureintro; exact het
  wp_apply (wp_Interface w S.objTy q)
  · ipureintro; exact hwq.1
  simp only [hty.1, ↓reduceIte]
  iapply wp_fupd
  wp_auto
  imod (S.newObj q) $$ Hn with Ho
  imodintro
  iapply HΨ $$ Ho

end proof

end k8s
end EtcdGrove
end Perennial
