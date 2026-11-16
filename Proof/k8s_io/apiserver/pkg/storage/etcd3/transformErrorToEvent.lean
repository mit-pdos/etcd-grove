/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/transformErrorToEvent.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.transformErrorToEvent
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.interpretWatchError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewInternalError

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem transformErrorToEvent.wp_proof
    (wp_interpretWatchError : interpretWatchError.spec (GF := GF) (hG := hG))
    (wp_NewInternalError : apierrors.NewInternalError.spec (GF := GF) (hG := hG)) :
    transformErrorToEvent.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hok
  ihave #Pae : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  wp_auto
  have hps : go.typeSetContains
      (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty)
      k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = true := by
    go_type_set
  wp_apply wp_interpretWatchError $$ [$Hok] as %err' Herr'
  icases Herr' with (%Herr' | ⟨%p, %st, ⟨%Herr', %Hf⟩, Hp⟩)
  · subst Herr'
    iunfold kErrOk at Hok
    icases Hok with ⟨%e, %He, #Heq, #Hstr, %Hfmt, #Hcode, #Hgrpc, #Has, #Hst⟩
    subst He
    wp_auto
    cases hsa : go.typeSetContains e.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty
    case true =>
      simp only []
      wp_auto
      simp only [hsa, ↓reduceIte]
      wp_auto
      ihave Hs := Hst $$ %trivial
      wp_bind (App (Val #(methods e.ty go!"Status" e.v)) (Val #()))
      iapply Hs
      inext
      iintro %st %Hf
      wp_auto
      iapply HΦ
      iexists _, status_ptr, st
      iframe
      ipureintro
      exact ⟨rfl, rfl, Hf⟩
    simp only [Bool.false_eq_true]
    wp_auto
    wp_apply wp_NewInternalError $$ [] as %p ⟨%st, Hp, %Hf⟩
    iclear Heq Hstr Hcode Hgrpc Has Hst
    (try wp_auto)
    simp only [hps, ↓reduceIte]
    wp_auto
    wp_method_call
    wp_auto
    iapply HΦ
    iexists _, status_ptr, st
    iframe
    ipureintro
    exact ⟨rfl, rfl, Hf.1⟩
  · subst Herr'
    simp only [interface.mkOk, hps, ↓reduceIte]
    wp_auto
    simp only [hps, ↓reduceIte]
    wp_auto
    wp_method_call
    wp_auto
    iapply HΦ
    iexists _, status_ptr, st
    iframe
    ipureintro
    exact ⟨rfl, rfl, Hf⟩

end proof

end k8s
end EtcdGrove
end Perennial
