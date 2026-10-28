/-
Proof of `Spec/k8s_io/client_go/tools/cache/MetaObjectToName.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.MetaObjectToName
public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.ObjectMeta__GetNamespace
public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.ObjectMeta__GetName
public import Proof.k8s_io.client_go.tools.cache.DsMeta

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache apimodel

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem MetaObjectToName.wp_proof [apps_sem : k8s_io.api.apps.v1.Assumptions]
    (wp_GetNamespace : metav1.ObjectMeta.GetNamespace.spec (GF := GF) (hG := hG))
    (wp_GetName : metav1.ObjectMeta.GetName.spec (GF := GF) (hG := hG)) :
    MetaObjectToName.spec (GF := GF) (hG := hG) := by
  intro l dq dd
  wp_start as Hds
  wp_auto
  wp_apply (dsAt_GetNamespace wp_GetNamespace l dq dd) $$ [Hds] as Hds
  · iexact Hds
  wp_func_call
  wp_call
  by_cases hl : dd.ObjectMeta'.Namespace'.length < 2 ^ 63
  case neg => simp only [hl, ↓reduceIte]; wp_apply wp_AngelicExit
  simp only [hl, ↓reduceIte]
  wp_auto
  have hz : sint.Z (W64 (dd.ObjectMeta'.Namespace'.length : Int)) =
      dd.ObjectMeta'.Namespace'.length := by word
  wp_if_destruct
  · wp_apply (dsAt_GetNamespace wp_GetNamespace l dq dd) $$ [Hds] as Hds
    · iexact Hds
    wp_apply (dsAt_GetName wp_GetName l dq dd) $$ [Hds] as Hds
    · iexact Hds
    iapply HΦ $$ Hds
  · have he : dd.ObjectMeta'.Namespace' = [] := by
      have h1 : ¬ (0 : Int) < dd.ObjectMeta'.Namespace'.length := by
        rw [← hz]; simpa [show sint.Z (W64 0) = 0 from rfl] using Hif
      exact List.eq_nil_of_length_eq_zero (by omega)
    wp_apply (dsAt_GetName wp_GetName l dq dd) $$ [Hds] as Hds
    · iexact Hds
    rw [he]
    iapply HΦ $$ Hds

end proof

end cache
end EtcdGrove
end Perennial
