/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/IsTooLargeResourceVersion.lean`. Lean-first (no Rocq
counterpart): `IsTimeout`'s answer, then `HasStatusCause`'s, each read off the view.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.IsTooLargeResourceVersion
public import Spec.k8s_io.apimachinery.pkg.api.errors.IsTimeout
public import Spec.k8s_io.apimachinery.pkg.api.errors.HasStatusCause
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]
variable [errors_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem storage.IsTooLargeResourceVersion.wp_proof
    (wp_IsTimeout : apierrors.IsTimeout.spec (GF := GF) (hG := hG))
    (wp_HasStatusCause : apierrors.HasStatusCause.spec (GF := GF) (hG := hG)) :
    storage.IsTooLargeResourceVersion.spec (GF := GF) (hG := hG) := by
  intro err w
  wp_start as #Hw
  ihave #Pe : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_IsTimeout err) as %b1 #H1
  ihave %h1 := H1 $$ Hw
  cases b1
  · (try wp_auto)
    have heq : apierrors.tooLargeV w = false := by
      cases w <;> simp_all [apierrors.tooLargeV]
    rw [heq]
    iapply HΦ
    itrivial
  · (try wp_auto)
    wp_apply (wp_HasStatusCause err _) as %b2 #H2
    ihave %h2 := H2 $$ Hw
    have heq : apierrors.tooLargeV w = b2 := by
      cases w <;> simp_all [apierrors.tooLargeV]
    rw [heq]
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
