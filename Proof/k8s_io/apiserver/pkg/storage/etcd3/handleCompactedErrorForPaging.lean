/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/handleCompactedErrorForPaging.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.handleCompactedErrorForPaging
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewResourceExpired
public import Spec.k8s_io.apiserver.pkg.storage.EncodeContinue

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem handleCompactedErrorForPaging.wp_proof
    (wp_EncodeContinue : storage.EncodeContinue.spec (GF := GF) (hG := hG))
    (wp_NewResourceExpired : apierrors.NewResourceExpired.spec (GF := GF) (hG := hG)) :
    handleCompactedErrorForPaging.spec (GF := GF) (hG := hG) := by
  intro ck kp henc
  wp_start as -
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  ihave #Pae : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_EncodeContinue as %t %err %Henc
  rw [henc] at Henc
  obtain ⟨-, rfl⟩ := Henc
  wp_auto
  wp_apply wp_NewResourceExpired as %p ⟨%st, Hp, %Hst⟩
  wp_auto
  sorry

end proof

end k8s
end EtcdGrove
end Perennial
