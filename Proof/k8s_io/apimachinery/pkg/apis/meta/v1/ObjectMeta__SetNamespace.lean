/-
Proof of `Spec/k8s_io/apimachinery/pkg/apis/meta/v1/ObjectMeta__SetNamespace.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.ObjectMeta__SetNamespace

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metav1

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

theorem ObjectMeta.SetNamespace.wp_proof : ObjectMeta.SetNamespace.spec (GF := GF) (hG := hG) := by
  intro l v x
  wp_start as Hl
  wp_auto
  iapply HΦ
  iframe

end proof

end metav1
end EtcdGrove
end Perennial
