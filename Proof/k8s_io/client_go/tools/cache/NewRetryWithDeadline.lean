/-
Proof of `Spec/k8s_io/client_go/tools/cache/NewRetryWithDeadline.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.NewRetryWithDeadline

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem NewRetryWithDeadline.wp_proof : NewRetryWithDeadline.spec (GF := GF) (hG := hG) := by
  intro md mr c
  wp_start
  wp_auto
  wp_apply wp_alloc as %l Hl
  (try wp_auto)
  iapply HΦ
  unfold retryOwn
  iexists l, _, c
  iframe
  ipureintro
  exact ⟨rfl, rfl, rfl⟩

end proof

end cache
end EtcdGrove
end Perennial
