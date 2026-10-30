/-
Proof of `Spec/k8s_io/client_go/tools/cache/retryWithDeadlineImpl__reset.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.retryWithDeadlineImpl__reset

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem retryWithDeadlineImpl.reset.wp_proof : retryWithDeadlineImpl.reset.spec (GF := GF) (hG := hG) := by
  intro l v
  wp_start as Hl
  wp_auto
  iapply HΦ
  unfold retryReset
  iexact Hl

end proof

end cache
end EtcdGrove
end Perennial
