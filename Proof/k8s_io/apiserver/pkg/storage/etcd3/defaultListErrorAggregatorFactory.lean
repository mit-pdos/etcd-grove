/-
Lean-first (no Rocq counterpart).

The proof of `defaultListErrorAggregatorFactory`: an allocation.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.defaultListErrorAggregatorFactory

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem defaultListErrorAggregatorFactory.wp_proof : defaultListErrorAggregatorFactory.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_alloc a as Ha
  wp_auto
  iapply HΦ
  itrivial

end proof

end k8s
end EtcdGrove
end Perennial
