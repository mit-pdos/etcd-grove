/-
Proof of `Spec/k8s_io/client_go/listers/New.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.New

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace listers

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.listers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.Assumptions]

theorem New.wp_proof : New.spec (GF := GF) (hG := hG) := by
  intro X idx res
  wp_start
  (try wp_auto)
  iapply HΦ
  all_goals (try itrivial)

end proof

end listers
end EtcdGrove
end Perennial
