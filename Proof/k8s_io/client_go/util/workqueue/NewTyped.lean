/-
Proof of `Spec/k8s_io/client_go/util/workqueue/NewTyped.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.NewTyped
public import Spec.k8s_io.client_go.util.workqueue.NewTypedWithConfig

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem NewTyped.wp_proof
    (wp_NewTypedWithConfig : NewTypedWithConfig.spec (GF := GF) (hG := hG)) :
    NewTyped.spec (GF := GF) (hG := hG) := by
  intro K T _
  wp_start
  (try wp_auto)
  wp_apply wp_NewTypedWithConfig (K := K) (T := T) _ ⟨rfl, Or.inl rfl⟩ as %q %γ H
  iapply HΦ $$ H

end proof

end workqueue
end EtcdGrove
end Perennial
