/-
Proof of `Spec/k8s_io/client_go/util/workqueue/NewTypedWithConfig.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.NewTypedWithConfig
public import Spec.k8s_io.client_go.util.workqueue.newQueueWithConfig

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

theorem NewTypedWithConfig.wp_proof
    (wp_newQueueWithConfig : newQueueWithConfig.spec (GF := GF) (hG := hG)) :
    NewTypedWithConfig.spec (GF := GF) (hG := hG) := by
  intro K T _ cfg Hcfg
  wp_start
  wp_auto
  wp_apply wp_newQueueWithConfig (K := K) (T := T) cfg _ Hcfg as %q %γ H
  iapply HΦ $$ H

end proof

end workqueue
end EtcdGrove
end Perennial
