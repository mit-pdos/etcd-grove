/-
Proof of `Spec/k8s_io/client_go/util/workqueue/rateLimitingType__AddRateLimited.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__AddRateLimited
public import Spec.k8s_io.client_go.util.workqueue.delayingType__AddAfter

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

theorem rateLimitingType.AddRateLimited.wp_proof
    (wp_AddAfter : delayingType.AddAfter.spec (GF := GF) (hG := hG)) :
    rateLimitingType.AddRateLimited.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ P k
  wp_start as #Hq
  iunfold isRateLimitingQueue at Hq
  icases Hq with ⟨%dq, %rl, #Hdf, #Hd, #Hrlf, #Hrl⟩
  iunfold isRateLimiter at Hrl
  icases Hrl with ⟨%i, %Hi, #HWhen, #HForget, #HNumRequeues⟩
  subst Hi
  wp_auto
  wp_apply HWhen as %d %_
  wp_apply wp_AddAfter $$ [$Hd]
  wp_end

end proof

end workqueue
end EtcdGrove
end Perennial
