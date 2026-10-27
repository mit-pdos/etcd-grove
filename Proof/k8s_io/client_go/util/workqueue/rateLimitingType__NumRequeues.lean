/-
Proof of `Spec/k8s_io/client_go/util/workqueue/rateLimitingType__NumRequeues.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__NumRequeues

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

theorem rateLimitingType.NumRequeues.wp_proof :
    rateLimitingType.NumRequeues.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ P k
  wp_start as #Hq
  iunfold isRateLimitingQueue at Hq
  icases Hq with ⟨%dq, %rl, #Hdf, #Hd, #Hrlf, #Hrl⟩
  iunfold isRateLimiter at Hrl
  icases Hrl with ⟨%i, %Hi, #HWhen, #HForget, #HNumRequeues⟩
  subst Hi
  wp_auto
  wp_apply HNumRequeues as %n -
  wp_end

end proof

end workqueue
end EtcdGrove
end Perennial
