/-
`NewRetryWithDeadline(maxRetryDuration, minResetPeriod, isRetryable, clock)`
(`retry_with_deadline.go:41`): a fresh `*retryWithDeadlineImpl` as a `RetryWithDeadline`. Lean-first;
phase 4 of `notes/k8s-daemonset-plan.md`, fifth round. Stated for the reflector's `watch`'s call:
`apierrors.IsInternalError` and a real clock.
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefWatchDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`NewRetryWithDeadline(md, mr, apierrors.IsInternalError, c)`**: its retry state. -/
abbrev NewRetryWithDeadline.spec : Prop :=
  ∀ (md mr : time.Duration) (c : k8s_io.utils.clock.RealClock),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache }}
    (App (App (App (App (Val (@! k8s_io.client_go.tools.cache.NewRetryWithDeadline)) (Val #md))
      (Val #mr)) (Val #(functions k8s_io.apimachinery.pkg.api.errors.IsInternalError [])))
      (Val #(interface.mkOk k8s_io.utils.clock.RealClock.ty #c : k8s_io.utils.clock.Clock)))
  {{ (rt : GoInterface), RET #rt; retryOwn rt }}

end spec

end cache
end EtcdGrove
end Perennial
