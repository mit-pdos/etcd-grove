/-
`(*ControllerExpectations).SatisfiedExpectations(logger, controllerKey)` (`controller_utils.go:195`):
the key's record fulfilled or expired, or no record (or an error). Lean-first; phase 5 of
`notes/k8s-daemonset-plan.md`.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.k8s_io.kubernetes.pkg.controller.ExpDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI k8s_io.kubernetes.pkg.controller

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`r.SatisfiedExpectations(logger, key)`**: some boolean (the counters are tracked loosely and
the clock is not modeled). Needs a reader slot, given back. -/
abbrev ControllerExpectations.SatisfiedExpectations.spec : Prop :=
  ∀ (r : Loc) (γe : ExpNames) (logger : github_com.go_logr.logr.Logger) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ isExp r γe ∗
      expReader γe }}
    (App (App (Val (r @!! go.GoType.PointerType ControllerExpectations.ty @!!
      go!"SatisfiedExpectations")) (Val #logger)) (Val #key))
  {{ (b : Bool), RET #b; expReader γe }}

end spec

end dsctl
end EtcdGrove
end Perennial
