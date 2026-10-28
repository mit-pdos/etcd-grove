/-
`NewControllerExpectations()` (`controller_utils.go:314`): a `ControllerExpectations` over a new
`cache.NewStore(ExpKeyFunc)`. Lean-first; phase 5 of `notes/k8s-daemonset-plan.md`.

`ExpKeyFunc` is a package variable, read here: the package's `isPkgInit` is `True` (no proof of
its initialization yet), so its value is a premise: `globalAddr ExpKeyFunc ↦□ kf` with `kf`
meeting `expKeyOk`. The initializer stores the closure `expKeyFn`, which meets it
(`ExpKeyFunc.spec`).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`NewControllerExpectations()`**: the expectations `r` (`isExp`), with all their reader
slots. -/
abbrev NewControllerExpectations.spec : Prop :=
  ∀ (kf : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗
      globalAddr ExpKeyFunc ↦□ kf ∗ expKeyOk kf }}
    (App (Val (@! NewControllerExpectations)) (Val #()))
  {{ (r : Loc), RET #r;
      ∃ γe : ExpNames, isExp r γe ∗
        [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), expReader γe }}

end spec

end dsctl
end EtcdGrove
end Perennial
