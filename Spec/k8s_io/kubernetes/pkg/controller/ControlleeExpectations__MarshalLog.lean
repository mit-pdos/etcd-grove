/-
`(*ControlleeExpectations).MarshalLog()` (`controller_utils.go:301`): a copy of the counters
(atomic loads) and the key, as an `interface{}`. Lean-first; phase 5 of `notes/k8s-daemonset-plan.md`.
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

/-- **`e.MarshalLog()`**: some value. -/
abbrev ControlleeExpectations.MarshalLog.spec : Prop :=
  ∀ (e : Loc) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ isCE e k }}
    (App (Val (e @!! go.GoType.PointerType ControlleeExpectations.ty @!! go!"MarshalLog")) (Val #()))
  {{ (v : GoInterface), RET #v; True }}

end spec

end dsctl
end EtcdGrove
end Perennial
