/-
`(*ControlleeExpectations).Add(add, del)` (`controller_utils.go:283`): two atomic additions to
the counters. Lean-first; phase 5 of `notes/k8s-daemonset-plan.md`.
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

/-- **`e.Add(add, del)`** returns (the counters are tracked loosely: any values). -/
abbrev ControlleeExpectations.Add.spec : Prop :=
  ∀ (e : Loc) (k : GoString) (add del : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ isCE e k }}
    (App (App (Val (e @!! go.GoType.PointerType ControlleeExpectations.ty @!! go!"Add"))
      (Val #add)) (Val #del))
  {{ RET #(); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
