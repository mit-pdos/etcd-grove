/-
`(*LazyErrorNodeSelector).Match(node)` (`nodeaffinity.go:84`): whether some term matches the node's
labels and fields, else the terms' parse errors, aggregated. Its body is gap D2's named hypothesis
(`LazyErrorNodeSelector__Match_body.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel k8s_io.component_helpers.scheduling.corev1.nodeaffinity

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.component_helpers.scheduling.corev1.nodeaffinity.Assumptions]

/-- **`ns.Match(node)`** of a parsed selector (`lesOk`) and a node in the heap: returns (some
`bool` and some error), the node kept. -/
abbrev LazyErrorNodeSelector.Match.spec : Prop :=
  ∀ (ns : Loc) (node : Loc) (dq : DFrac) (d : kd.core.Node),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1.nodeaffinity ∗
      lesOk ns ∗ nodeAt node dq d }}
    (App (Val (ns @!! go.GoType.PointerType LazyErrorNodeSelector.ty @!! go!"Match")) (Val #node))
  {{ (b : Bool) (err : GoInterface), RET (PairV #b #err); nodeAt node dq d }}

end spec

end dsctl
end EtcdGrove
end Perennial
