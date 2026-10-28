/-
`util.GetTargetNodeName(pod)` (`daemon/util/daemonset_util.go:226`): the node a DaemonSet pod is
for. Lean-first; phase 5 of `notes/k8s-daemonset-plan.md`.

**What the code does** (read 2026-10-28 at the pin): the pod's `Spec.NodeName` if it is not
empty; else the single value of the first `MatchFields` requirement with key
`metav1.ObjectNameField` and operator `v1.NodeSelectorOpIn` among the terms of the required node
affinity, in order. An error (`fmt.Errorf`) when there is no required node affinity, it has no
terms, no requirement matches, or the matching one has not exactly one value. That is
`dsctl.targetNode keyName opIn` of the pod's deep value (`S1Model.lean`), `none` for the errors.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Model
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.util.Assumptions]

/-- **`util.GetTargetNodeName(p)`** of a pod owned deeply at `dq` with deep value `d`: the node
name `targetNode keyName opIn d` and a `nil` error when it is `some`; else an error whose
`Error()` returns some string. The pod comes back. -/
abbrev GetTargetNodeName.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (d : kd.core.Pod),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.util ∗
      podAt p dq d }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.util.GetTargetNodeName)) (Val #p))
  {{ (n : GoString) (err : GoInterface), RET (PairV #n #err); podAt p dq d ∗
      match targetNode keyName opIn d with
      | some m => ⌜n = m ∧ err = interface.nil⌝
      | none => ∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ fmt.stringMethodSpec e go!"Error" }}

end spec

end dsctl
end EtcdGrove
end Perennial
