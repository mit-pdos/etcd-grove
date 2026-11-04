/-
`controlledBy(pod, uid)` (`dsmain.go`): whether an owner reference has the UID and `Controller` set. Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Defs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsmain

open Iris Iris.BI apimodel dsctl informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Assumptions]

/-- **`controlledBy(pod, uid)`**: track B's `ctlBy uid` of the pod. -/
abbrev controlledBy.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (d : kd.core.Pod) (uid : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain ∗ podAt p dq d }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.controlledBy)) (Val #p)) (Val #uid))
  {{ (b : Bool), RET #b; podAt p dq d ∗ ⌜b = true ↔ ctlBy uid d⌝ }}

end spec

end dsmain
end EtcdGrove
end Perennial
