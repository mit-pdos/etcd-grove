/-
`check(ctx, admin, uid)` (`dsmain.go`): the pods of `default` listed through the admin
clientset; a panic if two pods controlled by `uid` target one node (`GetTargetNodeName`); the
number of such pods. Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`).

**The spec**: with read access that gives S1 at the state read (`s1Reader`, from the two
invariants), the listed pods are those of a state where S1 holds for `uid` (`podClient.List`'s
answer is the table at the state read, or an error, which `check` turns into `0`): no panic.
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

/-- **`check(ctx, admin, uid)`**: returns (S1: no panic). -/
abbrev check.spec : Prop :=
  ∀ (ctx : GoInterface) (c : Loc) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (uid : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain ∗ ⌜ctx ≠ interface.nil⌝ ∗ clientsetAt c γa cfg true ∗ s1Reader γa }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.check)) (Val #ctx)) (Val #(clientVal c))) (Val #uid))
  {{ (n : w64), RET #n; True }}

end spec

end dsmain
end EtcdGrove
end Perennial
