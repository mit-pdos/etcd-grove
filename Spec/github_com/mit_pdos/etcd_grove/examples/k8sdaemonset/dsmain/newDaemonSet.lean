/-
`newDaemonSet()` (`dsmain.go`): the scenario's DaemonSet `default/ds-1`, its template defaulted. Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`).
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

/-- **`newDaemonSet()`**: a fresh DaemonSet (`newDsOk`). -/
abbrev newDaemonSet.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.newDaemonSet)) (Val #()))
  {{ (p : Loc), RET #p;
      ∃ d : kd.apps.DaemonSet, objPtrAt p (DFrac.own 1) (.ds d) ∗ ⌜newDsOk d⌝ }}

end spec

end dsmain
end EtcdGrove
end Perennial
