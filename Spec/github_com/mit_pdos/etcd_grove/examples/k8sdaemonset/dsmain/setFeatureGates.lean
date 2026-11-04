/-
`setFeatureGates()` (`dsmain.go`): `DefaultMutableFeatureGate.SetFromMap({WatchListClient: false,
AtomicFIFO: true, StaleControllerConsistencyDaemonSet: true})`, a panic on an error. Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`).

**Open (gap C7, the run's report).** The post `gatesSet` is persistent, but the gates are
mutable: it holds because no other code of the program sets them. Its proof needs a model of the
gate (`featureGate.SetFromMap`/`Enabled`, names only) with an exclusive right to set it, from the
program's start (as `startRights`' metric names); the proof is a stub until then.
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

/-- **`setFeatureGates()`**: the gates set (`gatesSet`). -/
abbrev setFeatureGates.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.setFeatureGates)) (Val #()))
  {{ RET #(); gatesSet }}

end spec

end dsmain
end EtcdGrove
end Perennial
