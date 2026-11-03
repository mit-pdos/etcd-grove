/-
`Match(ds, history)` (`update.go:493`): whether the revision's data is the DaemonSet's patch
(`getPatch`, `bytes.Equal`). Lean-first; Stage 3, track B.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`Match(ds, h)`**: whether `getPatchD` of the template is the revision's data; no error. -/
abbrev Match.spec : Prop :=
  ∀ (ds : Loc) (d : kd.apps.DaemonSet) (h : Loc) (r : kd.apps.ControllerRevision),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ □ dsAt ds DFrac.discard d ∗ □ crAt h DFrac.discard r }}
    (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.Match)) (Val #ds)) (Val #h))
  {{ RET (PairV #(decide (r.Data'.Raw' = getPatchD d.Spec'.Template')) #interface.nil); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
