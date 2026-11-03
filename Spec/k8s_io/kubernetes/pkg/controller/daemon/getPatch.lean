/-
`getPatch(ds)` (`update.go:505`): `json.Marshal` of the DaemonSet, `Unmarshal` into a
`map[string]interface{}`, the template under `spec` with `"$patch": "replace"`, `json.Marshal`
again. Lean-first; Stage 3, track B. Its value is `getPatchD` of the template (`Scene.lean`: the
boundary model); the unchecked type assertions hold because a DaemonSet's JSON has a `spec` object
with a `template` object. **Boundary**: `json.Marshal`/`Unmarshal` (names only) are trust-boundary
specs to propose (the run's report); this function's proof rests on them.
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

/-- **`getPatch(ds)`**: a fresh slice of `getPatchD` of the template; no error. -/
abbrev getPatch.spec : Prop :=
  ∀ (ds : Loc) (d : kd.apps.DaemonSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ □ dsAt ds DFrac.discard d }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.getPatch)) (Val #ds))
  {{ (sl : GoSlice), RET (PairV #sl #interface.nil); sl ↦* getPatchD d.Spec'.Template' }}

end spec

end dsctl
end EtcdGrove
end Perennial
