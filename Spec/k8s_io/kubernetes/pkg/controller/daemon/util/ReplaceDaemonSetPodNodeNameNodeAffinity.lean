/-
`util.ReplaceDaemonSetPodNodeNameNodeAffinity(affinity, nodename)` (`daemon/util/daemonset_util.go:176`):
the affinity that pins a DaemonSet pod to its node. Lean-first; phase 5 of
`notes/k8s-daemonset-plan.md`.

**What the code does** (read 2026-10-28 at the pin): a `nil` affinity gives a new one whose node
affinity requires `metadata.name In [nodename]` (one term, one `MatchFields` requirement); else the
given affinity is changed in place and returned: a missing node affinity is created with that
requirement, a missing required selector set to it, an existing one's terms replaced by that one
term. On deep values this is `dsctl.replAff` (`util/Defs.lean`), and a pod with no node name and
this affinity targets `nodename` (`dsctl.targetNode_replAff`).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.util.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.util.Assumptions]

/-- **`util.ReplaceDaemonSetPodNodeNameNodeAffinity(aff, n)`** of an `*Affinity` owned deeply
(and fully: it may be changed in place) with deep value `da` (`none` for `nil`): an `*Affinity`
owned deeply with deep value `replAff da n`, the given one when it is not `nil`. -/
abbrev ReplaceDaemonSetPodNodeNameNodeAffinity.spec : Prop :=
  ∀ (aff : Loc) (da : Option kd.core.Affinity) (n : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.util ∗
      ownPtrD kd.core.Affinity.own aff (DFrac.own 1) da }}
    (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.util.ReplaceDaemonSetPodNodeNameNodeAffinity))
      (Val #aff)) (Val #n))
  {{ (r : Loc), RET #r; ⌜aff ≠ null → r = aff⌝ ∗
      ownPtrD kd.core.Affinity.own r (DFrac.own 1) (some (replAff da n)) }}

end spec

end dsctl
end EtcdGrove
end Perennial
