/-
`findUpdatedPodsOnNode(ds, podsOnNode, hash)` (`update.go:272`): the node's one updated and one
old live pod (`util.IsPodUpdated`), or `ok = false` if there are two of either. Lean-first; Stage 3,
track B. An old pod is returned only if some live pod lacks the hash label (or the hash is
empty).
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

/-- **`findUpdatedPodsOnNode(ds, pods, hash)`**: see the file header. -/
abbrev findUpdatedPodsOnNode.spec : Prop :=
  ∀ (ds : Loc) (d : kd.apps.DaemonSet) (pl : GoSlice) (dq : DFrac) (ps : List kd.core.Pod)
    (hash : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ □ dsAt ds DFrac.discard d ∗ podsAt pl dq ps }}
    (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.findUpdatedPodsOnNode)) (Val #ds)) (Val #pl)) (Val #hash))
  {{ (np op : Loc) (ok : Bool), RET (PairV (PairV #np #op) #ok); podsAt pl dq ps ∗
      ⌜op ≠ null → hash = [] ∨ ∃ p ∈ ps, p.ObjectMeta'.DeletionTimestamp' = none ∧
        (p.ObjectMeta'.Labels'.getD ∅) !! hashKey ≠ some hash⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
