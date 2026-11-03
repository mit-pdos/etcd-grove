/-
`util.IsPodUpdated(pod, hash, dsTemplateGeneration)` (`daemonset_util.go`): the pod's hash label
is the (non-empty) hash, or its generation label is the generation's decimal (`podUpdated`).
Lean-first; Stage 3, track B.
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
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.util.Assumptions]

/-- **`IsPodUpdated(p, hash, gen)`**: `podUpdated`; the pod and the pointer come back. -/
abbrev IsPodUpdated.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (d : kd.core.Pod) (hash : GoString) (gp : Loc) (dqg : DFrac)
    (gen : Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.util ∗ podAt p dq d ∗
      int64PtrD gp dqg gen }}
    (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.util.IsPodUpdated)) (Val #p)) (Val #hash)) (Val #gp))
  {{ RET #(podUpdated d.ObjectMeta'.Labels' hash gen); podAt p dq d ∗
      int64PtrD gp dqg gen }}

end spec

end dsctl
end EtcdGrove
end Perennial
