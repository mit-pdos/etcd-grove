/-
`(*DaemonSetsController).resolveControllerRef(namespace, controllerRef)`
(`daemon_controller.go:827`): the DaemonSet the reference names, from the lister, if its kind is
`DaemonSet` and its UID the reference's; else `nil`. Lean-first; track C.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.LifeDefs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel informer informers cache workqueue k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`dsc.resolveControllerRef(ns, ref)`**: `nil`, or a cached version of the DaemonSet at `(ns, ref.Name)` with the reference's UID. -/
abbrev DaemonSetsController.resolveControllerRef.spec : Prop :=
  ∀  (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (ns : GoString) (cref : Loc) (r : kd.meta.OwnerReference),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ isDsc dsc c cfg γa F ∗ threadTok ∗ refAt cref r }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"resolveControllerRef")) (Val #ns)) (Val #cref))
  {{ (ds : Loc), RET #ds; threadTok ∗
      (⌜ds = null⌝ ∨ ∃ d : kd.apps.DaemonSet, □ dsAt ds DFrac.discard d ∗
        dsSeen γa ⟨ns, r.Name'⟩ d ∗ ⌜d.ObjectMeta'.UID' = r.UID'⌝) }}

end spec

end dsctl
end EtcdGrove
end Perennial
