/-
`(*PodControllerRefManager).ClaimPods(ctx, pods, filters...)` (`controller_ref_manager.go:183`):
for each pod, `ClaimObject` (keep a matching pod the controller controls; adopt a matching orphan,
`PatchPod`; release a non-matching controlled pod, `PatchPod`), the kept ones and the errors
aggregated. Lean-first; Stage 3, track B.

Scope: no filter, and every pod one `ClaimObject` leaves alone (`claimNoop`): the model has no pod
`Patch` (adoption and release would panic), and `sceneOk` (no orphans, every controlled pod
matching) makes every pod of the DaemonSet controller's claims such a pod. The result: the pods it
keeps (`claimKeeps`), no error.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.Defs
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.SelDefs
public import Spec.k8s_io.kubernetes.pkg.controller.NewPodControllerRefManager

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel k8s_io.kubernetes.pkg.controller

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

/-- **A pod `ClaimObject` leaves alone** (no adoption, no release) for the DaemonSet `d` with
selector value `S`: controlled by another UID, or by `d` and matching; or an orphan it does not
adopt (`d` being deleted, not matching, the pod being deleted, or another namespace). -/
def claimNoop (d : kd.apps.DaemonSet) (S : Option labels.SelV) (p : kd.core.Pod) : Prop :=
  match ctlOf p with
  | some r => r.UID' ≠ d.ObjectMeta'.UID' ∨ labels.selMatch S (p.ObjectMeta'.Labels'.getD ∅)
  | none => d.ObjectMeta'.DeletionTimestamp' ≠ none ∨
      ¬ labels.selMatch S (p.ObjectMeta'.Labels'.getD ∅) ∨ p.ObjectMeta'.DeletionTimestamp' ≠ none ∨
      (d.ObjectMeta'.Namespace' ≠ [] ∧ d.ObjectMeta'.Namespace' ≠ p.ObjectMeta'.Namespace')

/-- **A pod the claim keeps**: controlled by `d`, matching. -/
def claimKeeps (d : kd.apps.DaemonSet) (S : Option labels.SelV) (p : kd.core.Pod) : Prop :=
  ∃ r, ctlOf p = some r ∧ r.UID' = d.ObjectMeta'.UID' ∧
    labels.selMatch S (p.ObjectMeta'.Labels'.getD ∅)

/-- **`m.ClaimPods(ctx, pods)`**: see the file header. -/
abbrev PodControllerRefManager.ClaimPods.spec : Prop :=
  ∀ (m : Loc) (ds : Loc) (d : kd.apps.DaemonSet) (sel : GoInterface) (S : Option labels.SelV)
    (ctx : GoInterface) (pl : GoSlice) (dq : DFrac) (ps : List kd.core.Pod),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗
      podRefMgrAt m (interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #ds) sel ∗
      labels.selOk sel S ∗ □ dsAt ds DFrac.discard d ∗ podsAt pl dq ps ∗ ⌜∀ p ∈ ps, claimNoop d S p⌝ }}
    (App (App (App (Val (m @!! go.GoType.PointerType PodControllerRefManager.ty @!! go!"ClaimPods"))
      (Val #ctx)) (Val #pl)) (Val #slice.nil))
  {{ (cl : GoSlice) (err : GoInterface), RET (PairV #cl #err);
      podRefMgrAt m (interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #ds) sel ∗
      podsAt pl dq ps ∗ ⌜err = interface.nil⌝ ∗
      ∃ cs, podsAt cl (DFrac.own 1) cs ∗ ⌜∀ p, p ∈ cs ↔ p ∈ ps ∧ claimKeeps d S p⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
