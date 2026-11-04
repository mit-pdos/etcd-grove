/-
`(*ControllerRevisionControllerRefManager).ClaimControllerRevisions(ctx, histories)`
(`controller_ref_manager.go:457`): as `ClaimPods`, for revisions (adoption and release through
`PatchControllerRevision`, which the model lacks). Lean-first; Stage 3, track B. Scope: every
revision one `ClaimObject` leaves alone (`crClaimNoop`).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.Defs
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.SelDefs
public import Spec.k8s_io.kubernetes.pkg.controller.NewControllerRevisionControllerRefManager

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

/-- The controller reference of a revision (`GetControllerOfNoCopy`). -/
def crCtlOf (r : kd.apps.ControllerRevision) : Option kd.meta.OwnerReference :=
  r.ObjectMeta'.OwnerReferences'.find? (fun x => decide (x.Controller' = some true))

/-- **A revision `ClaimObject` leaves alone** (as `claimNoop`). -/
def crClaimNoop (d : kd.apps.DaemonSet) (S : Option labels.SelV) (r : kd.apps.ControllerRevision) :
    Prop :=
  match crCtlOf r with
  | some x => x.UID' ≠ d.ObjectMeta'.UID' ∨ labels.selMatch S (r.ObjectMeta'.Labels'.getD ∅)
  | none => d.ObjectMeta'.DeletionTimestamp' ≠ none ∨
      ¬ labels.selMatch S (r.ObjectMeta'.Labels'.getD ∅) ∨ r.ObjectMeta'.DeletionTimestamp' ≠ none ∨
      (d.ObjectMeta'.Namespace' ≠ [] ∧ d.ObjectMeta'.Namespace' ≠ r.ObjectMeta'.Namespace')

/-- **A revision the claim keeps**: controlled by `d`, matching. -/
def crClaimKeeps (d : kd.apps.DaemonSet) (S : Option labels.SelV) (r : kd.apps.ControllerRevision) :
    Prop :=
  ∃ x, crCtlOf r = some x ∧ x.UID' = d.ObjectMeta'.UID' ∧
    labels.selMatch S (r.ObjectMeta'.Labels'.getD ∅)

/-- **`m.ClaimControllerRevisions(ctx, hs)`**: the revisions it keeps; no error. -/
abbrev ControllerRevisionControllerRefManager.ClaimControllerRevisions.spec : Prop :=
  ∀ (m : Loc) (ds : Loc) (d : kd.apps.DaemonSet) (sel : GoInterface) (S : Option labels.SelV)
    (ctx : GoInterface) (hl : GoSlice) (dq : DFrac) (rs : List kd.apps.ControllerRevision),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗
      crRefMgrAt m (interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #ds) sel ∗
      labels.selOk sel S ∗ □ dsAt ds DFrac.discard d ∗ crsAt hl dq rs ∗ ⌜∀ r ∈ rs, crClaimNoop d S r⌝ }}
    (App (App (Val (m @!! go.GoType.PointerType ControllerRevisionControllerRefManager.ty @!!
      go!"ClaimControllerRevisions")) (Val #ctx)) (Val #hl))
  {{ (cl : GoSlice) (err : GoInterface), RET (PairV #cl #err);
      crRefMgrAt m (interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #ds) sel ∗
      crsAt hl dq rs ∗ ⌜err = interface.nil⌝ ∗
      ∃ cs, crsAt cl (DFrac.own 1) cs ∗ ⌜∀ r, r ∈ cs ↔ r ∈ rs ∧ crClaimKeeps d S r⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
