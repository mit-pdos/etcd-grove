/-
**Lenses into a pod's deep ownership** for the pod control (`RealPodControl.createPods` reads the
pod's labels). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.ClientLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.ObjLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel

/-- **A pod create's object is a pod, written.** -/
theorem CreateOut_ok_pod [GooseExts] {cfgFail admin : Bool} {ns : GoString} {d : kd.core.Pod}
    {σ σ' : St} {w : Bool} {o : Obj}
    (h : CreateOut cfgFail admin .pods ns (.pod d) σ (.ok (w, o)) σ') :
    w = true ∧ ∃ dp, o = .pod dp := by
  have hres := CreateOut_ok_res h
  rcases h with ⟨-, h, -⟩ | ⟨e, -, h, -⟩ | ⟨-, t, -, h⟩
  · cases h
  · cases h
  · cases h
    refine ⟨rfl, ?_⟩
    cases ho : (createApply Res.pods ns (Obj.pod d) σ t).1 with
    | pod dp => exact ⟨dp, rfl⟩
    | node _ => rw [ho] at hres; cases hres
    | ds _ => rw [ho] at hres; cases hres
    | cr _ => rw [ho] at hres; cases hres

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [core_sem : k8s_io.api.core.v1.Assumptions]
variable [meta_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

/-- **A pod's labels map**, read off its deep ownership, and put back. -/
theorem podAt_labels (p : Loc) (dq : DFrac) (d : kd.core.Pod) :
    podAt (GF := GF) p dq d ⊢ ∃ m : GoMap,
      p.[k8s_io.api.core.v1.Pod, go!"ObjectMeta"].[k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta,
        go!"Labels"] ↦{dq} m ∗
      ownMapD (GF := GF) (K := GoString) (V := GoString) m dq d.ObjectMeta'.Labels' ∗
      (p.[k8s_io.api.core.v1.Pod, go!"ObjectMeta"].[k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta,
          go!"Labels"] ↦{dq} m -∗
        ownMapD (GF := GF) (K := GoString) (V := GoString) m dq d.ObjectMeta'.Labels' -∗
        podAt p dq d) := by
  unfold podAt
  iintro ⟨%v, Hl, Hd⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  icases typedPointsto_not_null_dup _ _ _ $$ ObjectMeta with ⟨ObjectMeta, %Hnn2⟩
  iStructNamedPrefix ObjectMeta "M"
  iunfold kd.core.Pod.own at Hd
  icases Hd with ⟨DTypeMeta, DObjectMeta, DSpec, DStatus⟩
  iunfold kd.meta.ObjectMeta.own at DObjectMeta
  icases DObjectMeta with ⟨DName, DGenerateName, DNamespace, DSelfLink, DUID, DResourceVersion,
    DGeneration, DCreationTimestamp, DDeletionTimestamp, DDeletionGracePeriodSeconds, DLabels,
    DAnnotations, DOwnerReferences, DFinalizers, DManagedFields⟩
  iexists v.ObjectMeta'.Labels'
  iframe MLabels DLabels
  iintro MLabels DLabels
  iexists v
  isplitl [TypeMeta MName MGenerateName MNamespace MSelfLink MUID MResourceVersion MGeneration
    MCreationTimestamp MDeletionTimestamp MDeletionGracePeriodSeconds MLabels MAnnotations
    MOwnerReferences MFinalizers MManagedFields Spec Status]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
    iapply typedPointsto_combine _ _ _ Hnn2
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · unfold kd.core.Pod.own kd.meta.ObjectMeta.own
    simp only [named]
    iframe

/-- **A pod's name field**, read off its deep ownership, and put back. -/
theorem podAt_name (p : Loc) (dq : DFrac) (d : kd.core.Pod) :
    podAt (GF := GF) p dq d ⊢
      p.[k8s_io.api.core.v1.Pod, go!"ObjectMeta"].[k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta,
        go!"Name"] ↦{dq} d.ObjectMeta'.Name' ∗
      (p.[k8s_io.api.core.v1.Pod, go!"ObjectMeta"].[k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta,
          go!"Name"] ↦{dq} d.ObjectMeta'.Name' -∗ podAt p dq d) := by
  unfold podAt
  iintro ⟨%v, Hl, Hd⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  icases typedPointsto_not_null_dup _ _ _ $$ ObjectMeta with ⟨ObjectMeta, %Hnn2⟩
  iStructNamedPrefix ObjectMeta "M"
  iunfold kd.core.Pod.own at Hd
  icases Hd with ⟨DTypeMeta, DObjectMeta, DSpec, DStatus⟩
  iunfold kd.meta.ObjectMeta.own at DObjectMeta
  icases DObjectMeta with ⟨%hname, DGenerateName, DNamespace, DSelfLink, DUID, DResourceVersion,
    DGeneration, DCreationTimestamp, DDeletionTimestamp, DDeletionGracePeriodSeconds, DLabels,
    DAnnotations, DOwnerReferences, DFinalizers, DManagedFields⟩
  rw [← hname]
  iframe MName
  iintro MName
  iexists v
  isplitl [TypeMeta MName MGenerateName MNamespace MSelfLink MUID MResourceVersion MGeneration
    MCreationTimestamp MDeletionTimestamp MDeletionGracePeriodSeconds MLabels MAnnotations
    MOwnerReferences MFinalizers MManagedFields Spec Status]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
    iapply typedPointsto_combine _ _ _ Hnn2
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · unfold kd.core.Pod.own kd.meta.ObjectMeta.own
    simp only [named]
    iframe
    ipureintro; exact hname

/-- **`GetName()` on a DaemonSet held at any fraction**, through its `metav1.Object` interface
value: the name, the DaemonSet back. -/
theorem dsAt_GetName (hget : metav1.ObjectMeta.GetName.spec (GF := GF) (hG := hG))
    [apps_sem : k8s_io.api.apps.v1.Assumptions] (l : Loc) (dq : DFrac) (dd : kd.apps.DaemonSet) :
    {{ dsAt (GF := GF) l dq dd }}
      (App (Val #(methods (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) go!"GetName" #l))
        (Val #()))
    {{ RET #dd.ObjectMeta'.Name'; dsAt l dq dd }} := by
  wp_start as Ho
  simp only [dsAt]
  icases Ho with ⟨%v, Hl, Hd⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  icases kd.apps.DaemonSet.own_meta _ _ _ $$ Hd with ⟨Hm, Hback⟩
  ihave %Hb := meta_own_base _ _ _ $$ Hm
  wp_apply (hget _ v.ObjectMeta' dq) $$ [ObjectMeta] as ObjectMeta
  · iexact ObjectMeta
  ihave Hd := Hback $$ %v.ObjectMeta' %dd.ObjectMeta' [Hm]
  · iexact Hm
  rw [Hb.1]
  iapply HΦ
  iexists v
  iframe Hd
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- A map field with no deep map is `nil`. -/
theorem ownMapD_none {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : GoMap) (dq : DFrac) (L : Option (GMap K V)) (h : L = none) :
    ownMapD (GF := GF) m dq L ⊢ ⌜m = map.nil⌝ := by
  subst h
  unfold ownMapD
  iintro %h
  ipureintro
  exact h

/-- A map field with a deep map owns it. -/
theorem ownMapD_some {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : GoMap) (dq : DFrac) (L : Option (GMap K V)) (M : GMap K V) (h : L = some M) :
    ownMapD (GF := GF) m dq L ⊣⊢ m ↦${dq} M := by
  subst h
  unfold ownMapD
  exact .rfl

end lemmas

end dsctl
end EtcdGrove
end Perennial
