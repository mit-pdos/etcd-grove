/-
**component-helpers' `scheduling/corev1/nodeaffinity`: the predicates of its parsed selectors**
(phase 5 of `notes/k8s-daemonset-plan.md`). Lean-first (no Rocq counterpart).

The selectors the package builds (`labels.Selector`s and `fields.Selector`s, from `labels`' and
`fields`' constructors, names only here) are opaque: what the controller needs of them is that
`Matches` returns.

* `matcherOk T sel`: `sel` is a non-`nil` selector whose `Matches` on a map of type `T`
  (`labels.Set` or `fields.Set`, converted to the `Labels`/`Fields` interface) reads the map and
  returns some `bool` (persistent); `optMatcherOk`: `nil`, or one.
* `termOk t`: a parsed `nodeSelectorTerm` (its selectors, `nil` or `matcherOk`, and its parse
  errors, a read-only slice); `lesOk ns`: a `*LazyErrorNodeSelector` whose terms are; `rnaOk r`: a
  `RequiredNodeAffinity` (its label selector and node selector, each `nil` or as above).
* `nodeFieldsM name`: `extractNodeFields`' map.
* `node_labels_acc`, `node_name_eq`, `node_taints_acc`: a deep-owned node's labels, name, taints.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode
open k8s_io.component_helpers.scheduling.corev1.nodeaffinity

section model
variable [GooseExts]

/-- **`extractNodeFields`' map**: `metadata.name` for a named node. -/
def nodeFieldsM (name : GoString) : GMap GoString GoString :=
  if name = [] then ∅ else {[go!"metadata.name" := name]}

end model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A selector's `Matches` contract** (persistent): on the `Labels`/`Fields` interface of a map
of type `T` (read, possibly `nil`), some `bool`. -/
def matcherOk (T : go.GoType) (sel : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜sel = interface.ok i⌝ ∗
    □ ∀ (m : Loc) (dq : DFrac) (oM : Option (GMap GoString GoString)),
      {{ ownMapD m dq oM }}
        (App (Val #(methods i.ty go!"Matches" i.v)) (Val #(interface.mkOk T #m)))
      {{ (b : Bool), RET #b; ownMapD m dq oM }})

instance matcherOk_persistent (T : go.GoType) (sel : GoInterface) :
    Persistent (matcherOk (GF := GF) T sel) := by
  unfold matcherOk; infer_instance

/-- `nil`, or a selector with `matcherOk`. -/
def optMatcherOk (T : go.GoType) (sel : GoInterface) : IProp GF :=
  iprop(⌜sel = interface.nil⌝ ∨ matcherOk T sel)

instance optMatcherOk_persistent (T : go.GoType) (sel : GoInterface) :
    Persistent (optMatcherOk (GF := GF) T sel) := by
  unfold optMatcherOk; infer_instance

/-- **A parsed node selector term** (persistent). -/
def termOk (t : nodeSelectorTerm) : IProp GF :=
  iprop(optMatcherOk k8s_io.apimachinery.pkg.labels.Set'.ty t.matchLabels' ∗
    optMatcherOk k8s_io.apimachinery.pkg.fields.Set'.ty t.matchFields' ∗
    ∃ es : List GoInterface, t.parseErrs' ↦*□ es)

instance termOk_persistent (t : nodeSelectorTerm) : Persistent (termOk (GF := GF) t) := by
  unfold termOk; infer_instance

/-- **A parsed `*LazyErrorNodeSelector`** (persistent): its terms, read only. -/
def lesOk (ns : Loc) : IProp GF :=
  iprop(∃ (s : GoSlice) (ts : List nodeSelectorTerm), ns ↦□ LazyErrorNodeSelector.mk s ∗
    s ↦*□ ts ∗ [∗list] t ∈ ts, termOk t)

instance lesOk_persistent (ns : Loc) : Persistent (lesOk (GF := GF) ns) := by
  unfold lesOk; infer_instance

/-- **A parsed `RequiredNodeAffinity`** (persistent). -/
def rnaOk (r : RequiredNodeAffinity) : IProp GF :=
  iprop(optMatcherOk k8s_io.apimachinery.pkg.labels.Set'.ty r.labelSelector' ∗
    (⌜r.nodeSelector' = null⌝ ∨ lesOk r.nodeSelector'))

instance rnaOk_persistent (r : RequiredNodeAffinity) : Persistent (rnaOk (GF := GF) r) := by
  unfold rnaOk; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`len` of a map that may be `nil`** (`ownMapD`). -/
theorem wp_ownMapD_len {t : go.GoType} [t ↓u go.MapType go.string go.string] (m : Loc) (dq : DFrac)
    (oM : Option (GMap GoString GoString)) :
    {{ ownMapD (GF := GF) m dq oM }}
      (App (Val #(functions go.len [t])) (Val #m))
    {{ (n : w64), RET #n; ownMapD m dq oM }} := by
  iintro %Φ Hm HΦ
  cases oM with
  | none =>
    iunfold ownMapD at Hm
    icases Hm with %h
    subst h
    rw [show (null : Loc) = map.nil from rfl]
    wp_pures
    iapply HΦ
    iunfold ownMapD
    ipureintro; rfl
  | some M =>
    iunfold ownMapD at Hm
    iapply (wp_map_len (t := t) m M dq) $$ Hm
    inext
    iintro Hm
    iapply HΦ
    iunfold ownMapD
    iexact Hm

/-- **A deep-owned node's labels**, taken out and put back. -/
theorem node_labels_acc (v : k8s_io.api.core.v1.Node) (dq : DFrac) (d : kd.core.Node) :
    kd.core.Node.own (GF := GF) v dq d ⊢
      ownMapD v.ObjectMeta'.Labels' dq d.ObjectMeta'.Labels' ∗
      (ownMapD v.ObjectMeta'.Labels' dq d.ObjectMeta'.Labels' -∗ kd.core.Node.own v dq d) := by
  unfold kd.core.Node.own
  iintro ⟨TypeMeta, ObjectMeta, Spec, Status⟩
  iunfold kd.meta.ObjectMeta.own at ObjectMeta
  icases ObjectMeta with ⟨Name, GenerateName, Namespace, SelfLink, UID, ResourceVersion,
    Generation, CreationTimestamp, DeletionTimestamp, DeletionGracePeriodSeconds, Labels,
    Annotations, OwnerReferences, Finalizers, ManagedFields⟩
  iframe Labels
  iintro Labels
  iframe
  unfold kd.meta.ObjectMeta.own
  simp only [named]
  iframe

/-- **A deep-owned node's name**. -/
theorem node_name_eq (v : k8s_io.api.core.v1.Node) (dq : DFrac) (d : kd.core.Node) :
    kd.core.Node.own (GF := GF) v dq d ⊢ kd.core.Node.own v dq d ∗
      ⌜v.ObjectMeta'.Name' = d.ObjectMeta'.Name'⌝ := by
  unfold kd.core.Node.own
  iintro ⟨TypeMeta, ObjectMeta, Spec, Status⟩
  iunfold kd.meta.ObjectMeta.own at ObjectMeta
  icases ObjectMeta with ⟨%hn, GenerateName, Namespace, SelfLink, UID, ResourceVersion,
    Generation, CreationTimestamp, DeletionTimestamp, DeletionGracePeriodSeconds, Labels,
    Annotations, OwnerReferences, Finalizers, ManagedFields⟩
  isplitl
  · iframe
    unfold kd.meta.ObjectMeta.own
    simp only [named]
    iframe
    ipureintro; exact hn
  · ipureintro; exact hn

/-- **A deep-owned node's taints**, taken out and put back. -/
theorem node_taints_acc (v : k8s_io.api.core.v1.Node) (dq : DFrac) (d : kd.core.Node) :
    kd.core.Node.own (GF := GF) v dq d ⊢
      ownSliceD kd.core.Taint.own v.Spec'.Taints' dq d.Spec'.Taints' ∗
      (ownSliceD kd.core.Taint.own v.Spec'.Taints' dq d.Spec'.Taints' -∗ kd.core.Node.own v dq d) := by
  unfold kd.core.Node.own
  iintro ⟨TypeMeta, ObjectMeta, Spec, Status⟩
  iunfold kd.core.NodeSpec.own at Spec
  icases Spec with ⟨PodCIDR, PodCIDRs, ProviderID, Unschedulable, Taints, ConfigSource,
    DoNotUseExternalID, PodPreemptionPolicy⟩
  iframe Taints
  iintro Taints
  iframe
  unfold kd.core.NodeSpec.own
  simp only [named]
  iframe

end lemmas

end dsctl
end EtcdGrove
end Perennial
