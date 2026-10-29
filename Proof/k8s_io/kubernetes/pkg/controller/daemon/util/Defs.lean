/-
**The DaemonSet controller's `util` package: pure functions and lenses into deep ownership**
(phase 5 of `notes/k8s-daemonset-plan.md`). Lean-first (no Rocq counterpart).

* Lenses: the fields of a pod, a pod spec, an affinity, ... that `GetTargetNodeName`,
  `ReplaceDaemonSetPodNodeNameNodeAffinity`, `AddOrUpdateDaemonPodTolerations`, ... read and write,
  taken out of the deep ownership (`Proof/k8s_io/api/Deep.lean`) with the wand that puts them back.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Model
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode

/-! ## The pure functions -/

section pure
variable [GooseExts]

/-- `(*Toleration).MatchToleration` (`k8s.io/api/core/v1/toleration.go:32`) on deep values: the
same key, effect, operator and value. -/
def tolMatch (t u : kd.core.Toleration) : Bool :=
  decide (t.Key' = u.Key' ∧ t.Effect' = u.Effect' ∧ t.Operator' = u.Operator' ∧ t.Value' = u.Value')

/-- **`v1helper.AddOrUpdateTolerationInPodSpec`** on the deep tolerations: every toleration that
matches `t` is replaced by `t`, and `t` is appended if none matches. -/
def addOrUpdTol (t : kd.core.Toleration) (ts : List kd.core.Toleration) : List kd.core.Toleration :=
  ts.map (fun u => if tolMatch t u then t else u) ++ (if ts.any (tolMatch t) then [] else [t])

/-- The toleration `{Key: k, Operator: Exists, Effect: e}` (`AddOrUpdateDaemonPodTolerations`). -/
def dsTol (k e : GoString) : kd.core.Toleration := ⟨k, go!"Exists", go!"", e, none⟩

/-- **`util.AddOrUpdateDaemonPodTolerations`** on the deep tolerations of a spec whose
`HostNetwork` is `hn`: the not-ready and unreachable `NoExecute` tolerations, the disk-, memory-
and PID-pressure and unschedulable `NoSchedule` ones, and with the host network the
network-unavailable `NoSchedule` one, in this order. -/
def daemonTols (hn : Bool) (ts : List kd.core.Toleration) : List kd.core.Toleration :=
  let ts := addOrUpdTol (dsTol go!"node.kubernetes.io/not-ready" go!"NoExecute") ts
  let ts := addOrUpdTol (dsTol go!"node.kubernetes.io/unreachable" go!"NoExecute") ts
  let ts := addOrUpdTol (dsTol go!"node.kubernetes.io/disk-pressure" go!"NoSchedule") ts
  let ts := addOrUpdTol (dsTol go!"node.kubernetes.io/memory-pressure" go!"NoSchedule") ts
  let ts := addOrUpdTol (dsTol go!"node.kubernetes.io/pid-pressure" go!"NoSchedule") ts
  let ts := addOrUpdTol (dsTol go!"node.kubernetes.io/unschedulable" go!"NoSchedule") ts
  if hn then addOrUpdTol (dsTol go!"node.kubernetes.io/network-unavailable" go!"NoSchedule") ts
  else ts

/-- The requirement `GetTargetNodeName` looks for: key `K`, operator `Op` (`nameReq`'s test). -/
def reqP (K Op : GoString) (e : kd.core.NodeSelectorRequirement) : Bool :=
  decide (e.Key' = K ∧ e.Operator' = Op)

theorem find?_of_prefix {α : Type} (p : α → Bool) : ∀ (l : List α) (j : Nat) (e : α),
    (∀ k < j, ∀ r, l[k]? = some r → p r = false) → l[j]? = some e → p e = true →
    l.find? p = some e
  | [], _, _, _, he, _ => by simp at he
  | x :: l, 0, e, _, he, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he
    subst he; simp [hp]
  | x :: l, j + 1, e, h, he, hp => by
    have hx : p x = false := h 0 (by omega) x rfl
    simp only [List.find?_cons, hx]
    exact find?_of_prefix p l j e (fun k hk r hr => h (k + 1) (by omega) r hr) he hp

theorem find?_none_of_all {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ k < l.length, ∀ r, l[k]? = some r → p r = false) : l.find? p = none := by
  rw [List.find?_eq_none]
  intro x hx
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
  have := h k hk x (by rw [List.getElem?_eq_getElem hk, hkx])
  simp [this]

theorem nameReq_of_prefix (K Op : GoString) : ∀ (ts : List kd.core.NodeSelectorTerm) (i : Nat)
    (t : kd.core.NodeSelectorTerm) (e : kd.core.NodeSelectorRequirement),
    (∀ k < i, ∀ t', ts[k]? = some t' → t'.MatchFields'.find? (reqP K Op) = none) →
    ts[i]? = some t → t.MatchFields'.find? (reqP K Op) = some e → nameReq K Op ts = some e
  | [], _, _, _, _, ht, _ => by simp at ht
  | x :: ts, 0, t, e, _, ht, he => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
    subst ht
    simp only [nameReq]
    unfold reqP at he
    rw [he]
  | x :: ts, i + 1, t, e, h, ht, he => by
    have hx : x.MatchFields'.find? (reqP K Op) = none := h 0 (by omega) x rfl
    simp only [nameReq]
    unfold reqP at hx
    rw [hx]
    exact nameReq_of_prefix K Op ts i t e (fun k hk t' ht' => h (k + 1) (by omega) t' ht') ht he

theorem nameReq_none_of_all (K Op : GoString) : ∀ (ts : List kd.core.NodeSelectorTerm),
    (∀ k < ts.length, ∀ t', ts[k]? = some t' → t'.MatchFields'.find? (reqP K Op) = none) →
    nameReq K Op ts = none
  | [], _ => rfl
  | x :: ts, h => by
    have hx : x.MatchFields'.find? (reqP K Op) = none := h 0 (by simp) x rfl
    simp only [nameReq]
    unfold reqP at hx
    rw [hx]
    exact nameReq_none_of_all K Op ts (fun k hk t' ht' => h (k + 1) (by simp; omega) t' ht')

/-- The node selector `ReplaceDaemonSetPodNodeNameNodeAffinity` puts in: one term, whose only
`MatchFields` requirement is `metadata.name In [n]`. -/
def nameSel (n : GoString) : kd.core.NodeSelector :=
  ⟨[⟨[], [⟨keyName, opIn, [n]⟩]⟩]⟩

/-- **`util.ReplaceDaemonSetPodNodeNameNodeAffinity(affinity, n)`** on the deep value of
`affinity` (`none` for `nil`): its required node affinity replaced by `nameSel n`, the rest kept
(a missing affinity or node affinity is created empty). -/
def replAff (da : Option kd.core.Affinity) (n : GoString) : kd.core.Affinity :=
  let a := da.getD ⟨none, none, none⟩
  let na := a.NodeAffinity'.getD ⟨none, []⟩
  let na' : kd.core.NodeAffinity :=
    { na with RequiredDuringSchedulingIgnoredDuringExecution' := some (nameSel n) }
  { a with NodeAffinity' := some na' }

/-- **A pod with no node name whose affinity is `replAff da n` targets `n`.** -/
theorem targetNode_replAff (d : kd.core.Pod) (da : Option kd.core.Affinity) (n : GoString)
    (hn : d.Spec'.NodeName' = go!"") (ha : d.Spec'.Affinity' = some (replAff da n)) :
    targetNode keyName opIn d = some n := by
  simp [targetNode, reqTerms, hn, ha, replAff, nameSel, nameReq]

/-- `extensions.DaemonSetTemplateGenerationKey`. -/
def genKey : GoString := go!"pod-template-generation"
/-- `extensions.DefaultDaemonSetUniqueLabelKey`. -/
def hashKey : GoString := go!"controller-revision-hash"

/-- **`CreatePodTemplate`'s labels**: the template's (none for `nil`), with the generation's
decimal (`fmt.Sprint`) at `genKey` if there is one, and the hash at `hashKey` if it is not
empty. -/
def tmplLabels (L : Option (GMap GoString GoString)) (g : Option w64) (h : GoString) :
    GMap GoString GoString :=
  let M := L.getD ∅
  let M := match g with
    | some n => <[genKey := _root_.Perennial.fmt.decimal (sint.Z n)]> M
    | none => M
  if h ≠ [] then <[hashKey := h]> M else M

/-- **`util.CreatePodTemplate(template, generation, hash)`** on the deep value of the template:
the labels `tmplLabels`, the tolerations `daemonTols`, the rest kept. -/
def createTmplD (d : kd.core.PodTemplateSpec) (g : Option w64) (h : GoString) :
    kd.core.PodTemplateSpec :=
  ⟨{ d.ObjectMeta' with Labels' := some (tmplLabels d.ObjectMeta'.Labels' g h) },
   { d.Spec' with Tolerations' := daemonTols d.Spec'.HostNetwork' d.Spec'.Tolerations' }⟩

/-- **`util.IsPodUpdated(pod, hash, gen)`** of labels `L` (none for `nil`): the hash label is `h`
(and `h` is not empty), or the generation label is the decimal of `*gen`. -/
def podUpdated (L : Option (GMap GoString GoString)) (h : GoString) (g : Option w64) : Bool :=
  let M := L.getD ∅
  decide (h ≠ [] ∧ (M !! hashKey).getD go!"" = h) ||
    decide (∃ n, g = some n ∧ (M !! genKey).getD go!"" = _root_.Perennial.fmt.decimal (sint.Z n))

/-- **Surge is requested** (`SurgeCount` calls `GetScaledValueFromIntOrPercent`): a rolling
update with a rolling-update configuration whose `MaxSurge` is set. -/
def surgeReq (d : kd.apps.DaemonSet) : Prop :=
  d.Spec'.UpdateStrategy'.Type' = go!"RollingUpdate" ∧
    ∃ r, d.Spec'.UpdateStrategy'.RollingUpdate' = some r ∧ r.MaxSurge' = some ()

/-- **Unavailability is computed** (`UnavailableCount` calls `GetScaledValueFromIntOrPercent`):
a rolling update with a rolling-update configuration. -/
def unavailReq (d : kd.apps.DaemonSet) : Prop :=
  d.Spec'.UpdateStrategy'.Type' = go!"RollingUpdate" ∧
    d.Spec'.UpdateStrategy'.RollingUpdate' ≠ none

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A deep pointer is `nil` exactly for `none`. -/
theorem ptrD_null {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (p : Loc) (dq : DFrac) (e : Option E) :
    ownPtrD inner p dq e ⊢ ownPtrD inner p dq e ∗ ⌜p = null ↔ e = none⌝ := by
  cases e with
  | none =>
    unfold ownPtrD
    iintro %h
    isplitr
    · ipureintro; exact h
    · ipureintro; simp [h]
  | some e =>
    unfold ownPtrD
    iintro ⟨%x, Hp, Hi⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %hnn⟩
    isplitl
    · iexists x
      iframe
    · ipureintro; simp [hnn]

/-- **The fields of a pod `GetTargetNodeName` reads**, out of its points-to at any fraction (a load
through a fractional struct points-to is stuck, `notes/perennial-changes.md`). -/
theorem pod_tnn_acc (p : Loc) (v : k8s_io.api.core.v1.Pod) (dq : DFrac) :
    (p ↦{dq} v : IProp GF) ⊢
      p.[k8s_io.api.core.v1.Pod, go!"Spec"].[k8s_io.api.core.v1.PodSpec, go!"NodeName"] ↦{dq} v.Spec'.NodeName' ∗
      p.[k8s_io.api.core.v1.Pod, go!"Spec"].[k8s_io.api.core.v1.PodSpec, go!"Affinity"] ↦{dq} v.Spec'.Affinity' ∗
      p.[k8s_io.api.core.v1.Pod, go!"ObjectMeta"].[k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta, go!"Namespace"] ↦{dq} v.ObjectMeta'.Namespace' ∗
      p.[k8s_io.api.core.v1.Pod, go!"ObjectMeta"].[k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta, go!"Name"] ↦{dq} v.ObjectMeta'.Name' ∗
      ((p.[k8s_io.api.core.v1.Pod, go!"Spec"].[k8s_io.api.core.v1.PodSpec, go!"NodeName"] ↦{dq} v.Spec'.NodeName' ∗
        p.[k8s_io.api.core.v1.Pod, go!"Spec"].[k8s_io.api.core.v1.PodSpec, go!"Affinity"] ↦{dq} v.Spec'.Affinity' ∗
        p.[k8s_io.api.core.v1.Pod, go!"ObjectMeta"].[k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta, go!"Namespace"] ↦{dq} v.ObjectMeta'.Namespace' ∗
        p.[k8s_io.api.core.v1.Pod, go!"ObjectMeta"].[k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta, go!"Name"] ↦{dq} v.ObjectMeta'.Name') -∗
        p ↦{dq} v) := by
  iintro H
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ H
  iStructNamed H
  ihave %HnnS := typedPointsto_not_null _ _ _ $$ Spec
  ihave %HnnM := typedPointsto_not_null _ _ _ $$ ObjectMeta
  iStructNamedPrefix Spec "s_"
  iStructNamedPrefix ObjectMeta "m_"
  iframe s_NodeName s_Affinity m_Namespace m_Name
  iintro ⟨s_NodeName, s_Affinity, m_Namespace, m_Name⟩
  ihave Spec : (p.[k8s_io.api.core.v1.Pod, go!"Spec"] ↦{dq} v.Spec' : IProp GF) $$ [s_Volumes s_InitContainers s_Containers s_EphemeralContainers s_RestartPolicy s_TerminationGracePeriodSeconds s_ActiveDeadlineSeconds s_DNSPolicy s_NodeSelector s_ServiceAccountName s_DeprecatedServiceAccount s_AutomountServiceAccountToken s_NodeName s_HostNetwork s_HostPID s_HostIPC s_ShareProcessNamespace s_SecurityContext s_ImagePullSecrets s_Hostname s_Subdomain s_Affinity s_SchedulerName s_Tolerations s_HostAliases s_PriorityClassName s_Priority s_DNSConfig s_ReadinessGates s_RuntimeClassName s_EnableServiceLinks s_PreemptionPolicy s_Overhead s_TopologySpreadConstraints s_SetHostnameAsFQDN s_OS s_HostUsers s_SchedulingGates s_ResourceClaims s_Resources s_HostnameOverride s_SchedulingGroup s_EvictionResponders]
  · iapply typedPointsto_combine _ _ _ HnnS
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave ObjectMeta : (p.[k8s_io.api.core.v1.Pod, go!"ObjectMeta"] ↦{dq} v.ObjectMeta' : IProp GF) $$ [m_Name m_GenerateName m_Namespace m_SelfLink m_UID m_ResourceVersion m_Generation m_CreationTimestamp m_DeletionTimestamp m_DeletionGracePeriodSeconds m_Labels m_Annotations m_OwnerReferences m_Finalizers m_ManagedFields]
  · iapply typedPointsto_combine _ _ _ HnnM
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- An affinity's node affinity field, out of its points-to at any fraction. -/
theorem aff_na_acc (a : Loc) (x : k8s_io.api.core.v1.Affinity) (dq : DFrac) :
    (a ↦{dq} x : IProp GF) ⊢ a.[k8s_io.api.core.v1.Affinity, go!"NodeAffinity"] ↦{dq} x.NodeAffinity' ∗
      (a.[k8s_io.api.core.v1.Affinity, go!"NodeAffinity"] ↦{dq} x.NodeAffinity' -∗ a ↦{dq} x) :=
  AccessStrict.access_strict

/-- A node affinity's required selector field, out of its points-to at any fraction. -/
theorem na_req_acc (a : Loc) (x : k8s_io.api.core.v1.NodeAffinity) (dq : DFrac) :
    (a ↦{dq} x : IProp GF) ⊢
      a.[k8s_io.api.core.v1.NodeAffinity, go!"RequiredDuringSchedulingIgnoredDuringExecution"] ↦{dq}
        x.RequiredDuringSchedulingIgnoredDuringExecution' ∗
      (a.[k8s_io.api.core.v1.NodeAffinity, go!"RequiredDuringSchedulingIgnoredDuringExecution"] ↦{dq}
        x.RequiredDuringSchedulingIgnoredDuringExecution' -∗ a ↦{dq} x) :=
  AccessStrict.access_strict

/-- A node selector's terms field, out of its points-to at any fraction. -/
theorem ns_terms_acc (a : Loc) (x : k8s_io.api.core.v1.NodeSelector) (dq : DFrac) :
    (a ↦{dq} x : IProp GF) ⊢
      a.[k8s_io.api.core.v1.NodeSelector, go!"NodeSelectorTerms"] ↦{dq} x.NodeSelectorTerms' ∗
      (a.[k8s_io.api.core.v1.NodeSelector, go!"NodeSelectorTerms"] ↦{dq} x.NodeSelectorTerms' -∗ a ↦{dq} x) :=
  AccessStrict.access_strict

theorem bigSepL2_ownBaseD_eq {V : Type} : ∀ (vs es : List V) (dq : DFrac),
    ([∗list] x;e ∈ vs;es, ownBaseD (GF := GF) x dq e) ⊢ ⌜vs = es⌝
  | [], [], _ => by iintro -; ipureintro; rfl
  | [], _ :: _, _ => by iintro H; ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ H; cases h
  | _ :: _, [], _ => by iintro H; ihave %h := BigSepL2.bigSepL2_nil_inv_right $$ H; cases h
  | x :: vs, e :: es, dq => by
    iintro ⟨Hx, Hr⟩
    ihave %h := bigSepL2_ownBaseD_eq vs es dq $$ Hr
    iunfold ownBaseD at Hx
    icases Hx with %hx
    ipureintro; rw [hx, h]

theorem bigSepL2_ownBaseD_refl {V : Type} : ∀ (vs : List V) (dq : DFrac),
    ⊢ ([∗list] x;e ∈ vs;vs, ownBaseD (GF := GF) x dq e)
  | [], _ => by iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
  | x :: vs, dq => by
    iapply (BigSepL2.bigSepL2_cons (PROP := IProp GF)).2
    isplitr
    · unfold ownBaseD; ipureintro; rfl
    · iapply bigSepL2_ownBaseD_refl

theorem aff_own_na(x : k8s_io.api.core.v1.Affinity) (dq : DFrac) (a : kd.core.Affinity) :
    kd.core.Affinity.own (GF := GF) x dq a ⊢ ownPtrD kd.core.NodeAffinity.own x.NodeAffinity' dq a.NodeAffinity' ∗
      (ownPtrD kd.core.NodeAffinity.own x.NodeAffinity' dq a.NodeAffinity' -∗ kd.core.Affinity.own x dq a) := by
  unfold kd.core.Affinity.own
  iintro ⟨H1, H2, H3⟩
  iframe H1
  iintro H1
  simp only [named]
  iframe

theorem na_own_req (x : k8s_io.api.core.v1.NodeAffinity) (dq : DFrac) (a : kd.core.NodeAffinity) :
    kd.core.NodeAffinity.own (GF := GF) x dq a ⊢
      ownPtrD kd.core.NodeSelector.own x.RequiredDuringSchedulingIgnoredDuringExecution' dq
        a.RequiredDuringSchedulingIgnoredDuringExecution' ∗
      (ownPtrD kd.core.NodeSelector.own x.RequiredDuringSchedulingIgnoredDuringExecution' dq
        a.RequiredDuringSchedulingIgnoredDuringExecution' -∗ kd.core.NodeAffinity.own x dq a) := by
  unfold kd.core.NodeAffinity.own
  iintro ⟨H1, H2⟩
  iframe H1
  iintro H1
  simp only [named]
  iframe

/-- An affinity's node affinity, to be replaced. -/
theorem aff_own_na_set (x : k8s_io.api.core.v1.Affinity) (dq : DFrac) (a : kd.core.Affinity) :
    kd.core.Affinity.own (GF := GF) x dq a ⊢ ownPtrD kd.core.NodeAffinity.own x.NodeAffinity' dq a.NodeAffinity' ∗
      (∀ p e, ownPtrD kd.core.NodeAffinity.own p dq e -∗
        kd.core.Affinity.own { x with NodeAffinity' := p } dq { a with NodeAffinity' := e }) := by
  unfold kd.core.Affinity.own
  iintro ⟨H1, H2, H3⟩
  iframe H1
  iintro %p %e H1
  simp only [named]
  iframe

/-- A node affinity's required selector, to be replaced. -/
theorem na_own_req_set (x : k8s_io.api.core.v1.NodeAffinity) (dq : DFrac) (a : kd.core.NodeAffinity) :
    kd.core.NodeAffinity.own (GF := GF) x dq a ⊢
      ownPtrD kd.core.NodeSelector.own x.RequiredDuringSchedulingIgnoredDuringExecution' dq
        a.RequiredDuringSchedulingIgnoredDuringExecution' ∗
      (∀ p e, ownPtrD kd.core.NodeSelector.own p dq e -∗
        kd.core.NodeAffinity.own { x with RequiredDuringSchedulingIgnoredDuringExecution' := p } dq
          { a with RequiredDuringSchedulingIgnoredDuringExecution' := e }) := by
  unfold kd.core.NodeAffinity.own
  iintro ⟨H1, H2⟩
  iframe H1
  iintro %p %e H1
  simp only [named]
  iframe

theorem ns_own_terms (x : k8s_io.api.core.v1.NodeSelector) (dq : DFrac) (a : kd.core.NodeSelector) :
    kd.core.NodeSelector.own (GF := GF) x dq a ⊣⊢
      ownSliceD kd.core.NodeSelectorTerm.own x.NodeSelectorTerms' dq a.NodeSelectorTerms' := by
  unfold kd.core.NodeSelector.own
  simp only [named]
  exact .rfl

theorem term_own_fields (x : k8s_io.api.core.v1.NodeSelectorTerm) (dq : DFrac) (a : kd.core.NodeSelectorTerm) :
    kd.core.NodeSelectorTerm.own (GF := GF) x dq a ⊢
      ownSliceD kd.core.NodeSelectorRequirement.own x.MatchFields' dq a.MatchFields' ∗
      (ownSliceD kd.core.NodeSelectorRequirement.own x.MatchFields' dq a.MatchFields' -∗
        kd.core.NodeSelectorTerm.own x dq a) := by
  unfold kd.core.NodeSelectorTerm.own
  iintro ⟨H1, H2⟩
  iframe H2
  iintro H2
  simp only [named]
  iframe

/-- A requirement's key, operator, and values (a slice of the deep values). -/
theorem req_own (x : k8s_io.api.core.v1.NodeSelectorRequirement) (dq : DFrac)
    (a : kd.core.NodeSelectorRequirement) :
    kd.core.NodeSelectorRequirement.own (GF := GF) x dq a ⊣⊢
      ⌜x.Key' = a.Key' ∧ x.Operator' = a.Operator'⌝ ∗ x.Values' ↦*{dq} a.Values' := by
  unfold kd.core.NodeSelectorRequirement.own ownSliceD
  simp only [named]
  constructor
  · iintro ⟨%h1, %h2, %vs, Hs, Hl⟩
    ihave %h := (bigSepL2_ownBaseD_eq (GF := GF) vs a.Values' dq) $$ Hl
    subst h
    iframe
    ipureintro; exact ⟨h1, h2⟩
  · iintro ⟨⟨%h1, %h2⟩, Hs⟩
    isplitr
    · ipureintro; exact h1
    isplitr
    · ipureintro; exact h2
    iexists a.Values'
    iframe
    iapply bigSepL2_ownBaseD_refl

/-- **The node selector `ReplaceDaemonSetPodNodeNameNodeAffinity` builds** owns `nameSel n`: a
one-term slice whose term's `MatchFields` is a one-requirement slice whose values are `[n]`. -/
theorem nameSel_terms_own (n : GoString) (sv mfs tss : GoSlice)
    (rq : k8s_io.api.core.v1.NodeSelectorRequirement) (tm : k8s_io.api.core.v1.NodeSelectorTerm) :
    (sv ↦* [n] ∗ mfs ↦* [rq] ∗ tss ↦* [tm] ∗
      ⌜rq.Key' = keyName ∧ rq.Operator' = opIn ∧ rq.Values' = sv ∧
        tm.MatchExpressions' = slice.nil ∧ tm.MatchFields' = mfs⌝ : IProp GF) ⊢
      ownSliceD kd.core.NodeSelectorTerm.own tss (DFrac.own 1) (nameSel n).NodeSelectorTerms' := by
  iintro ⟨Hsv, Hmf, Hts, %h⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold nameSel ownSliceD
  iexists [tm]
  iframe Hts
  iapply (BigSepL2.bigSepL2_cons (PROP := IProp GF)).2
  isplitl
  · unfold kd.core.NodeSelectorTerm.own
    simp only [named]
    isplitr
    · rw [h4]; iapply ownSliceD_nil_of; rfl
    rw [h5]
    unfold ownSliceD
    iexists [rq]
    iframe Hmf
    iapply (BigSepL2.bigSepL2_cons (PROP := IProp GF)).2
    isplitl
    · iapply (req_own _ _ _).2
      rw [h3]
      iframe
      ipureintro; exact ⟨h1, h2⟩
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
  · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro

/-- A pod's spec. -/
theorem pod_spec_acc (v : k8s_io.api.core.v1.Pod) (dq : DFrac) (d : kd.core.Pod) :
    kd.core.Pod.own (GF := GF) v dq d ⊢ kd.core.PodSpec.own v.Spec' dq d.Spec' ∗
      (kd.core.PodSpec.own v.Spec' dq d.Spec' -∗ kd.core.Pod.own v dq d) := by
  unfold kd.core.Pod.own
  iintro ⟨TypeMeta, ObjectMeta, Spec, Status⟩
  iframe Spec
  iintro Spec
  simp only [named]
  iframe

/-- A pod's metadata fields `GetTargetNodeName`'s errors read. -/
theorem pod_meta (v : k8s_io.api.core.v1.Pod) (dq : DFrac) (d : kd.core.Pod) :
    kd.core.Pod.own (GF := GF) v dq d ⊢ kd.core.Pod.own v dq d ∗
      ⌜v.ObjectMeta'.Name' = d.ObjectMeta'.Name' ∧ v.ObjectMeta'.Namespace' = d.ObjectMeta'.Namespace'⌝ := by
  unfold kd.core.Pod.own kd.meta.ObjectMeta.own
  iintro ⟨TypeMeta, ⟨%h1, GenerateName, %h3, ObjectMetaRest⟩, Spec, Status⟩
  isplitl
  · simp only [named]
    iframe
    ipureintro; exact ⟨h1, h3⟩
  · ipureintro; exact ⟨h1, h3⟩

/-- A pod spec's node name and affinity. -/
theorem podSpec_aff_acc (v : k8s_io.api.core.v1.PodSpec) (dq : DFrac) (d : kd.core.PodSpec) :
    kd.core.PodSpec.own (GF := GF) v dq d ⊢ ⌜v.NodeName' = d.NodeName'⌝ ∗
      ownPtrD kd.core.Affinity.own v.Affinity' dq d.Affinity' ∗
      (ownPtrD kd.core.Affinity.own v.Affinity' dq d.Affinity' -∗ kd.core.PodSpec.own v dq d) := by
  unfold kd.core.PodSpec.own
  iintro ⟨Volumes, InitContainers, Containers, EphemeralContainers, RestartPolicy, TerminationGracePeriodSeconds, ActiveDeadlineSeconds, DNSPolicy, NodeSelector, ServiceAccountName, DeprecatedServiceAccount, AutomountServiceAccountToken, %hn, HostNetwork, HostPID, HostIPC, ShareProcessNamespace, SecurityContext, ImagePullSecrets, Hostname, Subdomain, Affinity, SchedulerName, Tolerations, HostAliases, PriorityClassName, Priority, DNSConfig, ReadinessGates, RuntimeClassName, EnableServiceLinks, PreemptionPolicy, Overhead, TopologySpreadConstraints, SetHostnameAsFQDN, OS, HostUsers, SchedulingGates, ResourceClaims, Resources, HostnameOverride, SchedulingGroup, EvictionResponders⟩
  isplitr
  · ipureintro; exact hn
  iframe Affinity
  iintro Affinity
  simp only [named]
  iframe
  ipureintro; exact hn

end lemmas

end dsctl
end EtcdGrove
end Perennial
