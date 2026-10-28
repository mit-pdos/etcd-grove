/-
**`pkg/api/v1/pod`'s pure model** (the pod helpers the DaemonSet controller calls; phase 5 of
`notes/k8s-daemonset-plan.md`). Lean-first (no Rocq counterpart).

* `condFind cs t`: the first condition of type `t` in `cs`, with its index
  (`GetPodConditionFromList`); `podReadyB cs`: there is a `Ready` condition and the first one's
  status is `True` (`IsPodReadyConditionTrue`); `phaseTerminalB p`: `Failed` or `Succeeded`.
* `ownSliceD_elem_acc`: an element of a deep-owned slice, read through its address.
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

section model
variable [GooseExts]

/-- **The first condition of type `t`**, with its index. -/
def condFind : List kd.core.PodCondition → GoString → Option (Nat × kd.core.PodCondition)
  | [], _ => none
  | c :: cs, t => if c.Type' = t then some (0, c) else (condFind cs t).map (fun p => (p.1 + 1, p.2))

/-- **`IsPodReadyConditionTrue`**: the first `Ready` condition has status `True`. -/
def podReadyB (cs : List kd.core.PodCondition) : Bool :=
  match condFind cs go!"Ready" with
  | some (_, c) => decide (c.Status' = go!"True")
  | none => false

/-- **`IsPodPhaseTerminal`**. -/
def phaseTerminalB (p : GoString) : Bool := decide (p = go!"Failed") || decide (p = go!"Succeeded")

theorem condFind_found (t : GoString) : ∀ (cs : List kd.core.PodCondition) (i : Nat)
    (c : kd.core.PodCondition), (∀ (j : Nat) (c' : kd.core.PodCondition), j < i → cs[j]? = some c' → c'.Type' ≠ t) →
    cs[i]? = some c → c.Type' = t → condFind cs t = some (i, c)
  | [], i, c, _, h, _ => by simp at h
  | c0 :: cs, 0, c, _, h, ht => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [condFind, ht]
  | c0 :: cs, i + 1, c, hbef, h, ht => by
    have h0 : c0.Type' ≠ t := hbef 0 c0 (by omega) rfl
    have := condFind_found t cs i c (fun j c' hj hc => hbef (j + 1) c' (by omega) (by simpa using hc))
      (by simpa using h) ht
    simp [condFind, h0, this]

theorem condFind_none (t : GoString) : ∀ (cs : List kd.core.PodCondition),
    (∀ (j : Nat) (c' : kd.core.PodCondition), cs[j]? = some c' → c'.Type' ≠ t) → condFind cs t = none
  | [], _ => rfl
  | c0 :: cs, h => by
    have h0 : c0.Type' ≠ t := h 0 c0 rfl
    have := condFind_none t cs (fun j c' hc => h (j + 1) c' (by simpa using hc))
    simp [condFind, h0, this]

theorem condFind_lookup (t : GoString) : ∀ (cs : List kd.core.PodCondition) (i : Nat)
    (c : kd.core.PodCondition), condFind cs t = some (i, c) → cs[i]? = some c ∧ c.Type' = t
  | [], _, _, h => by simp [condFind] at h
  | c0 :: cs, i, c, h => by
    unfold condFind at h
    by_cases h0 : c0.Type' = t
    · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, h0⟩
    · simp only [h0, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨⟨j, c'⟩, hj, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := condFind_lookup t cs j c' hj
      simpa using this

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An element of a deep-owned slice**, read through its address `sliceIndexRef V i s`. -/
theorem ownSliceD_elem_acc {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (s : GoSlice) (dq : DFrac) (es : List E) (i : Nat) (e : E)
    (h : es[i]? = some e) :
    ownSliceD inner s dq es ⊢ ∃ v : V, typedPointsto (sliceIndexRef V (i : Int) s) v dq ∗
      inner v dq e ∗ (typedPointsto (sliceIndexRef V (i : Int) s) v dq -∗ inner v dq e -∗
        ownSliceD inner s dq es) := by
  unfold ownSliceD
  iintro ⟨%vs, Hs, Hl⟩
  ihave %hlen := BigSepL2.bigSepL2_length $$ Hl
  have hi : i < vs.length := by
    have := (List.getElem?_eq_some_iff.1 h).1; omega
  obtain ⟨v, hv⟩ : ∃ v, vs[i]? = some v := ⟨vs[i], List.getElem?_eq_getElem hi⟩
  icases BigSepL2.bigSepL2_lookup_acc hv h $$ Hl with ⟨Hi, Hl⟩
  icases ownSlice_elem_acc (i : Int) v s dq vs (by omega) (by simpa using hv) $$ Hs with ⟨Hv, Hs⟩
  iexists v
  iframe Hv Hi
  iintro Hv Hi
  ihave Hs := Hs $$ Hv
  iexists vs
  rw [show (i : Int).toNat = i by omega, list_set_lookup_self vs i v hv]
  iframe Hs
  iapply Hl $$ Hi

/-- **The fields of a deep-owned condition list** that the helpers read: a condition's Go value
has the type, status and transition time of its deep value. -/
def condFieldsEq (v : k8s_io.api.core.v1.PodCondition) (c : kd.core.PodCondition) : Prop :=
  v.Type' = c.Type' ∧ v.Status' = c.Status' ∧ v.LastTransitionTime' = c.LastTransitionTime'

theorem conds_fields : ∀ (dq : DFrac) (vs : List k8s_io.api.core.v1.PodCondition)
    (cs : List kd.core.PodCondition),
    ([∗list] x;e ∈ vs;cs, kd.core.PodCondition.own (GF := GF) x dq e) ⊢
      ⌜List.Forall₂ condFieldsEq vs cs⌝
  | _, [], [] => by iintro -; ipureintro; exact .nil
  | _, [], _ :: _ => by iintro H; ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ H; cases h
  | _, _ :: _, [] => by iintro H; ihave %h := BigSepL2.bigSepL2_nil_inv_right $$ H; cases h
  | dq, x :: vs, e :: cs => by
    iintro ⟨Hx, Hr⟩
    iunfold kd.core.PodCondition.own at Hx
    icases Hx with ⟨%h1, %h2, %h3, %h4, %h5, %h6, %h7⟩
    ihave %h := conds_fields dq vs cs $$ Hr
    ipureintro; exact .cons ⟨h1, h3, h5⟩ h

theorem forall2_lookup {α β : Type} {R : α → β → Prop} : ∀ {l1 : List α} {l2 : List β},
    List.Forall₂ R l1 l2 → ∀ (j : Nat) (a : α) (b : β), l1[j]? = some a → l2[j]? = some b → R a b
  | _, _, .nil, j, a, b, h, _ => by simp at h
  | _, _, .cons hab hr, 0, a, b, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2; subst h1 h2; exact hab
  | _, _, .cons _ hr, j + 1, a, b, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2; exact forall2_lookup hr j a b h1 h2

/-- **A deep-owned pod's conditions**, taken out and put back. -/
theorem pod_conds_acc (v : k8s_io.api.core.v1.Pod) (dq : DFrac) (d : kd.core.Pod) :
    kd.core.Pod.own (GF := GF) v dq d ⊢
      ownSliceD kd.core.PodCondition.own v.Status'.Conditions' dq d.Status'.Conditions' ∗
      (ownSliceD kd.core.PodCondition.own v.Status'.Conditions' dq d.Status'.Conditions' -∗
        kd.core.Pod.own v dq d) := by
  unfold kd.core.Pod.own
  iintro ⟨TypeMeta, ObjectMeta, Spec, Status⟩
  iunfold kd.core.PodStatus.own at Status
  icases Status with ⟨%ObservedGeneration_h, %hp, Conditions, Message, Reason, NominatedNodeName, HostIP, HostIPs, PodIP, PodIPs, StartTime, InitContainerStatuses, ContainerStatuses, QOSClass, EphemeralContainerStatuses, Resize, ResourceClaimStatuses, ExtendedResourceClaimStatus, AllocatedResources, Resources, NodeAllocatableResourceClaimStatuses, VolumeHealth⟩
  iframe Conditions
  iintro Conditions
  iframe
  unfold kd.core.PodStatus.own
  simp only [named]
  iframe
  ipureintro; exact ⟨ObservedGeneration_h, hp⟩

/-- **A deep-owned pod's phase**. -/
theorem pod_phase_eq (v : k8s_io.api.core.v1.Pod) (dq : DFrac) (d : kd.core.Pod) :
    kd.core.Pod.own (GF := GF) v dq d ⊢ kd.core.Pod.own v dq d ∗ ⌜v.Status'.Phase' = d.Status'.Phase'⌝ := by
  unfold kd.core.Pod.own
  iintro ⟨TypeMeta, ObjectMeta, Spec, Status⟩
  iunfold kd.core.PodStatus.own at Status
  icases Status with ⟨ObservedGeneration, %hp, Conditions, Message, Reason, NominatedNodeName, HostIP, HostIPs, PodIP, PodIPs, StartTime, InitContainerStatuses, ContainerStatuses, QOSClass, EphemeralContainerStatuses, Resize, ResourceClaimStatuses, ExtendedResourceClaimStatus, AllocatedResources, Resources, NodeAllocatableResourceClaimStatuses, VolumeHealth⟩
  isplitl
  · iframe
    unfold kd.core.PodStatus.own
    simp only [named]
    iframe
    ipureintro; exact hp
  · ipureintro; exact hp

end lemmas

end dsctl
end EtcdGrove
end Perennial
