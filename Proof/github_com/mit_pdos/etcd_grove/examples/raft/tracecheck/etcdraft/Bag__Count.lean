/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__Count`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Count
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__find

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Bag.Count.wp_proof (wp_find : Bag.find.spec (GF := GF) (hG := hG)) :
    Bag.Count.spec (GF := GF) (hG := hG) := by
  intro g b p m
  wp_start as ⟨#Hg, #Hm⟩
  ihave #Hg0 := Hg
  iunfold bagRO at Hg0
  icases Hg0 with ⟨%items, #Hits, #Hib⟩
  ihave %Hil := ownSlice_len $$ Hits
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hib
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_find_unfold.method_unfold]
  try wp_auto
  wp_apply wp_find g b p m $$ [Hg Hm] as %k %Hk
  · iframe Hg Hm
  try wp_auto
  have hfind := List.find?_eq_bind_findIdx?_getElem? (xs := b) (p := fun it => it.1 == m)
  cases hf : b.findIdx? (fun it => it.1 == m) with
  | none =>
    rw [hf] at Hk
    simp only at Hk
    rw [decide_eq_false (show ¬ sint.Z (W64 0) ≤ sint.Z k by rw [Hk]; decide)]
    try wp_auto
    have : b.count m = 0 := by
      unfold Bag.count; rw [hfind, hf]; rfl
    rw [this]
    iapply HΦ; ipureintro; rfl
  | some i =>
    rw [hf] at Hk
    simp only at Hk
    have hi : i < b.length := ((List.findIdx?_eq_some_iff_getElem).1 hf).1
    obtain ⟨x, Hx⟩ : ∃ x, b[i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨y, Hy⟩ : ∃ y, items[i]? = some y := ⟨_, List.getElem?_eq_getElem (Hbl ▸ hi)⟩
    ihave ⟨-, %Hyc⟩ := BigSepL2.bigSepL2_lookup
      (Φ := fun _ it p => iprop(msgRO (GF := GF) it.msg' p.1 ∗ ⌜sint.Z it.count' = (p.2 : Int)⌝)) Hy Hx $$ Hib
    have hk0 : 0 ≤ sint.Z k := by rw [Hk]; exact Int.natCast_nonneg _
    rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z k from hk0)]
    try wp_auto
    have hkl : sint.Z k < sint.Z g.items'.len := by
      have : (i : Int) < items.length := by rw [Hbl]; exact_mod_cast hi
      rw [Hil.1] at this; rw [Hk]; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z g.items'.len from ⟨hk0, hkl⟩))]
    have hki : (sint.Z k).toNat = i := by rw [Hk]; simp
    icases ownSlice_elem_acc _ y _ _ items hk0 (by rw [hki]; exact Hy) $$ Hits with ⟨Hy', -⟩
    icases typedPointsto_split _ _ _ $$ Hy' with Hyf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hyf
    wp_auto
    iapply HΦ; ipureintro
    rw [Hyc]
    unfold Bag.count; rw [hfind, hf]; simp [Hx]

end proof

end Etcdraft
end EtcdGrove
end Perennial
