/-
The proof of `Spec/go_etcd_io/bbolt/node__removeChild.lean`: U8 (`notes/bbolt-proof-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.node__removeChild
public import Proof.go_etcd_io.bbolt.Rebalance.SliceWithin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

theorem not_mem_of_none {α : Type} (l : List α) (x : α) (h : ∀ k < l.length, l[k]? ≠ some x) :
    x ∉ l := by
  intro hm
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hm
  exact h k hk (by rw [List.getElem?_eq_getElem hk, hkx])

theorem erase_of_first {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x : α) (j : Nat)
    (hbefore : ∀ k < j, l[k]? ≠ some x) (hat : l[j]? = some x) :
    l.erase x = l.take j ++ l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hat
  | cons y l ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hat
      subst hat; simp
    | succ j =>
      have hy : y ≠ x := fun h => hbefore 0 (by omega) (by simp [h])
      rw [List.erase_cons_tail (by simpa using hy)]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      congr 1
      exact ih j (fun k hk => by have := hbefore (k + 1) (by omega); simpa using this)
        (by simpa using hat)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.removeChild.wp_proof : node.removeChild.spec (GF := GF) (hG := hG) := by
  intro nl nv cs tl
  wp_start as ⟨Hn, Hs, Hcap⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  wp_auto
  rename_i ip0
  irename : (ip0 ↦ (zero_val w64) : IProp GF) => Hci
  ihave Hn : (nl ↦ nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave IH : iprop(∃ (j : w64),
      "i" ∷ i_ptr ↦ j ∗ "ci" ∷ (∃ v : w64, ip0 ↦ v) ∗ "child" ∷ (∃ c : Loc, child_ptr ↦ c) ∗
      "Hn" ∷ nl ↦ nv ∗ "Hs" ∷ nv.children' ↦* cs ∗ "Hcap" ∷ ownSliceCap Loc nv.children' (DFrac.own 1) ∗
      "n" ∷ n_ptr ↦ nl ∗ "target" ∷ target_ptr ↦ tl ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nv.children'.len ∧
        ∀ k < sint.nat j, cs[k]? ≠ some tl⌝) $$ [i Hci child Hn Hs Hcap n target]
  · iexists W64 0
    iframe
    isplitl [Hci]
    · iexists _; iframe
    isplitl [child]
    · iexists _; iframe
    ipureintro
    exact ⟨by decide, by word, fun k hk => absurd hk (by simp)⟩
  irename : ("_" ∷ True : IProp GF) => Htriv
  iclear Htriv
  wp_for IH
  icases ci with ⟨%cv0, ci⟩
  icases child with ⟨%c0, child⟩
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z nv.children'.len := by simpa using Hif
    clear Hif
    have Hjn : sint.nat j < cs.length := by word
    list_elem cs (sint.nat j) as c
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nv.children'.len
      from ⟨Hj.1, Hlt⟩))]
    wp_apply wp_load_slice_index _ (sint.Z j) cs _ c Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hc_lookup
    try wp_auto
    wp_if_destruct
    · iStructNamed Hn
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z j ∧
        sint.Z j ≤ sint.Z nv.children'.cap from ⟨by decide, Hj.1, by word⟩))]
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (j + W64 1) ∧
        sint.Z (j + W64 1) ≤ sint.Z nv.children'.len ∧ sint.Z nv.children'.len ≤ sint.Z nv.children'.cap
        from ⟨by word, by word, Hcw.2⟩))]
      try wp_auto
      wp_apply wp_slice_append_delete (st := nodes.ty) nv.children' cs j ⟨Hj.1, Hlt⟩ $$ [Hs Hcap]
        as ⟨Hs, Hcap⟩
      · iframe
      try wp_auto
      wp_for_post
      have Hat : cs[sint.nat j]? = some tl := by rw [← Hif]; exact Hc_lookup
      rw [erase_of_first cs tl (sint.nat j) Hj.2.2 Hat]
      iapply HΦ
      iexists _
      iframe
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · wp_for_post
      iframe
      iexists j + W64 1
      iframe
      isplitl [ci]
      · iexists _; iframe
      isplitl [child]
      · iexists _; iframe
      ipureintro
      refine ⟨by word, by word, fun k hk => ?_⟩
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [Hj1] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact Hj.2.2 k hk
      · subst hk; rw [Hc_lookup]; intro h; exact Hif (Option.some.inj h)
  · have Hge : ¬ sint.Z j < sint.Z nv.children'.len := by simpa using Hif
    have Heq : sint.nat j = cs.length := by word
    have Hnm : tl ∉ cs := not_mem_of_none cs tl (fun k hk => Hj.2.2 k (by omega))
    iapply HΦ
    iexists nv.children'
    rw [List.erase_of_not_mem Hnm]
    iframe

end proof

end bbolt
end EtcdGrove
end Perennial
