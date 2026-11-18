/- Lean-first (no Rocq counterpart). Lemmas of `candsElems` (the candidate slices' elements). -/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem candsElems_length (vs : List cand) (cs : List TCand) :
    candsElems (GF := GF) vs cs ⊢ ⌜vs.length = cs.length⌝ := by
  unfold candsElems
  iintro ⟨%hl, -⟩; ipureintro; exact hl

theorem candsElems_lookup (vs : List cand) (cs : List TCand) (i : Nat) (v : cand)
    (hv : vs[i]? = some v) :
    candsElems (GF := GF) vs cs ⊢ ∃ c, ⌜cs[i]? = some c⌝ ∗ candRep v c := by
  unfold candsElems
  iintro ⟨%hl, #Hall⟩
  have hi : i < cs.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hv).1
  iexists cs[i]
  isplitr
  · ipureintro; exact List.getElem?_eq_getElem hi
  iapply Hall
  ipureintro; exact ⟨hv, List.getElem?_eq_getElem hi⟩

theorem candsElems_snoc (vs : List cand) (cs : List TCand) (v : cand) (c : TCand) :
    candsElems (GF := GF) vs cs ∗ candRep v c ⊢ candsElems (vs ++ [v]) (cs ++ [c]) := by
  unfold candsElems
  iintro ⟨⟨%hl, #Hall⟩, #Ho⟩
  isplitr
  · ipureintro; simp [hl]
  imodintro
  iintro %i %v' %o' %hi
  obtain ⟨h1, h2⟩ := hi
  by_cases hlt : i < vs.length
  · rw [List.getElem?_append_left hlt] at h1
    rw [List.getElem?_append_left (by omega)] at h2
    iapply Hall; ipureintro; exact ⟨h1, h2⟩
  · rw [List.getElem?_append_right (by omega)] at h1
    rw [List.getElem?_append_right (by omega)] at h2
    have : i - vs.length = 0 := by
      have := (List.getElem?_eq_some_iff.1 h1).1; simp at this; omega
    rw [this] at h1
    rw [show i - cs.length = 0 by omega] at h2
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    iexact Ho

theorem candsElems_set (vs : List cand) (cs : List TCand) (j : Nat) (v : cand) (c : TCand) :
    candsElems (GF := GF) vs cs ∗ candRep v c ⊢ candsElems (vs.set j v) (cs.set j c) := by
  unfold candsElems
  iintro ⟨⟨%hl, #Hall⟩, #Ho⟩
  isplitr
  · ipureintro; simp [hl]
  imodintro
  iintro %i %v' %o' %hi
  obtain ⟨h1, h2⟩ := hi
  rw [List.getElem?_set] at h1 h2
  by_cases hij : j = i
  · subst hij
    simp only [if_true] at h1 h2
    by_cases hjl : j < vs.length
    · have hjl' : j < cs.length := by omega
      simp only [hjl, hjl', if_true, Option.some.injEq] at h1 h2
      subst h1 h2
      iexact Ho
    · simp only [hjl, if_false] at h1; cases h1
  · simp only [hij, if_false] at h1 h2
    iapply Hall; ipureintro; exact ⟨h1, h2⟩

/-- Reading an element of an owned slice: its points-to, and the slice back from it unchanged. -/
theorem ownSlice_elem_read_cand
    (i : Int) (v : cand) (s : GoSlice) (vs : List cand) (hpos : 0 ≤ i) (hlookup : vs[i.toNat]? = some v) :
    (s ↦* vs : IProp GF) ⊢
      typedPointsto (sliceIndexRef cand i s) v (DFrac.own 1) ∗
      (typedPointsto (sliceIndexRef cand i s) v (DFrac.own 1) -∗ s ↦* vs) := by
  iintro Hs
  icases ownSlice_elem_acc i v s (DFrac.own 1) vs hpos hlookup $$ Hs with ⟨Hv, Hb⟩
  iframe
  iintro Hv
  have hset : vs.set i.toNat v = vs := by
    apply List.ext_getElem?
    intro n
    rw [List.getElem?_set]
    split
    · rename_i hn; subst hn
      rw [if_pos (List.getElem?_eq_some_iff.1 hlookup).1]; exact hlookup.symm
    · rfl
  ihave H := Hb $$ Hv
  rw [hset]
  iexact H

end lemmas

end etcd_wal
end EtcdGrove
end Perennial
