/-
**Helpers for `fieldpath`'s sorted sets and maps of path elements** (`PathElementSet`,
`PathElementMap`, `PathElementValueMap`): sorted lists of well-formed elements, their merges, and
the representation's reading.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
public import Perennial.Proof.sort.FindBasics
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace fpA

/-- All elements well-formed. -/
abbrev AllWf (xs : List PE) : Prop := ∀ x ∈ xs, x.wf = true

theorem cmp_self (x : PE) (hx : x.wf = true) : PE.compare x x = 0 :=
  (PE_compare_eq_zero_law_holds x x hx hx).2 rfl

theorem lt_irrefl (x : PE) (hx : x.wf = true) : ¬ PE.lt x x := by
  unfold PE.lt; rw [cmp_self x hx]; decide

theorem sorted_nodup (xs : List PE) (hw : AllWf xs) (hs : PE.Sorted xs) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    unfold PE.Sorted at hs
    rw [List.pairwise_cons] at hs
    refine List.nodup_cons.2 ⟨fun hm => lt_irrefl x (hw x (by simp)) (hs.1 x hm), ?_⟩
    exact ih (fun y hy => hw y (by simp [hy])) hs.2

theorem hasCard_of_sorted (xs : List PE) (hw : AllWf xs) (hs : PE.Sorted xs) :
    (FSet.ofList xs).HasCard xs.length :=
  ⟨xs, sorted_nodup xs hw hs, rfl, rfl⟩

/-! ## Binary search over a sorted list -/

theorem lt_trans' {a b c : PE} (ha : a.wf = true) (hb : b.wf = true) (hc : c.wf = true) :
    PE.lt a b → PE.lt b c → PE.lt a c := PE_compare_trans_law_holds a b c ha hb hc

/-- Trichotomy. -/
theorem lt_total {a b : PE} (ha : a.wf = true) (hb : b.wf = true) :
    PE.lt a b ∨ a = b ∨ PE.lt b a := by
  unfold PE.lt
  have z := PE_compare_eq_zero_law_holds a b ha hb
  have an := PE_compare_antisymm_law_holds b a hb ha
  rcases Int.lt_trichotomy (PE.compare a b) 0 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (z.1 h))
  · exact Or.inr (Or.inr (an.2 h))

theorem lt_asymm {a b : PE} (ha : a.wf = true) (hb : b.wf = true) : PE.lt a b → ¬ PE.lt b a := by
  intro h1 h2
  exact lt_irrefl a ha (lt_trans' ha hb ha h1 h2)

theorem sorted_get {xs : List PE} (hs : PE.Sorted xs) {i j : Nat} {a b : PE}
    (hij : i < j) (ha : xs[i]? = some a) (hb : xs[j]? = some b) : PE.lt a b := by
  unfold PE.Sorted at hs
  rw [List.pairwise_iff_getElem] at hs
  have hi : i < xs.length := (List.getElem?_eq_some_iff.1 ha).1
  have hj : j < xs.length := (List.getElem?_eq_some_iff.1 hb).1
  have e1 := (List.getElem?_eq_some_iff.1 ha).2
  have e2 := (List.getElem?_eq_some_iff.1 hb).2
  have := hs i j hi hj hij
  rw [e1, e2] at this; exact this

/-- The binary search's index: the elements before it are below the target. -/
abbrev BsIdx (xs : List PE) (pe : PE) (i : Nat) : Prop :=
  i ≤ xs.length ∧ ∀ (k : Nat) (x : PE), xs[k]? = some x → (k < i ↔ PE.lt x pe)

theorem bs_found {xs : List PE} {pe : PE} {i : Nat} (hw : AllWf xs) (hp : pe.wf = true)
    (hs : PE.Sorted xs) (hb : BsIdx xs pe i) :
    (∃ x, xs[i]? = some x ∧ PE.compare x pe = 0) ↔ pe ∈ xs := by
  constructor
  · rintro ⟨x, hx, hc⟩
    have hxw := hw x (List.mem_of_getElem? hx)
    rw [(PE_compare_eq_zero_law_holds x pe hxw hp).1 hc] at hx
    exact List.mem_of_getElem? hx
  · intro hm
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hm
    have hj' : xs[j]? = some pe := by rw [List.getElem?_eq_getElem hj, hje]
    refine ⟨pe, ?_, cmp_self pe hp⟩
    rcases Nat.lt_trichotomy j i with h | h | h
    · exact absurd ((hb.2 j pe hj').1 h) (lt_irrefl pe hp)
    · rw [← h]; exact hj'
    · have hi : i < xs.length := by omega
      have hy : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
      have l1 := sorted_get hs h hy hj'
      have := (hb.2 i xs[i] hy).2 l1
      omega

theorem bs_take_lt {xs : List PE} {pe : PE} {i : Nat} (hb : BsIdx xs pe i) :
    ∀ a ∈ xs.take i, PE.lt a pe := by
  intro a ha
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem ha
  simp only [List.length_take] at hk
  have : xs[k]? = some a := by
    rw [← hke, List.getElem_take]; exact List.getElem?_eq_getElem (by omega)
  exact (hb.2 k a this).1 (by omega)

theorem bs_drop_nlt {xs : List PE} {pe : PE} {i : Nat} (hb : BsIdx xs pe i) :
    ∀ b ∈ xs.drop i, ¬ PE.lt b pe := by
  intro b hbm
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hbm
  simp only [List.length_drop] at hk
  have : xs[i + k]? = some b := by
    rw [← hke, List.getElem_drop]; exact List.getElem?_eq_getElem (by omega)
  intro hl
  have := (hb.2 (i + k) b this).2 hl
  omega

/-- Inserting the target at the search's index keeps the list sorted. -/
theorem bs_insert_sorted {xs : List PE} {pe : PE} {i : Nat} (hw : AllWf xs) (hp : pe.wf = true)
    (hs : PE.Sorted xs) (hb : BsIdx xs pe i) (hn : pe ∉ xs) :
    PE.Sorted (xs.take i ++ pe :: xs.drop i) := by
  have hs' := hs
  unfold PE.Sorted at hs' ⊢
  rw [← List.take_append_drop i xs, List.pairwise_append] at hs'
  rw [List.pairwise_append, List.pairwise_cons]
  have hdrop : ∀ b ∈ xs.drop i, PE.lt pe b := by
    intro b hbm
    have hbw := hw b (List.mem_of_mem_drop hbm)
    rcases lt_total hp hbw with h | h | h
    · exact h
    · subst h; exact absurd (List.mem_of_mem_drop hbm) hn
    · exact absurd h (bs_drop_nlt hb b hbm)
  refine ⟨hs'.1, ⟨hdrop, hs'.2.1⟩, ?_⟩
  intro a ha b hbm
  rcases List.mem_cons.1 hbm with rfl | hbm
  · exact bs_take_lt hb a ha
  · exact hs'.2.2 a ha b hbm

/-- The signs of `compare · pe` are non-decreasing along a sorted list. -/
theorem sorted_signum {xs : List PE} {pe : PE} (hw : AllWf xs) (hp : pe.wf = true)
    (hs : PE.Sorted xs) (k l : Nat) (a b : PE) (ha : xs[k]? = some a) (hb : xs[l]? = some b)
    (hkl : k < l) : sort.signum (PE.compare a pe) ≤ sort.signum (PE.compare b pe) := by
  have haw := hw a (List.mem_of_getElem? ha)
  have hbw := hw b (List.mem_of_getElem? hb)
  have hab := sorted_get hs hkl ha hb
  have za := PE_compare_eq_zero_law_holds a pe haw hp
  have zb := PE_compare_eq_zero_law_holds b pe hbw hp
  have key : PE.compare b pe ≤ 0 → PE.compare a pe < 0 := by
    intro hle
    rcases Int.lt_or_eq_of_le hle with h | h
    · exact lt_trans' haw hbw hp hab h
    · have hbe := zb.1 h; subst hbe; exact hab
  unfold sort.signum
  split <;> split <;> (try split) <;> (try split) <;> omega

/-- `slices.BinarySearchFunc`'s result over the Go elements, read over their models. -/
theorem bs_transfer {E : Type} (es : List E) (xs : List PE) (pe : PE) (m : E → PE)
    (hmd : ∀ (k : Nat) (a : E), es[k]? = some a → xs[k]? = some (m a))
    (hlen : es.length = xs.length) (i : Int) (found : Bool)
    (hi1 : 0 ≤ i ∧ i ≤ es.length)
    (hi2 : ∀ (k : Nat) (ek : E), es[k]? = some ek → ((k : Int) < i ↔ PE.compare (m ek) pe < 0))
    (hi3 : found = true ↔ ∃ ei, es[i.toNat]? = some ei ∧ PE.compare (m ei) pe = 0) :
    BsIdx xs pe i.toNat ∧ (found = true ↔ ∃ x, xs[i.toNat]? = some x ∧ PE.compare x pe = 0) := by
  have back : ∀ (k : Nat) (x : PE), xs[k]? = some x → ∃ a, es[k]? = some a ∧ m a = x := by
    intro k x hx
    have hk : k < es.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hx).1
    refine ⟨es[k], List.getElem?_eq_getElem hk, ?_⟩
    have := hmd k es[k] (List.getElem?_eq_getElem hk)
    rw [hx] at this; exact (Option.some.inj this).symm
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · intro k x hx
    obtain ⟨a, ha, rfl⟩ := back k x hx
    have := hi2 k a ha
    unfold PE.lt
    constructor
    · intro h; exact this.1 (by omega)
    · intro h; have := this.2 h; omega
  · rw [hi3]
    constructor
    · rintro ⟨a, ha, hc⟩; exact ⟨m a, hmd _ a ha, hc⟩
    · rintro ⟨x, hx, hc⟩
      obtain ⟨a, ha, rfl⟩ := back _ x hx
      exact ⟨a, ha, hc⟩

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fieldpath.Assumptions]

/-- A `PathElementSet`'s one field, and the way back. -/
theorem peset_members_acc (l : Loc) (v : fieldpath.PathElementSet) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢ l.[fieldpath.PathElementSet, go!"members"] ↦{dq} v.members' ∗
      (l.[fieldpath.PathElementSet, go!"members"] ↦{dq} v.members' -∗ l ↦{dq} v) := by
  iintro Hl
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %hn⟩
  iStructNamed Hl
  iframe members
  iintro Hm
  iapply typedPointsto_combine _ _ _ hn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hm

/-- The first index of a Go value in a list (classically decided). -/
def peIdx {E : Type} (es : List E) (a : E) : Nat :=
  @List.idxOf _ (@instBEqOfDecidableEq _ (fun x y => Classical.propDecidable (x = y))) a es

theorem peIdx_get {E : Type} (es : List E) (a : E) (h : a ∈ es) : es[peIdx es a]? = some a := by
  letI : DecidableEq E := fun x y => Classical.propDecidable (x = y)
  unfold peIdx
  have hl : es.idxOf a < es.length := List.idxOf_lt_length_of_mem h
  rw [List.getElem?_eq_getElem hl, List.getElem_idxOf]

/-- The model of a Go element of `es` (`xs` its models): what the comparison sees. -/
def mdl {E : Type} (es : List E) (xs : List PE) (d : PE) (a : E) : PE := xs[peIdx es a]?.getD d

theorem isPEL_mdl (es : List fieldpath.PathElement) (xs : Path) (d : PE) :
    isPEL (GF := GF) es xs ⊢ ⌜∀ (k : Nat) (a : fieldpath.PathElement), es[k]? = some a → xs[k]? = some (mdl es xs d a)⌝ := by
  iintro #H
  iapply (pure_forall (PROP := IProp GF)).2; iintro %k
  iapply (pure_forall (PROP := IProp GF)).2; iintro %a
  by_cases hk : es[k]? = some a
  · have hm : a ∈ es := List.mem_of_getElem? hk
    ihave ⟨%x1, %h1, H1⟩ := fpL.isPEL_lookup es xs k a hk $$ H
    ihave ⟨%x2, %h2, H2⟩ := fpL.isPEL_lookup es xs (peIdx es a) a (peIdx_get es a hm) $$ H
    ihave %he := fpL.isPE_agree' a x1 x2 $$ [$H1 $H2]
    ipureintro
    intro _
    unfold mdl; rw [h2, h1, he]; rfl
  · ipureintro; intro h; exact absurd h hk

end rep

end fpA

end smd
end EtcdGrove
end Perennial
