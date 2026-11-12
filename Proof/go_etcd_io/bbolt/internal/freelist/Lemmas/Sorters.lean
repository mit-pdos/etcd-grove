/-
`common.Pgids` and `freelist.txIDx` are sorters (`sort.isSorter`) of the slice they hold, by the
unsigned order; and `sort.Sort`'s result read back as `sortPgids` (U2, `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.SliceLen
public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.sort
public import GeneratedProof.go_etcd_io.bbolt.internal.freelist

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode

/-- The unsigned order of `sort.Sort`'s results. -/
abbrev pgLt (a b : w64) : Prop := uint.Z a < uint.Z b

/-- `sort.Sort`'s post, by `pgLt`, is `sortPgids`. -/
theorem sort_post_eq {xs xs' : List w64} (hp : xs.Perm xs')
    (hs : ∀ (i j : Nat) (xi xj : w64), xs'[i]? = some xi → xs'[j]? = some xj → i < j →
      ¬ pgLt xj xi) :
    xs' = sortPgids xs := by
  refine (sortPgids_eq_of_sorted ?_ hp.symm).symm
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := hs i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  unfold pgLt at this; simp only [uint.Z] at this
  omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The three methods of a slice type `T` of `w64`s whose `Len`, `Less`, `Swap` are the
`sort.Interface` ones of `[]uint64` make it a sorter, given their specs. -/
theorem w64Slice_isSorter (T : go.GoType) (s : GoSlice)
    (hLen : ∀ (l : List w64), {{ s ↦* l }} (App (Val #(methods T go!"Len" #s)) (Val #()))
      {{ RET #(W64 l.length); (s ↦* l : IProp GF) }})
    (hLess : ∀ (l : List w64) (i j : w64) (a b : w64),
      0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b →
      {{ s ↦* l }} (App (App (Val #(methods T go!"Less" #s)) (Val #i)) (Val #j))
      {{ (r : Bool), RET #r; (s ↦* l : IProp GF) ∗ ⌜r = true ↔ pgLt a b⌝ }})
    (hSwap : ∀ (l : List w64) (i j : w64) (a b : w64),
      0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b →
      {{ s ↦* l }} (App (App (Val #(methods T go!"Swap" #s)) (Val #i)) (Val #j))
      {{ RET #(); (s ↦* ((l.set (sint.nat i) b).set (sint.nat j) a) : IProp GF) }}) :
    ⊢ sort.isSorter (GF := GF) (interface.mk T #s) (fun l => s ↦* l) pgLt := by
  unfold sort.isSorter
  isplitr
  · iintro !> %l
    iapply (hLen l)
  isplitr
  · iintro !> %l %i %j %a %b %H
    iapply (hLess l i j a b H)
  · iintro !> %l %i %j %a %b %H
    iapply (hSwap l i j a b H)

section Pgids
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `Pgids(s)` is a sorter of the slice `s`, by the unsigned order. -/
theorem Pgids_isSorter (s : GoSlice) :
    ⊢ sort.isSorter (GF := GF) (interface.mk go_etcd_io.bbolt.internal.common.Pgids.ty #s) (fun l => s ↦* l) pgLt := by
  apply w64Slice_isSorter
  · intro l
    iintro %Φ Hs HΦ
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    rw [method_unfold (t := go_etcd_io.bbolt.internal.common.Pgids.ty)]
    wp_auto
    have hlen : s.len = W64 l.length := by word
    rw [hlen]
    iapply HΦ $$ Hs
  · intro l i j a b ⟨Hi0, Hj0, Ha, Hb⟩
    iintro %Φ Hs HΦ
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    have hib : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := by
      refine ⟨Hi0, ?_⟩; have := (List.getElem?_eq_some_iff.mp Ha).1; word
    have hjb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := by
      refine ⟨Hj0, ?_⟩; have := (List.getElem?_eq_some_iff.mp Hb).1; word
    rw [method_unfold (t := go_etcd_io.bbolt.internal.common.Pgids.ty)]
    wp_auto
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index s (sint.Z i) l (DFrac.own 1) a Hi0 $$ [$Hs] as Hs
    · ipureintro; exact Ha
    (try wp_auto)
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index s (sint.Z j) l (DFrac.own 1) b Hj0 $$ [$Hs] as Hs
    · ipureintro; exact Hb
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    unfold pgLt; simp only [uint.Z]
    constructor
    · intro h; have := of_decide_eq_true h; word
    · intro h; apply decide_eq_true; word
  · intro l i j a b ⟨Hi0, Hj0, Ha, Hb⟩
    iintro %Φ Hs HΦ
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    have hib : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := by
      refine ⟨Hi0, ?_⟩; have := (List.getElem?_eq_some_iff.mp Ha).1; word
    have hjb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := by
      refine ⟨Hj0, ?_⟩; have := (List.getElem?_eq_some_iff.mp Hb).1; word
    rw [method_unfold (t := go_etcd_io.bbolt.internal.common.Pgids.ty)]
    wp_auto
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    (try wp_auto)
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    (try wp_auto)
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index s (sint.Z j) l (DFrac.own 1) b Hj0 $$ [$Hs] as Hs
    · ipureintro; exact Hb
    (try wp_auto)
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    (try wp_auto)
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index s (sint.Z i) l (DFrac.own 1) a Hi0 $$ [$Hs] as Hs
    · ipureintro; exact Ha
    (try wp_auto)
    wp_apply wp_store_slice_index s (sint.Z i) l b $$ [$Hs] as Hs
    · ipureintro; word
    (try wp_auto)
    wp_apply wp_store_slice_index s (sint.Z j) (l.set (sint.Z i).toNat b) a $$ [$Hs] as Hs
    · ipureintro; simp only [List.length_set]; word
    (try wp_auto)
    iapply HΦ $$ Hs

end Pgids

section txIDx
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `txIDx(s)` is a sorter of the slice `s`, by the unsigned order. -/
theorem txIDx_isSorter (s : GoSlice) :
    ⊢ sort.isSorter (GF := GF) (interface.mk go_etcd_io.bbolt.internal.freelist.txIDx.ty #s) (fun l => s ↦* l) pgLt := by
  apply w64Slice_isSorter
  · intro l
    iintro %Φ Hs HΦ
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    rw [method_unfold (t := go_etcd_io.bbolt.internal.freelist.txIDx.ty)]
    wp_auto
    have hlen : s.len = W64 l.length := by word
    rw [hlen]
    iapply HΦ $$ Hs
  · intro l i j a b ⟨Hi0, Hj0, Ha, Hb⟩
    iintro %Φ Hs HΦ
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    have hib : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := by
      refine ⟨Hi0, ?_⟩; have := (List.getElem?_eq_some_iff.mp Ha).1; word
    have hjb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := by
      refine ⟨Hj0, ?_⟩; have := (List.getElem?_eq_some_iff.mp Hb).1; word
    rw [method_unfold (t := go_etcd_io.bbolt.internal.freelist.txIDx.ty)]
    wp_auto
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index s (sint.Z i) l (DFrac.own 1) a Hi0 $$ [$Hs] as Hs
    · ipureintro; exact Ha
    (try wp_auto)
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index s (sint.Z j) l (DFrac.own 1) b Hj0 $$ [$Hs] as Hs
    · ipureintro; exact Hb
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    unfold pgLt; simp only [uint.Z]
    constructor
    · intro h; have := of_decide_eq_true h; word
    · intro h; apply decide_eq_true; word
  · intro l i j a b ⟨Hi0, Hj0, Ha, Hb⟩
    iintro %Φ Hs HΦ
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    have hib : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := by
      refine ⟨Hi0, ?_⟩; have := (List.getElem?_eq_some_iff.mp Ha).1; word
    have hjb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := by
      refine ⟨Hj0, ?_⟩; have := (List.getElem?_eq_some_iff.mp Hb).1; word
    rw [method_unfold (t := go_etcd_io.bbolt.internal.freelist.txIDx.ty)]
    wp_auto
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    (try wp_auto)
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    (try wp_auto)
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index s (sint.Z j) l (DFrac.own 1) b Hj0 $$ [$Hs] as Hs
    · ipureintro; exact Hb
    (try wp_auto)
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    (try wp_auto)
    (try simp only [hib, hjb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index s (sint.Z i) l (DFrac.own 1) a Hi0 $$ [$Hs] as Hs
    · ipureintro; exact Ha
    (try wp_auto)
    wp_apply wp_store_slice_index s (sint.Z i) l b $$ [$Hs] as Hs
    · ipureintro; word
    (try wp_auto)
    wp_apply wp_store_slice_index s (sint.Z j) (l.set (sint.Z i).toNat b) a $$ [$Hs] as Hs
    · ipureintro; simp only [List.length_set]; word
    (try wp_auto)
    iapply HΦ $$ Hs

end txIDx

end proof

end bbolt
end EtcdGrove
end Perennial
