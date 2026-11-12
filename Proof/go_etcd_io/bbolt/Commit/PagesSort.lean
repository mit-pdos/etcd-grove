/-
`common.Pages` as a `sort.Interface` (U10c, `notes/bbolt-proof-plan.md`; `tx.write()`'s
`sort.Sort(pages)`): `Len`, `Less` (reads the two pages' `id` fields) and `Swap`, over a slice of
page pointers `l.map f` whose headers `f e ↦ g e` are owned (`pagesR`). `Less` answers some
boolean (`sorterAnySpec`): `tx.write` needs only a permutation, the pages' extents being disjoint.
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.sort.SortAnyLess

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- What the sorter over the slice `sl` holds: the page pointers `l.map f`, and each page's
header `g e`. -/
def pagesR {E : Type} (sl : GoSlice) (f : E → Loc) (g : E → Page) (l : List E) : IProp GF :=
  iprop(sl ↦* l.map f ∗ [∗list] e ∈ l, f e ↦ g e)

theorem Pages.wp_Len (sl : GoSlice) (ls : List Loc) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ sl ↦*{dq} ls }}
      (App (Val (sl @!! Pages.ty @!! go!"Len")) (Val #()))
    {{ RET #(W64 ls.length); sl ↦*{dq} ls }} := by
  wp_start as Hs
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have : sl.len = W64 (ls.length : Int) := by
    rw [Hl.1]
    show sl.len = BitVec.ofInt 64 ((sint.Z sl.len).toNat : Int)
    rw [Int.toNat_of_nonneg Hl.2]
    exact BitVec.ofInt_toInt.symm
  rw [this]
  iapply HΦ
  iexact Hs

theorem Pages.wp_Swap (sl : GoSlice) (ps : List Loc) (i j : w64) (a b : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ sl ↦* ps ∗
        ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ ps[sint.nat i]? = some a ∧ ps[sint.nat j]? = some b⌝ }}
      (App (App (Val (sl @!! Pages.ty @!! go!"Swap")) (Val #i)) (Val #j))
    {{ RET #(); sl ↦* (ps.set (sint.nat i) b).set (sint.nat j) a }} := by
  wp_start as ⟨Hs, %Hij⟩
  wp_auto
  obtain ⟨hi0, hj0, ha, hb⟩ := Hij
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hilt : sint.nat i < ps.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < ps.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by
    have := Hl.1; refine ⟨hi0, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by
    have := Hl.1; refine ⟨hj0, ?_⟩; word
  try simp only [Hbi, _root_.and_self, ite_true]
  (try wp_auto)
  try simp only [Hbj, _root_.and_self, ite_true]
  (try wp_auto)
  try simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z j) ps (DFrac.own 1) b hj0 $$ [Hs] as Hs
  · iframe; ipureintro; exact hb
  (try wp_auto)
  try simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z i) ps (DFrac.own 1) a hi0 $$ [Hs] as Hs
  · iframe; ipureintro; exact ha
  (try wp_auto)
  wp_apply wp_store_slice_index sl (sint.Z i) ps b $$ [Hs] as Hs
  · iframe; ipureintro; exact ⟨hi0, by have := Hl.1; word⟩
  (try wp_auto)
  wp_apply wp_store_slice_index sl (sint.Z j) _ a $$ [Hs] as Hs
  · iframe; ipureintro; exact ⟨hj0, by simp only [List.length_set]; have := Hl.1; word⟩
  (try wp_auto)
  iapply HΦ
  iexact Hs

/-- Every header of the list at half, twice. -/
theorem pagesHdr_halves {E : Type} (f : E → Loc) (g : E → Page) (l : List E) :
    ([∗list] e ∈ l, f e ↦ g e) ⊣⊢
      ([∗list] e ∈ l, typedPointsto (GF := GF) (f e) (g e) (DFrac.own (1 : Qp).half)) ∗
        [∗list] e ∈ l, typedPointsto (GF := GF) (f e) (g e) (DFrac.own (1 : Qp).half) := by
  constructor
  · refine (BigSepL.bigSepL_mono ?_).trans BigSepL.bigSepL_sep_eqv.1
    intro _ e _; exact (typedPointsto_half_split _ _ _).1
  · refine BigSepL.bigSepL_sep_eqv.2.trans (BigSepL.bigSepL_mono ?_)
    intro _ e _
    iintro H
    icases typedPointsto_half_combine _ _ _ _ $$ H with ⟨-, H⟩
    iexact H

theorem Pages.wp_Less {E : Type} (sl : GoSlice) (f : E → Loc) (g : E → Page) (l : List E)
    (i j : w64) (a b : E)
    (hij : 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ pagesR sl f g l }}
      (App (App (Val (sl @!! Pages.ty @!! go!"Less")) (Val #i)) (Val #j))
    {{ (r : Bool), RET #r; pagesR sl f g l }} := by
  wp_start as Hr
  unfold pagesR
  icases Hr with ⟨Hs, Hh⟩
  wp_auto
  obtain ⟨hi0, hj0, ha, hb⟩ := hij
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hilt : sint.nat i < l.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < l.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by
    have := Hl.1; simp only [List.length_map] at this; refine ⟨hi0, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by
    have := Hl.1; simp only [List.length_map] at this; refine ⟨hj0, ?_⟩; word
  have hma : (l.map f)[(sint.Z i).toNat]? = some (f a) := by
    rw [List.getElem?_map]; rw [show (sint.Z i).toNat = sint.nat i from rfl, ha]; rfl
  have hmb : (l.map f)[(sint.Z j).toNat]? = some (f b) := by
    rw [List.getElem?_map]; rw [show (sint.Z j).toNat = sint.nat j from rfl, hb]; rfl
  icases (pagesHdr_halves f g l).1 $$ Hh with ⟨Hh1, Hh2⟩
  icases BigSepL.bigSepL_mem_acc (List.mem_of_getElem? ha) $$ Hh1 with ⟨Ha, Hh1⟩
  icases BigSepL.bigSepL_mem_acc (List.mem_of_getElem? hb) $$ Hh2 with ⟨Hb, Hh2⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Ha with ⟨Ha, %Hann⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hb with ⟨Hb, %Hbnn⟩
  iStructNamed Ha
  irename id => Haid
  irename flags => Haf
  irename count => Hac
  irename overflow => Hao
  iStructNamed Hb
  try simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z i) _ (DFrac.own 1) (f a) hi0 $$ [Hs] as Hs
  · iframe; ipureintro; exact hma
  (try wp_auto)
  try simp only [Hbj, _root_.and_self, ite_true]
  (try wp_auto)
  wp_apply wp_load_slice_index sl (sint.Z j) _ (DFrac.own 1) (f b) hj0 $$ [Hs] as Hs
  · iframe; ipureintro; exact hmb
  (try wp_auto)
  iapply HΦ
  ihave Ha : typedPointsto (f a) (g a) (DFrac.own (1 : Qp).half) $$ [Haid Haf Hac Hao]
  · iapply typedPointsto_combine _ _ _ Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hb : typedPointsto (f b) (g b) (DFrac.own (1 : Qp).half) $$ [id flags count overflow]
  · iapply typedPointsto_combine _ _ _ Hbnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hh1 := Hh1 $$ Ha
  ihave Hh2 := Hh2 $$ Hb
  iframe Hs
  iapply (pagesHdr_halves f g l).2
  iframe

/-- **`Pages` over the slice `sl` is a sorter** of the list held by `pagesR`. -/
theorem pages_sorter {E : Type} (sl : GoSlice) (f : E → Loc) (g : E → Page) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ⊢
      sorterAnySpec (interface.mk Pages.ty #sl) (pagesR (GF := GF) sl f g) := by
  iintro #Hpkg
  unfold sorterAnySpec
  isplitr
  · imodintro
    iintro %l
    iintro !> %Φ HR HΦ
    unfold pagesR
    icases HR with ⟨Hs, Hh⟩
    wp_apply (Pages.wp_Len sl (l.map f) (DFrac.own 1)) $$ [$Hs] as Hs
    rw [List.length_map]
    iapply HΦ
    iframe
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ HR HΦ
    wp_apply (Pages.wp_Less sl f g l i j a b Hij) $$ [$HR] as %r HR
    iapply HΦ
    iexact HR
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ HR HΦ
  obtain ⟨hi, hj, ha, hb'⟩ := Hij
  unfold pagesR
  icases HR with ⟨Hs, Hh⟩
  have hp : l.Perm ((l.set (sint.nat i) b).set (sint.nat j) a) :=
    slices.swap_perm l (sint.nat j) (sint.nat i) b a hb' ha
  wp_apply (Pages.wp_Swap sl (l.map f) i j (f a) (f b)) $$ [$Hs] as Hs
  · ipureintro
    refine ⟨hi, hj, ?_, ?_⟩
    · rw [List.getElem?_map, ha]; rfl
    · rw [List.getElem?_map, hb']; rfl
  iapply HΦ
  rw [List.map_set, List.map_set]
  iframe Hs
  iapply (BigSepL.bigSepL_perm (Φ := fun e => iprop(f e ↦ g e)) hp).1
  iexact Hh

end proof

end bbolt
end EtcdGrove
end Perennial
