/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/slices/SortFuncOn/partitionCmpFunc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Perennial's `slices.partitionCmpFunc` spec and proof (Perennial/Spec/slices/partitionCmpFunc.lean,
Perennial/Proof/slices/partitionCmpFunc.lean) with the comparator needed only on `φ`, which every element
of the slice satisfies (Proof/slices/SortFuncOn/Basics.lean).
-/
module

public import Perennial.Proof.slices.PartitionBasics
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.PartBasics
public import Perennial.Spec.slices.partitionCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.Basics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec

variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

abbrev slices.partitionCmpFunc.specOn : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (φ : E → Prop) (data : GoSlice)
    (a b pivot : w64) (cmp_code : GoFunc) (xs : List E) (Hφ : AllOn φ xs),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hcmp" ∷ cmpOn R φ cmp_code ∗
        "%pivot_range" ∷ ⌜sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ }}
      (App (App (App (App (App (Val #(functions partitionCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #pivot)) (Val #cmp_code))
    {{ (xs' : List E) (bl : Bool) (r : w64), RET (PairV #r #bl);
        data ↦* xs' ∗
        "%range" ∷ ⌜sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hpart" ∷ ⌜IsPartitioned R xs' (sint.nat a) (sint.nat b) (sint.nat r)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }}

end spec

section proof

variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.partitionCmpFunc.wp_proofOn : slices.partitionCmpFunc.specOn (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ φ data a b pivot cmp_code xs Hφ
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  list_elem xs (sint.nat pivot) as xp
  list_elem xs (sint.nat a) as xa
  slice_index_if
  wp_auto
  slice_index_if
  wp_auto
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z pivot) xs _ xp (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxp_lookup
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z a) xs _ xa (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxa_lookup
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z a) xs xp $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; omega
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z pivot) _ xa $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; simp; omega
  wp_auto
  ipersist a
  ipersist data
  ipersist cmp
  ihave HI : partInv R data a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold partInv
    iexists _, _, _
    iframe
    ipureintro
    simp only [sint_toNat]
    refine ⟨by word, ?_, ?_, swap_perm xs _ _ xp xa Hxp_lookup Hxa_lookup,
      outsideSame_swap _ _ _ _ _ _ _ (by word) (by word), by simp, by simp⟩
    · intro i xi xa' _ _; constructor <;> intro <;> word
    · by_cases h : sint.nat pivot = sint.nat a
      · rw [h, list_lookup_insert_eq _ (by simp; word)]
        rw [h, Hxa_lookup] at Hxp_lookup; exact Hxp_lookup
      · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by word)]
  part_loop1_on
  part_loop2_on
  part_load_j
  wp_if_destruct
  · part_finish
  · part_swap
    clear Hpart Hpivot HPerm1 Houtside1 HBr1 HBr2 HBr1' HBr2' Hlen2 Hxi_lookup Hxj_lookup ij_bound Hif Hle
      xs1 i_val j_val xi xj
    wp_for
    part_loop1_on
    part_loop2_on
    part_load_j
    wp_if_destruct
    · wp_for_post
      part_finish
    · part_swap
      wp_for_post
      unfold partInv
      simp only [Bool.false_eq_true]
      iframe

end proof

end Perennial
