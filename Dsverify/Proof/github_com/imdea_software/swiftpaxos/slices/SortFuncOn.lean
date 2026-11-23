/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/slices/SortFuncOn.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`slices.SortFunc` with the comparator needed only on the slice's elements: Perennial's proof
(Perennial/Proof/slices/SortFunc.lean and its `pdqsort` callees) re-run over `cmpOn R φ cmp`
(the comparator's spec only on values satisfying `φ`, which every element of the input
satisfies; Proof/slices/SortFuncOn/*.lean are the copies of the callees' specs and proofs), the
copies linked, and `slices.SortFunc.specOn` (Proof/swift/RecSync.lean, the hypothesis of
`recoveredSync`'s proof) derived with `φ x := x ∈ xs`.
-/
module

public import Perennial.Proof.slices.SortFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Proof.slices.Link
public import Perennial.Proof.math.bits.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.pdqsortCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec

variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- `slices.SortFunc.spec` with `cmpOn R φ cmp` for `cmpImplements R cmp`, given `φ` on every
element of the input. -/
abbrev slices.SortFunc.specPhi : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) (φ : E → Prop) {S : go.GoType}
    [S ↓u go.SliceType Et] (data : GoSlice) (cmp_code : GoFunc) (xs : List E)
    (SWO : StrictWeakOrder R) (Hφ : AllOn φ xs),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hlength_bound" ∷ ⌜xs.length ≤ 2 ^ 62⌝ ∗
        "#Hcmp" ∷ cmpOn R φ cmp_code }}
      (App (App (Val #(functions SortFunc [S, Et])) (Val #data)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜∀ (i j : Nat) (xi xj : E), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → ¬ R xj xi⌝ }}

end spec

section proof

variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- Perennial's `slices.SortFunc.wp_proof`, over `cmpOn`. -/
theorem slices.SortFunc.wp_proofPhi
    (wp_Len : math.bits.Len.spec (GF := GF) (hG := hG))
    (wp_pdqsortCmpFunc : slices.pdqsortCmpFunc.specOn (GF := GF) (hG := hG)) :
    slices.SortFunc.specPhi (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R φ S _ data cmp_code xs SWO Hφ
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  wp_apply wp_Len with %l _
  wp_apply wp_pdqsortCmpFunc R φ data (W64 0) data.len l cmp_code xs Hφ $$ [Hxs]
    with %xs' ⟨Hxs, %Hperm, %Hsorted, %Houtside⟩
  · iframe Hxs; iframe #; ipureintro
    refine ⟨by word, ?_⟩
    unfold header; simp
  iapply HΦ
  iframe Hxs
  ipureintro
  refine ⟨Hperm, ?_⟩
  intro i j xi xj Hi Hj Hij
  apply isSortedSeg_is_sorted R xs' _ i j xi xj Hij Hi Hj
  rw [← Hperm.length_eq, Hlen.1]
  exact Hsorted

end proof

section link

variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.wp_insertionSortCmpFuncOn : slices.insertionSortCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.insertionSortCmpFunc.wp_proofOn

theorem slices.wp_siftDownCmpFuncOn : slices.siftDownCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.siftDownCmpFunc.wp_proofOn

theorem slices.wp_heapSortCmpFuncOn : slices.heapSortCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.heapSortCmpFunc.wp_proofOn slices.wp_siftDownCmpFuncOn

theorem slices.wp_breakPatternsCmpFuncOn : slices.breakPatternsCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.breakPatternsCmpFunc.wp_proofOn slices.wp_nextPowerOfTwo slices.xorshift.wp_Next

theorem slices.wp_order2CmpFuncOn : slices.order2CmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.order2CmpFunc.wp_proofOn

theorem slices.wp_medianCmpFuncOn : slices.medianCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.medianCmpFunc.wp_proofOn slices.wp_order2CmpFuncOn

theorem slices.wp_medianAdjacentCmpFuncOn : slices.medianAdjacentCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.medianAdjacentCmpFunc.wp_proofOn slices.wp_medianCmpFuncOn

theorem slices.wp_choosePivotCmpFuncOn : slices.choosePivotCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.choosePivotCmpFunc.wp_proofOn slices.wp_medianCmpFuncOn slices.wp_medianAdjacentCmpFuncOn

theorem slices.wp_reverseRangeCmpFuncOn : slices.reverseRangeCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.reverseRangeCmpFunc.wp_proofOn

theorem slices.wp_partialInsertionSortCmpFuncOn :
    slices.partialInsertionSortCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.partialInsertionSortCmpFunc.wp_proofOn

theorem slices.wp_partitionEqualCmpFuncOn : slices.partitionEqualCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.partitionEqualCmpFunc.wp_proofOn

theorem slices.wp_partitionCmpFuncOn : slices.partitionCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.partitionCmpFunc.wp_proofOn

theorem slices.wp_pdqsortCmpFuncOn : slices.pdqsortCmpFunc.specOn (GF := GF) (hG := hG) :=
  slices.pdqsortCmpFunc.wp_proofOn slices.wp_insertionSortCmpFuncOn slices.wp_heapSortCmpFuncOn
    slices.wp_breakPatternsCmpFuncOn slices.wp_choosePivotCmpFuncOn slices.wp_reverseRangeCmpFuncOn
    slices.wp_partialInsertionSortCmpFuncOn slices.wp_partitionEqualCmpFuncOn
    slices.wp_partitionCmpFuncOn

theorem slices.wp_SortFuncPhi : slices.SortFunc.specPhi (GF := GF) (hG := hG) :=
  slices.SortFunc.wp_proofPhi math.bits.wp_Len slices.wp_pdqsortCmpFuncOn

end link

end Perennial

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section bridge
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [slices.Assumptions]

/-- **`slices.SortFunc.specOn`** (Proof/swift/RecSync.lean): `specPhi` with `φ x := x ∈ xs`;
the comparator's spec on two elements of the input from the persistent `P` of each. -/
theorem slices.SortFunc.wp_proofOn : slices.SortFunc.specOn (hG := hG) := by
  intro E _ _ Et _ R P _ S _ data cmp_code xs SWO
  haveI : Persistent (slices.cmpImplementsOn (Et := Et) R P cmp_code) := by
    unfold slices.cmpImplementsOn; infer_instance
  iintro %Φ ⟨#Hpkg, Hxs, %Hlen, #HP, #Hcmp⟩ HΦ
  ihave #Hon : slices.cmpOn (GF := netDistGF) R (fun x => x ∈ xs) cmp_code $$ []
  · unfold slices.cmpOn
    iintro %x %y %Ψ !> %Hxy HΨ
    obtain ⟨hx, hy⟩ := Hxy
    ihave #Px := (BigSepL.bigSepL_mem (Φ := fun x => P x) hx) $$ HP
    ihave #Py := (BigSepL.bigSepL_mem (Φ := fun x => P x) hy) $$ HP
    unfold slices.cmpImplementsOn
    iapply Hcmp $$ [] HΨ
    isplitl [] <;> iassumption
  iapply (slices.wp_SortFuncPhi (E := E) (Et := Et) R (fun x => x ∈ xs) (S := S) data cmp_code xs
    SWO (fun _ h => h)) $$ [Hxs]
  · iframe Hxs; iframe #; ipureintro; exact Hlen
  iintro %xs' !> ⟨Hxs, %Hperm, %Hsorted⟩
  iapply HΦ
  iframe Hxs
  ipureintro
  exact ⟨Hperm, Hsorted⟩

end bridge

end Perennial.github_com.imdea_software.swiftpaxos
