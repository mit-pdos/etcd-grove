module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SeededAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.splitKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.setItem

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem SeededAt.wp_proof (wp_splitKey : splitKey.spec (GF := GF) (hG := hG))
    (wp_setItem : setItem.spec (GF := GF) (hG := hG)) :
    SeededAt.spec (GF := GF) (hG := hG) := by
  intro r1 r2 h1 h12 h2
  wp_start as -
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %l1 ⟨Hl1, Hc1⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %lk ⟨Hlk, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  imod ownSlice_persist _ _ _ $$ Hlk with #Hlk
  (try wp_auto)
  rename_i gi_ptr
  irename : (gi_ptr ↦ (zero_val w64) : IProp GF) => iv
  ihave HI : (∃ (j : w64) (kv : GoString) (iv : w64) (stv : mstore) (hsl : GoSlice) (hs : List mstore),
      "i" ∷ i_ptr ↦ j ∗ "k" ∷ k_ptr ↦ kv ∗ "iv" ∷ gi_ptr ↦ iv ∗ "st" ∷ st_ptr ↦ stv ∗
      "h" ∷ h_ptr ↦ hsl ∗ "Hh" ∷ hsl ↦* hs ∗ "Hc" ∷ ownSliceCap mstore hsl (DFrac.own 1) ∗
      "Hst" ∷ storeOwn stv (seedPrefL r1 r2 (sint.nat j)).st ∗
      "Hhs" ∷ ([∗list] x;g ∈ hs;(seedPrefL r1 r2 (sint.nat j)).hist, storeOwn x g) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 2⌝ : IProp GF) $$ [i k iv st h Hl1 Hc1]
  · iexists W64 0, _, _, _, _, _
    iframe
    rw [show sint.nat (W64 0) = 0 by word]
    simp only [seedPrefL, if_pos, seedInitL]
    ihave Hn := ownSlice_nil (V := item) (GF := GF) DFrac.discard
    unfold storeOwn
    isplitl [Hn]
    · isplitl
      · iexact Hn
      · ipureintro; rfl
    isplitl
    · iapply BigSepL2.bigSepL2_singleton.2
      isplitl
      · iexact Hn
      · ipureintro; rfl
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hj01 : j = W64 0 ∨ j = W64 1 := by
      have : sint.Z j < 2 := by simp at Hif; exact lt_of_lt_of_eq Hif (by decide)
      word
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z (W64 (max (max (0 + 1 + 1) 0) 0)) := by
      rcases hj01 with rfl | rfl <;> decide
    have hk : ([go!"ns-1/pod-1", zero_val GoString].set (sint.nat (W64 (0 + 1))) go!"ns-2/pod-2")[sint.nat j]? =
        some (if sint.nat j = 0 then kA else kB) := by
      rcases hj01 with rfl | rfl <;> rfl
    have hrv : ([r1, r2] : List w64)[sint.nat j]? = some (if sint.nat j = 0 then r1 else r2) := by
      rcases hj01 with rfl | rfl <;> rfl
    have hpre : seedPrefL r1 r2 (sint.nat (j + W64 1)) =
        seedStepL (seedPrefL r1 r2 (sint.nat j)) (if sint.nat j = 0 then kA else kB)
          (if sint.nat j = 0 then r1 else r2) := by
      rcases hj01 with rfl | rfl <;> rfl
    have hlt : uint.nat (seedPrefL r1 r2 (sint.nat j)).st.rv + 1 ≤
        uint.nat (if sint.nat j = 0 then r1 else r2) := by
      rcases hj01 with rfl | rfl
      · simp [seedPrefL, seedInitL]; omega
      · show uint.nat r1 + 1 ≤ uint.nat r2; omega
    have hrv63 : uint.nat (if sint.nat j = 0 then r1 else r2) < 2 ^ 63 := by
      split <;> omega
    have hitems : (seedPrefL r1 r2 (sint.nat j)).st.items.length ≤ 1 := by
      rcases hj01 with rfl | rfl
      · simp [seedPrefL, seedInitL]
      · have h1 : sint.nat (W64 1) = 1 := by word
        simp only [h1, seedPrefL, seedStepL, seedInitL]
        simpa using setItemL_length ([] : List item) (seedItem kA r1)
    have hj2 : sint.Z j < 2 := by rcases hj01 with rfl | rfl <;> decide
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z j) _ DFrac.discard (if sint.nat j = 0 then kA else kB) hb.1 $$ [Hlk] as -
    · isplit
      · iexact Hlk
      · ipureintro; exact hk
    generalize (if sint.nat j = 0 then kA else kB) = key at hpre
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %lr ⟨Hlr, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z j) _ (DFrac.own 1) (if sint.nat j = 0 then r1 else r2) hb.1 $$ [Hlr] as -
    · isplit
      · iexact Hlr
      · ipureintro; rcases hj01 with rfl | rfl <;> rfl
    generalize hrvd : (if sint.nat j = 0 then r1 else r2) = rv at hrv hpre hlt hrv63
    generalize seedPrefL r1 r2 (sint.nat j) = H at hpre hlt hitems
    ihave Hst' : iprop(stv.items' ↦*□ H.st.items ∗ ⌜stv.rv' = H.st.rv⌝) $$ [Hst]
    · unfold storeOwn; iexact Hst
    icases Hst' with ⟨#Hsti, %Hstrv⟩
    (try wp_auto)
    ihave HJ : (∃ (rr : w64) (hsl : GoSlice) (hs : List mstore),
        "r" ∷ r_ptr ↦ rr ∗ "h" ∷ h_ptr ↦ hsl ∗ "Hh" ∷ hsl ↦* hs ∗
        "Hc" ∷ ownSliceCap mstore hsl (DFrac.own 1) ∗
        "Hhs" ∷ ([∗list] x;g ∈ hs;(H.hist ++ padL H.st.items (uint.nat H.st.rv + 1) (uint.nat rr)),
          storeOwn x g) ∗
        "%Hr" ∷ ⌜uint.nat H.st.rv + 1 ≤ uint.nat rr ∧ uint.nat rr ≤ uint.nat rv⌝ : IProp GF)
        $$ [r h Hh Hc Hhs]
    · iexists _, _, _
      iframe
      rw [Hstrv, show uint.nat (H.st.rv + W64 1) = uint.nat H.st.rv + 1 by word, padL_self,
        List.append_nil]
      iframe
      ipureintro; constructor <;> word
    wp_for HJ
    wp_if_destruct
    · wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %la ⟨Hla, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hh $Hc $Hla] as %hsl' ⟨Hh, Hc, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists rr + W64 1, hsl', _
      iframe
      have hr1 : uint.nat (rr + W64 1) = uint.nat rr + 1 := by word
      rw [hr1, padL_snoc _ _ _ Hr.1, ← List.append_assoc]
      isplitl
      · iapply BigSepL2.bigSepL2_snoc.2
        iframe
        (try unfold storeOwn)
        isplitl
        · iexact Hsti
        · ipureintro; simp only; word
      ipureintro; constructor <;> word
    · have hrr : rr = rv := by
        have : ¬ uint.Z rr < uint.Z rv := Hif
        word
      wp_apply wp_splitKey
      (try wp_auto)
      wp_apply wp_setItem $$ [Hsti]
      · isplitl
        · iexact Hsti
        · ipureintro; omega
      iintro %out ⟨-, Hout, -⟩
      imod ownSlice_persist _ _ _ $$ Hout with #Hout
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %la ⟨Hla, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hh $Hc $Hla] as %hsl' ⟨Hh, Hc, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _, _, _, hsl', _
      iframe
      rw [hpre]
      have hrr' : uint.nat rr = uint.nat rv := by rw [hrr]
      rw [hrr'] at *
      isplitr
      · (try unfold storeOwn)
        simp only [seedStepL, seedItem]
        isplitl
        · iexact Hout
        · ipureintro; trivial
      isplitl
      · simp only [seedStepL]
        iapply BigSepL2.bigSepL2_snoc.2
        simp only [seedItem]
        isplitl [Hhs]
        · iexact Hhs
        (try unfold storeOwn)
        isplitl
        · iexact Hout
        · ipureintro; trivial
      ipureintro; constructor <;> word
  · have hj2 : j = W64 2 := by
      have : ¬ sint.Z j < 2 := by
        intro h; apply Hif; simp; exact lt_of_lt_of_eq h (by decide)
      word
    rw [hj2, show sint.nat (W64 2) = 2 by word] at *
    have hP : seedPrefL r1 r2 2 = seedSharedL r1 r2 := rfl
    rw [hP]
    (try wp_auto)
    iapply HΦ
    iexists hs
    iframe

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
