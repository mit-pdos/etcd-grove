/-
Lean-first (no Rocq counterpart).

The proof of `(*histHashes).skipTo`: at or beyond `t`, `c` itself (`skipToL_le`); otherwise, `hh.mu`
held, `base` is `c`'s history's canonical node, `gaps[base]` (taken out of the map, or none) holds the
nodes of `base`'s history with one, two, ... foreign stores appended (`gapsOwn`: the same history as
`c`'s, by `histOwn_agree_len`, so its last store `c`'s store, by `HWf`), grown by `intern` up to
`t - rv` nodes and put back; node `t - rv - 1` holds `skipToL`'s history (`repeat_foreignL_gaps`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__skipTo
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__canonLocked
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__intern
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histLen

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section pure
variable [GooseExts]

/-- One more foreign store. -/
theorem gapsL_succ (s : GSt) (len j : Nat) :
    gapsL s len (j + 1) = gapsL s len j ++ [⟨s.items, W64 ((len + j + 1 : Nat) : Int)⟩] := by
  simp [gapsL, List.range_succ]

/-- **`skipToL`'s stores are `gapsL`'s** (a well-formed configuration). -/
theorem repeat_foreignL_gaps (H : HSt) (hw : HWf H) (j : Nat) (hj : H.hist.length + j < 2 ^ 64) :
    Nat.repeat k8s_dist.foreignL j H =
      ⟨⟨H.st.items, W64 ((H.hist.length + j : Nat) : Int)⟩, H.hist ++ gapsL H.st H.hist.length j⟩ := by
  induction j with
  | zero =>
    obtain ⟨⟨items, rv⟩, hist⟩ := H
    simp only [HWf] at hw
    simp only [Nat.repeat, Nat.add_zero, gapsL, List.range_zero, List.map_nil, List.append_nil]
    have : rv = W64 ((hist.length : Nat) : Int) := by rw [hw.1]; word
    rw [← this]
  | succ j ih =>
    simp only [Nat.repeat]
    rw [ih (by omega)]
    simp only [k8s_dist.foreignL, gapsL_succ, List.append_assoc]
    have : W64 ((H.hist.length + j : Nat) : Int) + W64 1 = W64 ((H.hist.length + (j + 1) : Nat) : Int) := by
      word
    rw [this, show H.hist.length + j + 1 = H.hist.length + (j + 1) by omega]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem histHashes.skipTo.wp_proof
    (wp_canonLocked : histHashes.canonLocked.spec (GF := GF) (hG := hG))
    (wp_intern : histHashes.intern.spec (GF := GF) (hG := hG))
    (wp_histLen : histLen.spec (GF := GF) (hG := hG)) :
    histHashes.skipTo.spec (GF := GF) (hG := hG) := by
  intro hh c g t
  wp_start as ⟨#Hhh, #Hc, %Hpre⟩
  obtain ⟨Hwf, Ht⟩ := Hpre
  unfold cfgOwn
  icases Hc with ⟨#Hcst, #Hch, #Hcp, %Hchl⟩
  iunfold storeOwn at Hcst
  icases Hcst with ⟨#Hitems, %Hrv⟩
  (try wp_auto)
  wp_if_destruct
  · -- t ≤ rv: c itself
    (try wp_auto)
    iapply HΦ
    rw [k8s_dist.skipToL_le _ _ (by rw [← Hrv]; word)]
    unfold storeOwn
    iframe
    iframe #
    ipureintro; exact ⟨Hrv, Hchl⟩
  have Htr := Hif
  obtain ⟨hs0, x0, Hsnoc⟩ : ∃ hs0 x0, g.st.hist = hs0 ++ [x0] := by
    rcases nil_or_snoc g.st.hist with h | h
    · have := Hwf.2; rw [h] at this; simp at this
    · exact h
  wp_if_destruct
  · -- a nil history: impossible (`HWf`: a store in it)
    rw [Hsnoc] at *
    icases (histOwn_snoc _ hs0 x0).1 $$ Hch with ⟨%hn, Hp, -⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
    exact absurd Hif Hnn
  have HL : g.st.hist.length = uint.nat c.st'.rv' := by rw [Hrv]; exact Hwf.1
  have HLt : g.st.hist.length < uint.nat t := by
    have : uint.nat c.st'.rv' < uint.nat t := by
      have h : uint.Z c.st'.rv' < uint.Z t := by omega
      word
    omega
  have HL63 : g.st.hist.length < 2 ^ 63 := by omega
  iunfold hhOwn at Hhh
  icases Hhh with ⟨#Hsync, #Hmu⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (hhInv hh) $$ [$Hsync $Hmu] as ⟨Hlk, Hinv⟩
  iunfold hhInv at Hinv
  icases Hinv with ⟨Hinv, Hgaps⟩
  (try wp_auto)
  wp_apply wp_canonLocked hh c.hist' g.st.hist $$ [$Hinv $Hch] as %base ⟨Hinv, #Hbase⟩
  · ipureintro; exact Hchl
  iunfold hhGaps at Hgaps
  icases Hgaps with ⟨%mg, %G, Hg, HG⟩
  (try wp_auto)
  wp_join iprop(∃ (mg' : GoMap) (G' : GMap Loc GoSlice),
      hh_ptr ↦ hh ∗ structFieldRef histHashes go!"gaps" hh ↦ mg' ∗ mg' ↦$ G' ∗
      [∗map] b ↦ sl ∈ G', gapsOwn b sl) with [hh Hg HG]
      as ⟨%mg', %G', hh, Hg, HM, HMs⟩
  · (try wp_auto)
    wp_apply (wp_map_make1 (K := Loc) (V := GoSlice) _ _) as %m1 Hm1
    (try wp_auto)
    isplitr
    · ipureintro; rfl
    iexists m1, ∅
    iframe
    iapply BigSepM.bigSepM_empty.2
    itrivial
  · icases HG with (%Hnil | ⟨HM, HMs⟩)
    · exact absurd Hnil (by assumption)
    · iexists mg, G
      iframe
  (try wp_auto)
  wp_apply (wp_map_lookup1 _ _ mg' G' base (DFrac.own 1)) $$ [$HM] as HM
  ihave Hgb : (∃ ns : List Loc,
      ((G' !! base).getD (zero_val GoSlice)) ↦* ns ∗
      ownSliceCap Loc ((G' !! base).getD (zero_val GoSlice)) (DFrac.own 1) ∗
      ⌜g.st.hist.length + ns.length < 2 ^ 63⌝ ∗
      ([∗list] i ↦ n ∈ ns, histOwn n (g.st.hist ++ gapsL g.st.st g.st.hist.length (i + 1))) ∗
      (∀ sl' : GoSlice, gapsOwn base sl' -∗ [∗map] b ↦ sl ∈ <[base := sl']> G', gapsOwn b sl) : IProp GF)
      $$ [HMs]
  · cases hC : G' !! base with
    | none =>
      iexists []
      rw [Option.getD_none]
      isplitr
      · iapply (show ⊢ (zero_val GoSlice ↦* ([] : List Loc) : IProp GF) from ownSlice_nil _)
      isplitr
      · iapply (show ⊢ (ownSliceCap Loc (zero_val GoSlice) (DFrac.own 1) : IProp GF) from ownSliceCap_nil)
      isplitr
      · ipureintro; simpa using HL63
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      iintro %sl' Hsl'
      iapply (BigSepM.bigSepM_insert hC).2
      iframe
    | some sl0 =>
      simp only [Option.getD_some]
      icases (BigSepM.bigSepM_delete hC).1 $$ HMs with ⟨Hgo, Hrest⟩
      iunfold gapsOwn at Hgo
      icases Hgo with ⟨%ns, %hs, %s0, Hns, Hcap, #Hhs, %Hhs0, #Hl⟩
      ihave %Hhe := histOwn_agree_len base hs g.st.hist (by omega) Hchl $$ Hhs Hbase
      subst Hhe
      have Hs0 : s0 = g.st.st := by
        have := Hwf.2; rw [Hhs0.1] at this; exact Option.some.inj this
      subst Hs0
      iexists ns
      iframe
      isplitr
      · ipureintro; exact Hhs0.2
      isplitr
      · iexact Hl
      iintro %sl' Hsl'
      iapply BigSepM.bigSepM_insert_delete.2
      iframe
  icases Hgb with ⟨%ns0, Hns, Hcap, %Hns0, #Hl, Hback⟩
  (try wp_auto)
  ihave HJ : (∃ (gsl : GoSlice) (ns : List Loc), "g" ∷ g_ptr ↦ gsl ∗ "Hns" ∷ gsl ↦* ns ∗
      "Hcap" ∷ ownSliceCap Loc gsl (DFrac.own 1) ∗
      "Hl" ∷ ([∗list] i ↦ n ∈ ns, histOwn n (g.st.hist ++ gapsL g.st.st g.st.hist.length (i + 1))) ∗
      "Hinv" ∷ hhCanon hh ∗ "%Hb" ∷ ⌜g.st.hist.length + ns.length < 2 ^ 63⌝ : IProp GF)
      $$ [g Hns Hcap Hinv]
  · iexists _, ns0
    iframe
    iframe #
    ipureintro; exact Hns0
  wp_for HJ
  wp_if_destruct
  · ihave %Hgl := ownSlice_len $$ Hns
    icases Hl with #Hl
    have Hlt : ns.length + g.st.hist.length < uint.nat t := by
      have h1 : uint.Z c.st'.rv' < uint.Z t := by omega
      have h2 : uint.Z (t - c.st'.rv') = uint.Z t - uint.Z c.st'.rv' := by word
      rw [HL, Hgl.1]
      word
    (try wp_auto)
    wp_join iprop(∃ hv : Loc, h_ptr ↦ hv ∗ g_ptr ↦ gsl ∗ gsl ↦* ns ∗
        histOwn hv (g.st.hist ++ gapsL g.st.st g.st.hist.length ns.length)) with [h g Hns]
        as ⟨%hv, h, g, Hns, #Hhv⟩
    · (try wp_auto)
      have Hb' : 0 ≤ sint.Z (gsl.len - W64 1) ∧ sint.Z (gsl.len - W64 1) < sint.Z gsl.len := by
        constructor <;> word
      list_elem ns (sint.nat (gsl.len - W64 1)) as v
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z (gsl.len - W64 1)) ns _ v Hb'.1 $$ [Hns] as Hns
      · isplit
        · iexact Hns
        · ipureintro; exact Hv_lookup
      ihave #Hv := BigSepL.bigSepL_lookup Hv_lookup $$ Hl
      rw [show sint.nat (gsl.len - W64 1) + 1 = ns.length by word] at *
      (try wp_auto)
      isplitr
      · ipureintro; rfl
      iexists v
      iframe
      iframe #
    · have H0 : ns.length = 0 := by word
      iexists base
      iframe
      rw [H0]
      simp only [gapsL, List.range_zero, List.map_nil, List.append_nil]
      iexact Hbase
    have Hgn : (g.st.hist ++ gapsL g.st.st g.st.hist.length ns.length).length =
        g.st.hist.length + ns.length := by simp [gapsL]
    (try wp_auto)
    wp_apply wp_histLen hv _ $$ [$Hhv]
    (try wp_auto)
    wp_apply wp_histLen hv _ $$ [$Hhv]
    (try wp_auto)
    wp_apply wp_intern hh hv _ _
      ⟨g.st.st.items, W64 ((g.st.hist.length + ns.length + 1 : Nat) : Int)⟩ _ $$ [$Hinv $Hhv]
      as %c1 ⟨Hinv, #Hc1⟩
    · isplitr
      · iunfold storeOwn
        iframe #
        ipureintro; simp only [Hgn]; word
      · ipureintro; simp only [Hgn]; word
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [arrayLiteralSize1]
    wp_apply (wp_slice_append _ ns _ _ (DFrac.own 1)) $$ [$Hns $Hcap $Hl1] as %gsl' ⟨Hns', Hcap', -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists gsl', ns ++ [c1]
    iframe
    isplitr
    · iapply BigSepL.bigSepL_snoc.2
      isplitr
      · iexact Hl
      rw [gapsL_succ, ← List.append_assoc]
      iexact Hc1
    ipureintro; simp only [List.length_append, List.length_singleton]; omega
  · ihave %Hgl := ownSlice_len $$ Hns
    icases Hl with #Hl
    obtain ⟨J', hJ'⟩ : ∃ J', uint.nat t - g.st.hist.length = J' + 1 :=
      ⟨uint.nat t - g.st.hist.length - 1, by omega⟩
    have Hge : J' < ns.length := by
      have h1 : uint.Z c.st'.rv' < uint.Z t := by omega
      have h2 : uint.Z (t - c.st'.rv') = uint.Z t - uint.Z c.st'.rv' := by word
      rw [Hgl.1]
      word
    have Hidx : sint.nat (t - c.st'.rv' - W64 1) = J' := by
      have h1 : uint.Z c.st'.rv' < uint.Z t := by omega
      word
    (try wp_auto)
    wp_apply (wp_mapInsert _ mg' G' base gsl) $$ [$HM] as HM
    (try wp_auto)
    have Hb' : 0 ≤ sint.Z (t - c.st'.rv' - W64 1) ∧ sint.Z (t - c.st'.rv' - W64 1) < sint.Z gsl.len := by
      have h1 : uint.Z c.st'.rv' < uint.Z t := by omega
      constructor <;> word
    list_elem ns (sint.nat (t - c.st'.rv' - W64 1)) as n
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ _ ns _ n Hb'.1 $$ [Hns] as Hns
    · isplit
      · iexact Hns
      · ipureintro; exact Hn_lookup
    ihave #Hn := BigSepL.bigSepL_lookup Hn_lookup $$ Hl
    rw [Hidx, gapsL_succ, ← List.append_assoc] at *
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock _ (hhInv hh) $$ [$Hsync $Hmu $Hlk Hinv Hg HM Hback Hns Hcap]
    · iunfold hhInv
      iframe
      iunfold hhGaps
      iexists mg', _
      iframe
      iright
      iframe
      iapply Hback
      iunfold gapsOwn
      iexists ns, g.st.hist, g.st.st
      iframe
      iframe #
      ipureintro; exact ⟨Hwf.2, Hb⟩
    icases (histOwn_snoc n _ _).1 $$ Hn with ⟨%hn, #Hnp, #Hnst, %Hnn, -⟩
    iStructNamed Hnp
    (try wp_auto)
    iapply HΦ
    have Hsk : k8s_dist.skipToL g.st (uint.nat t) =
        ⟨⟨g.st.st.items, W64 ((g.st.hist.length + (J' + 1) : Nat) : Int)⟩,
          g.st.hist ++ gapsL g.st.st g.st.hist.length (J' + 1)⟩ := by
      unfold k8s_dist.skipToL
      rw [← Hwf.1, hJ']
      exact repeat_foreignL_gaps g.st Hwf (J' + 1) (by omega)
    rw [Hsk, gapsL_succ, ← List.append_assoc]
    simp only
    rw [show g.st.hist.length + (J' + 1) = g.st.hist.length + J' + 1 by omega]
    iframe #
    ipureintro
    simp only [List.length_append, List.length_singleton, gapsL, List.length_map, List.length_range]
    omega

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
