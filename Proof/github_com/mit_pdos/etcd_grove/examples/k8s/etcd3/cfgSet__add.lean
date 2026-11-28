/-
Lean-first (no Rocq counterpart).

The proof of `(*cfgSet).add`: the bucket map made if nil; `c`'s history made canonical; the bucket of
`c`'s key taken out of the map (or none), each of its configurations compared with `c` (`storeEqual`,
`pendEqual`): a match is `c`'s configuration, its history the key's (the bucket's facts) and so `c`'s
(`histOwn_agree_len`); otherwise `c` appended to the list and its index to the bucket, every bucket's
indices still into the longer list.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cfgSet__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histHashes__canonical
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeHash
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pendEqual

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

/-- A bucket's indices into the list `cs` (`cfgSetOwn`'s facts). -/
abbrev bucketIdx (cs : List mcfg) (k : ckey) (is : List w64) : Prop :=
  ∀ i ∈ is, 0 ≤ sint.Z i ∧ ∃ d, cs[sint.nat i]? = some d ∧ d.hist' = k.hist'

theorem bucketIdx_snoc (cs : List mcfg) (x : mcfg) (k : ckey) (is : List w64)
    (h : bucketIdx cs k is) : bucketIdx (cs ++ [x]) k is := by
  intro i hi
  obtain ⟨h0, d, hd, hk⟩ := h i hi
  refine ⟨h0, d, ?_, hk⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hd).1]
  exact hd

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- Every bucket's indices into a longer list. -/
theorem buckets_snoc (B : GMap ckey GoSlice) (cs : List mcfg) (x : mcfg) :
    ([∗map] k ↦ sl ∈ B, ∃ is : List w64, sl ↦* is ∗ ownSliceCap w64 sl (DFrac.own 1) ∗
      ⌜bucketIdx cs k is⌝) ⊢
    ([∗map] k ↦ sl ∈ B, ∃ is : List w64, sl ↦* is ∗ ownSliceCap w64 sl (DFrac.own 1) ∗
      ⌜bucketIdx (cs ++ [x]) k is⌝ : IProp GF) := by
  apply BigSepM.bigSepM_mono
  intro k sl _
  iintro ⟨%is, Hs, Hc, %Hi⟩
  iexists is
  iframe
  ipureintro; exact bucketIdx_snoc cs x k is Hi

theorem cfgSet.add.wp_proof
    (wp_canonical : histHashes.canonical.spec (GF := GF) (hG := hG))
    (wp_storeHash : storeHash.spec (GF := GF) (hG := hG))
    (wp_storeEqual : storeEqual.spec (GF := GF) (hG := hG))
    (wp_pendEqual : pendEqual.spec (GF := GF) (hG := hG)) :
    cfgSet.add.spec (GF := GF) (hG := hG) := by
  intro s hh gs c g
  wp_start as ⟨#Hhh, Hset, #Hc, %Hgs⟩
  iunfold cfgSetOwn at Hset
  icases Hset with ⟨%lsl, %mb, %cs, %B, Hsh, Hsl, Hsb, Hcs, Hcap, Hcg, %Hcsl, Hb⟩
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hcg
  (try wp_auto)
  wp_join iprop(∃ (mb' : GoMap) (B' : GMap ckey GoSlice),
      s_ptr ↦ s ∗ structFieldRef cfgSet go!"buckets" s ↦ mb' ∗ mb' ↦$ B' ∗
      [∗map] k ↦ sl ∈ B', ∃ is : List w64, sl ↦* is ∗ ownSliceCap w64 sl (DFrac.own 1) ∗
        ⌜bucketIdx cs k is⌝) with [s Hsb Hb]
      as ⟨%mb', %B', s, Hsb, HB, HBs⟩
  · (try wp_auto)
    wp_apply (wp_map_make1 (K := ckey) (V := GoSlice) _ _) as %m1 Hm1
    (try wp_auto)
    isplitr
    · ipureintro; rfl
    iexists m1, ∅
    iframe
    iapply BigSepM.bigSepM_empty.2
    itrivial
  · icases Hb with (%Hnil | ⟨HB, HBs⟩)
    · exact absurd Hnil.1 (by assumption)
    · iexists mb, B
      iframe
  iunfold cfgOwn at Hc
  icases Hc with ⟨#Hcst, #Hch, #Hcp, %Hchl⟩
  (try wp_auto)
  wp_apply wp_canonical hh c.hist' g.st.hist $$ [$Hhh $Hch] as %h' #Hh'
  · ipureintro; exact Hchl
  (try wp_auto)
  wp_apply wp_storeHash c.st' g.st.st $$ [$Hcst] as %hv -
  (try wp_auto)
  wp_apply (wp_map_lookup1 _ _ mb' B' _ (DFrac.own 1)) $$ [$HB] as HB
  rename_i iu_ptr
  irename: (iu_ptr ↦ zero_val w64) => iu
  ihave %Hcsl' := ownSlice_len $$ Hcs
  ihave Hbk : (∃ is : List w64,
      ((B' !! ckey.mk h' c.st'.rv' c.pend'.len hv).getD (zero_val GoSlice)) ↦* is ∗
      ownSliceCap w64 ((B' !! ckey.mk h' c.st'.rv' c.pend'.len hv).getD (zero_val GoSlice)) (DFrac.own 1) ∗
      ⌜bucketIdx cs (ckey.mk h' c.st'.rv' c.pend'.len hv) is⌝ ∗
      ((∀ sl' : GoSlice, (∃ is' : List w64, sl' ↦* is' ∗ ownSliceCap w64 sl' (DFrac.own 1) ∗
          ⌜bucketIdx (cs ++ [⟨c.st', c.pend', h'⟩]) (ckey.mk h' c.st'.rv' c.pend'.len hv) is'⌝) -∗
        [∗map] k ↦ sl ∈ <[ckey.mk h' c.st'.rv' c.pend'.len hv := sl']> B', ∃ is : List w64, sl ↦* is ∗
          ownSliceCap w64 sl (DFrac.own 1) ∗ ⌜bucketIdx (cs ++ [⟨c.st', c.pend', h'⟩]) k is⌝) ∧
       ((∃ is' : List w64, ((B' !! ckey.mk h' c.st'.rv' c.pend'.len hv).getD (zero_val GoSlice)) ↦* is' ∗
          ownSliceCap w64 ((B' !! ckey.mk h' c.st'.rv' c.pend'.len hv).getD (zero_val GoSlice)) (DFrac.own 1) ∗
          ⌜bucketIdx cs (ckey.mk h' c.st'.rv' c.pend'.len hv) is'⌝) -∗
        [∗map] k ↦ sl ∈ B', ∃ is : List w64, sl ↦* is ∗
          ownSliceCap w64 sl (DFrac.own 1) ∗ ⌜bucketIdx cs k is⌝)) : IProp GF) $$ [HBs]
  · cases hC : B' !! ckey.mk h' c.st'.rv' c.pend'.len hv with
    | none =>
      iexists []
      rw [Option.getD_none]
      isplitr
      · iapply (show ⊢ (zero_val GoSlice ↦* ([] : List w64) : IProp GF) from ownSlice_nil _)
      isplitr
      · iapply (show ⊢ (ownSliceCap w64 (zero_val GoSlice) (DFrac.own 1) : IProp GF) from ownSliceCap_nil)
      isplitr
      · ipureintro; intro i hi; simp at hi
      isplit
      · iintro %sl' Hsl'
        iapply (BigSepM.bigSepM_insert hC).2
        iframe
        iapply buckets_snoc
        iexact HBs
      · iintro -
        iexact HBs
    | some sl0 =>
      simp only [Option.getD_some]
      icases (BigSepM.bigSepM_delete hC).1 $$ HBs with ⟨⟨%is, Hns, Hcap, %Hi⟩, Hrest⟩
      iexists is
      iframe
      isplitr
      · ipureintro; exact Hi
      isplit
      · iintro %sl' Hsl'
        iapply BigSepM.bigSepM_insert_delete.2
        iframe
        iapply buckets_snoc
        iexact Hrest
      · iintro Hsl'
        iapply (BigSepM.bigSepM_delete hC).2
        iframe
  icases Hbk with ⟨%is, Hns, Hbcap, %Hbi, Hback⟩
  ihave %Hlns := ownSlice_len $$ Hns
  ihave HJ : (∃ (j : w64) (iv : w64), "i" ∷ i_ptr ↦ j ∗ "iu" ∷ iu_ptr ↦ iv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j⌝ : IProp GF) $$ [i iu]
  · iexists W64 0, _
    iframe
    ipureintro; word
  wp_for HJ
  wp_if_destruct
  · have Hb' := And.intro Hj Hif
    list_elem is (sint.nat j) as v
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z j) is _ v Hj $$ [Hns] as Hns
    · isplit
      · iexact Hns
      · ipureintro; exact Hv_lookup
    obtain ⟨Hv0, d, Hd, Hdk⟩ := Hbi v (List.mem_of_getElem? Hv_lookup)
    have Hdi : sint.nat v < cs.length := (List.getElem?_eq_some_iff.1 Hd).1
    obtain ⟨gd, Hgd⟩ : ∃ gd, gs[sint.nat v]? = some gd :=
      ⟨gs[sint.nat v]'(by omega), List.getElem?_eq_getElem _⟩
    icases BigSepL2.bigSepL2_lookup_acc Hd Hgd $$ Hcg with ⟨#Hdc, Hcgb⟩
    ihave Hcg := Hcgb $$ Hdc
    iunfold cfgOwn at Hdc
    icases Hdc with ⟨#Hdst, #Hdh, #Hdp, %Hdhl⟩
    (try wp_auto)
    have Hb2 : 0 ≤ sint.Z v ∧ sint.Z v < sint.Z lsl.len := ⟨Hv0, by have := Hcsl'.1; have := Hcsl'.2; word⟩
    simp only [Hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index lsl (sint.Z v) cs _ d Hv0 $$ [Hcs] as Hcs
    · isplit
      · iexact Hcs
      · ipureintro; exact Hd
    (try wp_auto)
    wp_apply wp_storeEqual d.st' c.st' gd.st.st g.st.st $$ [$Hdst $Hcst]
    wp_if_destruct
    · (try wp_auto)
      wp_apply wp_pendEqual d.pend' c.pend' gd.pend g.pend $$ [$Hdp $Hcp]
      wp_if_destruct
      · (try wp_auto)
        wp_for_post
        (try wp_auto)
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only at Hdk
        rw [Hdk]
        ihave %Hhe := histOwn_agree_len h' gd.st.hist g.st.hist Hdhl Hchl $$ Hdh Hh'
        isplitl
        · iunfold cfgSetOwn
          iexists lsl, mb', cs, B'
          iframe
          isplitr
          · ipureintro; exact Hcsl
          iright
          iframe
          icases Hback with ⟨-, Hb2⟩
          iapply Hb2
          iexists is
          iframe
          ipureintro; exact Hbi
        · ipureintro
          have Hge : gd = g := by
            obtain ⟨⟨a, b⟩, p⟩ := gd
            obtain ⟨⟨a', b'⟩, p'⟩ := g
            simp_all
          rw [← Hge]
          exact List.mem_of_getElem? Hgd
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, _
        iframe
        ipureintro; word
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, _
      iframe
      ipureintro; word
  · (try wp_auto)
    wp_apply (wp_map_lookup1 _ _ mb' B' (ckey.mk h' c.st'.rv' c.pend'.len hv) (DFrac.own 1)) $$ [$HB] as HB
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [arrayLiteralSize1]
    wp_apply (wp_slice_append _ is _ _ (DFrac.own 1)) $$ [$Hns $Hbcap $Hl1] as %sl' ⟨Hns', Hcap', -⟩
    (try wp_auto)
    wp_apply (wp_mapInsert _ mb' B' _ sl') $$ [$HB] as HB
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l2 ⟨Hl2, -⟩
    simp only [arrayLiteralSize1]
    wp_apply (wp_slice_append _ cs _ _ (DFrac.own 1)) $$ [$Hcs $Hcap $Hl2] as %lsl' ⟨Hcs', Hcap2', -⟩
    (try wp_auto)
    iapply HΦ
    simp only [↓reduceIte]
    iunfold cfgSetOwn
    iexists lsl', mb', cs ++ [⟨c.st', c.pend', h'⟩], _
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_singleton.2
      iunfold cfgOwn
      iframe #
      ipureintro; exact Hchl
    isplitr
    · ipureintro; simp only [List.length_append, List.length_singleton]; omega
    iright
    iframe
    icases Hback with ⟨Hb1, -⟩
    iapply Hb1
    iexists is ++ [lsl.len]
    iframe
    ipureintro
    intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · exact bucketIdx_snoc cs _ _ is Hbi i hi
    · simp only [List.mem_singleton] at hi
      subst hi
      refine ⟨Hcsl'.2, ⟨c.st', c.pend', h'⟩, ?_, rfl⟩
      rw [← Hcsl'.1]
      simp

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
