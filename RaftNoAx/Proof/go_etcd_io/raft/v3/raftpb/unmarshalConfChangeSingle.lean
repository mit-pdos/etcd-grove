/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/unmarshalConfChangeSingle.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.unmarshalConfChangeSingle
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeEnum
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeVarint
public import RaftNoAx.Proof.go_etcd_io.raft.v3.raftpb.CloneLeaf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- An optional field's cell as a decoder leaves it: `nil`, or a fresh pointer to the value. -/
def ccOptCellW {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) : Option V → IProp GF
  | none => iprop(⌜p = null⌝)
  | some v => iprop(p ↦ v)

theorem ccOptCellW_persist {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (o : Option V)
    (E : CoPset) : ccOptCellW (GF := GF) p o ⊢ |={E}=> optCell p o := by
  cases o with
  | none => simp only [ccOptCellW, optCell]; iintro %H; imodintro; ipureintro; exact H
  | some v =>
    simp only [ccOptCellW, optCell]
    iintro H
    ipersist H
    imodintro; iexact H

theorem raftpb.unmarshalConfChangeSingle.wp_proof
    (wp_consumeEnum : raftpb.consumeEnum.spec (GF := GF) (hG := hG))
    (wp_consumeVarint : raftpb.consumeVarint.spec (GF := GF) (hG := hG)) :
    raftpb.unmarshalConfChangeSingle.spec (GF := GF) (hG := hG) := by
  intro d dq bs
  wp_start as Hd
  ihave %Hlen := ownSlice_len $$ Hd
  wp_auto
  ihave %Hsn := typedPointsto_not_null $$ «$r0»
  iStructNamed «$r0»
  have hlenZ : sint.Z d.len = (bs.length : Int) := by word
  have hz0 : sint.Z (W64 0) = 0 := rfl
  have hn0 : sint.nat (W64 0) = 0 := rfl
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (i1 : w64) (o1 : Option w32) (pt : Loc),
        "i" ∷ i_ptr ↦ i1 ∗ "HT" ∷ «$r0_ptr».[raftpb.ConfChangeSingle, go!"Type"] ↦ pt ∗
        "data" ∷ data_ptr ↦ d ∗ "s" ∷ s_ptr ↦ «$r0_ptr» ∗
        "$res0" ∷ «$res0_ptr» ↦ zero_val Loc ∗ "$res1" ∷ «$res1_ptr» ↦ zero_val Bool ∗
        "cT" ∷ ccOptCellW pt o1 ∗ "Hd" ∷ d ↦*{dq} bs ∗
        "%H1" ∷ ⌜ccOptField bs 0 (W8 8) ccEnumL = some (o1, sint.nat i1) ∧ 0 ≤ sint.Z i1 ∧
          sint.Z i1 ≤ bs.length⌝) ∨
      (⌜v = returnVal #()⌝ ∗ "Hd" ∷ d ↦*{dq} bs ∗ "$res0" ∷ «$res0_ptr» ↦ null ∗
        "$res1" ∷ «$res1_ptr» ↦ false ∗ "%Hn" ∷ ⌜ccDecodeSingle bs = none⌝)))
    at next with [i Type' Hd «$res0» «$res1» data s]
  · wp_if_destruct
    · -- 0 < len
      have h0 : 0 < bs.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, bs[0]? = some c := ⟨_, List.getElem?_eq_getElem h0⟩
      simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z d.len from ⟨by decide, by omega⟩]
      wp_apply wp_load_slice_index d (sint.Z (W64 0)) bs dq c (by decide) $$ [Hd] as Hd
      · iframe; ipureintro; exact hc
      wp_if_destruct
      · have h1n : sint.nat (W64 0 + W64 1) = 1 := rfl
        have h1z : sint.Z (W64 0 + W64 1) = 1 := rfl
        wp_apply wp_consumeEnum d dq bs (W64 0 + W64 1) (by decide) (by omega) $$ [$Hd]
          as %v %j %ok ⟨Hd, %Hr⟩
        have hO : ccOptField bs 0 (W8 8) ccEnumL = (ccEnumL bs 1).map (fun p => (some p.1, p.2)) := by
          unfold ccOptField; rw [ite_eq_left hc]
        rw [h1n] at Hr
        cases he : ccEnumL bs 1 with
        | none =>
          rw [he] at Hr
          subst Hr
          wp_auto
          iright
          iframe
          ipureintro
          unfold ccDecodeSingle
          rw [hO, he]; exact ⟨rfl, rfl⟩
        | some p =>
          rw [he] at Hr
          obtain ⟨v', j'⟩ := p
          simp only at Hr
          obtain ⟨rfl, rfl, hj⟩ := Hr
          have hb := ccEnumL_bound he
          wp_auto
          ileft
          isplitr
          · ipureintro; rfl
          iexists j, some v, _
          simp only [ccOptCellW]
          iframe
          ipureintro
          refine ⟨?_, by omega, by omega⟩
          rw [hO, he, show sint.nat j = j' from by
            rw [show sint.nat j = (sint.Z j).toNat from rfl, hj]; simp]
          rfl
      · ileft
        iframe
        iexists none
        simp only [ccOptCellW]
        isplitr
        · ipureintro; rfl
        ipureintro
        refine ⟨?_, by decide, by omega⟩
        rw [ccOptField_none]
        · rfl
        · rw [hc]; simpa using Hif
    · ileft
      iframe
      iexists none
      simp only [ccOptCellW]
      isplitr
      · ipureintro; rfl
      ipureintro
      refine ⟨?_, by decide, by omega⟩
      rw [ccOptField_none]
      · rfl
      · rw [List.getElem?_eq_none (by omega)]; simp
  iintro (⟨%Hv, %i1, %o1, %pt, i, HT, data, s, «$res0», «$res1», cT, Hd, %H1⟩ |
    ⟨%Hv, Hd, «$res0», «$res1», %Hn⟩) <;> subst Hv
  rotate_left
  · wp_auto
    iapply HΦ
    rw [Hn]
    iframe
    ipureintro; rfl
  have hi1 : (sint.nat i1 : Int) = sint.Z i1 := by word
  wp_auto
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (i2 : w64) (o2 : Option w64) (pn : Loc),
        "i" ∷ i_ptr ↦ i2 ∗ "HN" ∷ «$r0_ptr».[raftpb.ConfChangeSingle, go!"NodeId"] ↦ pn ∗
        "data" ∷ data_ptr ↦ d ∗ "s" ∷ s_ptr ↦ «$r0_ptr» ∗
        "$res0" ∷ «$res0_ptr» ↦ zero_val Loc ∗ "$res1" ∷ «$res1_ptr» ↦ zero_val Bool ∗
        "cN" ∷ ccOptCellW pn o2 ∗ "Hd" ∷ d ↦*{dq} bs ∗
        "%H2" ∷ ⌜ccOptField bs (sint.nat i1) (W8 16) ccVarintL = some (o2, sint.nat i2) ∧
          0 ≤ sint.Z i2 ∧ sint.Z i2 ≤ bs.length⌝) ∨
      (⌜v = returnVal #()⌝ ∗ "Hd" ∷ d ↦*{dq} bs ∗ "$res0" ∷ «$res0_ptr» ↦ null ∗
        "$res1" ∷ «$res1_ptr» ↦ false ∗ "%Hn" ∷ ⌜ccDecodeSingle bs = none⌝)))
    at next with [i NodeId Hd «$res0» «$res1» data s]
  · wp_if_destruct
    · have hlt : sint.nat i1 < bs.length := by omega
      have hi1' : sint.Z (i1 + W64 1) = sint.Z i1 + 1 := by word
      have hi1n : sint.nat (i1 + W64 1) = sint.nat i1 + 1 := by word
      obtain ⟨c, hc⟩ : ∃ c, bs[sint.nat i1]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
      simp only [show 0 ≤ sint.Z i1 ∧ sint.Z i1 < sint.Z d.len from ⟨H1.2.1, by omega⟩]
      wp_apply wp_load_slice_index d (sint.Z i1) bs dq c H1.2.1 $$ [Hd] as Hd
      · iframe; ipureintro; exact hc
      wp_if_destruct
      · wp_apply wp_consumeVarint d dq bs (i1 + W64 1) (by omega) (by omega) $$ [$Hd]
          as %v %j %ok ⟨Hd, %Hr⟩
        have hO : ccOptField bs (sint.nat i1) (W8 16) ccVarintL =
            (ccVarintL bs (sint.nat i1 + 1)).map (fun p => (some p.1, p.2)) := by
          unfold ccOptField; rw [ite_eq_left hc]
        rw [hi1n] at Hr
        cases he : ccVarintL bs (sint.nat i1 + 1) with
        | none =>
          rw [he] at Hr
          subst Hr
          wp_auto
          iright
          iframe
          ipureintro
          unfold ccDecodeSingle
          rw [H1.1]
          simp only [Option.bind_some]
          rw [hO, he]; simp
        | some p =>
          rw [he] at Hr
          obtain ⟨v', j'⟩ := p
          simp only at Hr
          obtain ⟨rfl, rfl, hj⟩ := Hr
          have hb := ccVarintL_bound he
          wp_auto
          ileft
          isplitr
          · ipureintro; rfl
          iexists j, some v, _
          simp only [ccOptCellW]
          iframe
          ipureintro
          refine ⟨?_, by omega, by omega⟩
          rw [hO, he, show sint.nat j = j' from by
            rw [show sint.nat j = (sint.Z j).toNat from rfl, hj]; simp]
          rfl
      · ileft
        iframe
        iexists none
        simp only [ccOptCellW]
        isplitr
        · ipureintro; rfl
        ipureintro
        refine ⟨?_, H1.2.1, H1.2.2⟩
        rw [ccOptField_none _ _ _ _ (by rw [hc]; simpa using Hif)]
    · ileft
      iframe
      iexists none
      simp only [ccOptCellW]
      isplitr
      · ipureintro; rfl
      ipureintro
      refine ⟨?_, H1.2.1, H1.2.2⟩
      rw [ccOptField_none _ _ _ _ (by rw [List.getElem?_eq_none (by omega)]; simp)]
  iintro (⟨%Hv, %i2, %o2, %pn, i, HN, data, s, «$res0», «$res1», cN, Hd, %H2⟩ |
    ⟨%Hv, Hd, «$res0», «$res1», %Hn⟩) <;> subst Hv
  rotate_left
  · wp_auto
    iapply HΦ
    rw [Hn]
    iframe
    ipureintro; rfl
  have hi2 : (sint.nat i2 : Int) = sint.Z i2 := by word
  imod ccOptCellW_persist pt o1 ⊤ $$ cT with #cT
  imod ccOptCellW_persist pn o2 ⊤ $$ cN with #cN
  ipersist HT
  ipersist HN
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.ConfChangeSingle «$r0_ptr» _ _ slice.nil [] ⊤ (ufWire_nil _)
    $$ [state sizeCache unknownFields Hnil] with #Hpbm
  · iframe
  wp_auto
  have hD : ccDecodeSingle bs = if sint.nat i2 = bs.length then
      some ⟨o1.getD (W32 0), o2.getD (W64 0)⟩ else none := by
    unfold ccDecodeSingle
    rw [H1.1]
    simp only [Option.bind_some]
    rw [H2.1]
    simp only [Option.bind_some]
  wp_if_destruct
  · iapply HΦ
    rw [hD, ite_eq_left Hlen.1.symm]
    iframe
    isplitr
    · ipureintro; rfl
    unfold ccsRO ccsPts
    iexists pt, pn, []
    isplitr
    · ipureintro; exact Hsn
    ihave #HcT : (cellRO pt (o1.getD (W32 0)) : IProp GF) $$ [cT]
    · rw [show W32 0 = zero_val w32 from rfl]; iapply (nx_optCell_cellRO pt o1); iexact cT
    ihave #HcN : (cellRO pn (o2.getD (W64 0)) : IProp GF) $$ [cN]
    · rw [show W64 0 = zero_val w64 from rfl]; iapply (nx_optCell_cellRO pn o2); iexact cN
    simp only
    iframe HT HN Hpbm HcT HcN
  · have hne : sint.nat i2 ≠ bs.length := fun h => Hif (by word)
    iapply HΦ
    rw [hD, ite_eq_right hne]
    iframe
    ipureintro; rfl
