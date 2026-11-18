/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/UnmarshalConfChangeV1.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`).
-/
module

public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.UnmarshalConfChangeV1
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeVarint
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeEnum
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeBytes
public import RaftNoAx.Proof.go_etcd_io.raft.v3.raftpb.unmarshalConfChangeSingle

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

/-- A bytes field as a decoder leaves it: `nil`, or a fresh slice holding the bytes. -/
def ccOptBytesW (q : GoSlice) : Option (List w8) → IProp GF
  | none => iprop(⌜q = slice.nil⌝)
  | some v => iprop(q ↦* v)

theorem ccOptBytesW_persist (q : GoSlice) (o : Option (List w8)) (E : CoPset) :
    ccOptBytesW (GF := GF) q o ⊢ |={E}=> q ↦*□ o.getD [] := by
  cases o with
  | none =>
    simp only [ccOptBytesW, Option.getD_none]
    iintro %H
    subst H
    ihave Hn : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod (ownSlice_persist _ _) $$ Hn with Hn
    imodintro; iexact Hn
  | some v =>
    simp only [ccOptBytesW, Option.getD_some]
    iintro H
    imod (ownSlice_persist _ _) $$ H with H
    imodintro; iexact H

theorem ccV1_combine (p : Loc) (hp : p ≠ null) (st : google_golang_org.protobuf.internal.impl.MessageState)
    (pt pn : Loc) (cs : GoSlice) (pi : Loc) (us : GoSlice) (sc : w32) :
    (p.[raftpb.ConfChange, go!"state"] ↦ st ∗ p.[raftpb.ConfChange, go!"Type"] ↦ pt ∗
      p.[raftpb.ConfChange, go!"NodeId"] ↦ pn ∗ p.[raftpb.ConfChange, go!"Context"] ↦ cs ∗
      p.[raftpb.ConfChange, go!"Id"] ↦ pi ∗ p.[raftpb.ConfChange, go!"unknownFields"] ↦ us ∗
      p.[raftpb.ConfChange, go!"sizeCache"] ↦ sc : IProp GF) ⊢
    ∃ x' : raftpb.ConfChange, p ↦ x' := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7⟩
  iexists raftpb.ConfChange.mk st pt pn cs pi us sc
  iapply typedPointsto_combine _ _ _ hp
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem raftpb.UnmarshalConfChangeV1.wp_proof
    (wp_consumeVarint : raftpb.consumeVarint.spec (GF := GF) (hG := hG))
    (wp_consumeEnum : raftpb.consumeEnum.spec (GF := GF) (hG := hG))
    (wp_consumeBytes : raftpb.consumeBytes.spec (GF := GF) (hG := hG)) :
    raftpb.UnmarshalConfChangeV1.spec (GF := GF) (hG := hG) := by
  intro d bs dq p x
  wp_start as ⟨Hd, Hp⟩
  ihave #Hfact : iprop(∃ e : GoInterface,
      (globalAddr go_etcd_io.raft.v3.raftpb.errDecodeConfChange ↦□ e : IProp GF) ∗
      ⌜e ≠ interface.nil⌝) $$ []
  · iapply (isPkgInit_access (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb).trans sep_elim_right $$ Hpkg
  icases Hfact with ⟨%err, #Herr, %Herrn⟩
  ihave %Hlen := ownSlice_len $$ Hd
  ihave %Hpn := typedPointsto_not_null $$ Hp
  wp_auto
  have hlenZ : sint.Z d.len = (bs.length : Int) := by word
  have hz0 : sint.Z (W64 0) = 0 := rfl
  have hn0 : sint.nat (W64 0) = 0 := rfl
  iStructNamed Hp
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (i1 : w64) (o1 : Option w64) (q1 : Loc),
        "i" ∷ i_ptr ↦ i1 ∗ "Id" ∷ p.[raftpb.ConfChange, go!"Id"] ↦ q1 ∗
        "c1" ∷ ccOptCellW q1 o1 ∗ "Hd" ∷ d ↦*{dq} bs ∗ "c" ∷ c_ptr ↦ p ∗ "data" ∷ data_ptr ↦ d ∗
        "$res0" ∷ «$res0_ptr» ↦ GoInterface.nil ∗
        "%H1" ∷ ⌜ccOptField bs 0 (W8 8) ccVarintL = some (o1, sint.nat i1) ∧ 0 ≤ sint.Z i1 ∧
          sint.Z i1 ≤ bs.length⌝) ∨
      (⌜v = returnVal #()⌝ ∗ "Hd" ∷ d ↦*{dq} bs ∗ "$res0" ∷ «$res0_ptr» ↦ err ∗
        "Id" ∷ p.[raftpb.ConfChange, go!"Id"] ↦ (zero_val raftpb.ConfChange).Id' ∗ "%Hn" ∷ ⌜ccDecodeV1 bs = none⌝)))
    at next with [i Id Hd c data «$res0»]
  · wp_if_destruct
    · -- in range
      have h0 : 0 < bs.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, bs[0]? = some c := ⟨_, List.getElem?_eq_getElem h0⟩
      simp only [show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z d.len from ⟨by decide, by omega⟩]
      wp_apply wp_load_slice_index d (sint.Z (W64 0)) bs dq c (by decide) $$ [Hd] as Hd
      · iframe; ipureintro; exact hc
      have hin : sint.nat (W64 0 + W64 1) = 0 + 1 := rfl
      have hiz : sint.Z (W64 0 + W64 1) = 1 := rfl
      have hiZ0 : 0 ≤ sint.Z (W64 0 + W64 1) := by decide
      have hiZ1 : sint.Z (W64 0 + W64 1) ≤ bs.length := by omega
      have hcI : bs[0]? = some c := hc
      wp_if_destruct
      · -- the tag
        wp_apply wp_consumeVarint d dq bs (W64 0 + W64 1) hiZ0 hiZ1 $$ [$Hd] as %v %j %ok ⟨Hd, %Hr⟩
        have hO : ccOptField bs 0 (W8 8) ccVarintL =
            (ccVarintL bs (0 + 1)).map (fun p => (some p.1, p.2)) := by
          unfold ccOptField; rw [ite_eq_left hcI]
        rw [hin] at Hr
        cases he : ccVarintL bs (0 + 1) with
        | none =>
          rw [he] at Hr
          subst Hr
          wp_auto
          iright
          iframe
          ipureintro
          unfold ccDecodeV1
          rw [hO, he]; simp
        | some pr =>
          rw [he] at Hr
          obtain ⟨v', j'⟩ := pr
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
        isplitr
        · ipureintro; first | rfl | trivial
        iframe
        iexists none
        simp only [ccOptCellW]
        isplitr
        · ipureintro; rfl
        ipureintro
        refine ⟨?_, by decide, by omega⟩
        rw [ccOptField_none _ _ _ _ (by rw [hc]; simpa using Hif)]
        try rfl
    · ileft
      isplitr
      · ipureintro; first | rfl | trivial
      iframe
      iexists none
      simp only [ccOptCellW]
      isplitr
      · ipureintro; rfl
      ipureintro
      refine ⟨?_, by decide, by omega⟩
      rw [ccOptField_none _ _ _ _ (by rw [List.getElem?_eq_none (by omega)]; simp)]
      try rfl
  iintro (⟨%Hv, %i1, %o1, %q1, i, Id, c1, Hd, c, data, «$res0», %H1⟩ |
    ⟨%Hv, Hd, «$res0», Id, %Hn⟩) <;> subst Hv
  rotate_left
  · wp_auto
    iapply HΦ
    rw [Hn]
    iframe
    isplitr
    · ipureintro; exact Herrn
    iapply ccV1_combine p Hpn
    iframe
  have hik : (sint.nat i1 : Int) = sint.Z i1 := by word
  wp_auto
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (i2 : w64) (o2 : Option w32) (q2 : Loc),
        "i" ∷ i_ptr ↦ i2 ∗ "Type'" ∷ p.[raftpb.ConfChange, go!"Type"] ↦ q2 ∗
        "c2" ∷ ccOptCellW q2 o2 ∗ "Hd" ∷ d ↦*{dq} bs ∗ "c" ∷ c_ptr ↦ p ∗ "data" ∷ data_ptr ↦ d ∗
        "$res0" ∷ «$res0_ptr» ↦ GoInterface.nil ∗
        "%H2" ∷ ⌜ccOptField bs (sint.nat i1) (W8 16) ccEnumL = some (o2, sint.nat i2) ∧ 0 ≤ sint.Z i2 ∧
          sint.Z i2 ≤ bs.length⌝) ∨
      (⌜v = returnVal #()⌝ ∗ "Hd" ∷ d ↦*{dq} bs ∗ "$res0" ∷ «$res0_ptr» ↦ err ∗
        "Type'" ∷ p.[raftpb.ConfChange, go!"Type"] ↦ (zero_val raftpb.ConfChange).Type' ∗ "%Hn" ∷ ⌜ccDecodeV1 bs = none⌝)))
    at next with [i Type' Hd c data «$res0»]
  · wp_if_destruct
    · -- in range
      have hlt : sint.nat i1 < bs.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, bs[sint.nat i1]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
      simp only [show 0 ≤ sint.Z i1 ∧ sint.Z i1 < sint.Z d.len from ⟨H1.2.1, by omega⟩]
      wp_apply wp_load_slice_index d (sint.Z i1) bs dq c H1.2.1 $$ [Hd] as Hd
      · iframe; ipureintro; exact hc
      have hin : sint.nat (i1 + W64 1) = sint.nat i1 + 1 := by word
      have hiZ0 : 0 ≤ sint.Z (i1 + W64 1) := by word
      have hiZ1 : sint.Z (i1 + W64 1) ≤ bs.length := by word
      have hcI : bs[sint.nat i1]? = some c := hc
      wp_if_destruct
      · -- the tag
        wp_apply wp_consumeEnum d dq bs (i1 + W64 1) hiZ0 hiZ1 $$ [$Hd] as %v %j %ok ⟨Hd, %Hr⟩
        have hO : ccOptField bs (sint.nat i1) (W8 16) ccEnumL =
            (ccEnumL bs (sint.nat i1 + 1)).map (fun p => (some p.1, p.2)) := by
          unfold ccOptField; rw [ite_eq_left hcI]
        rw [hin] at Hr
        cases he : ccEnumL bs (sint.nat i1 + 1) with
        | none =>
          rw [he] at Hr
          subst Hr
          wp_auto
          iright
          iframe
          ipureintro
          unfold ccDecodeV1
          rw [H1.1]; simp only [Option.bind_some]; rw [hO, he]; simp
        | some pr =>
          rw [he] at Hr
          obtain ⟨v', j'⟩ := pr
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
        isplitr
        · ipureintro; first | rfl | trivial
        iframe
        iexists none
        simp only [ccOptCellW]
        isplitr
        · ipureintro; rfl
        ipureintro
        refine ⟨?_, H1.2.1, H1.2.2⟩
        rw [ccOptField_none _ _ _ _ (by rw [hc]; simpa using Hif)]
        try rfl
    · ileft
      isplitr
      · ipureintro; first | rfl | trivial
      iframe
      iexists none
      simp only [ccOptCellW]
      isplitr
      · ipureintro; rfl
      ipureintro
      refine ⟨?_, H1.2.1, H1.2.2⟩
      rw [ccOptField_none _ _ _ _ (by rw [List.getElem?_eq_none (by omega)]; simp)]
      try rfl
  iintro (⟨%Hv, %i2, %o2, %q2, i, Type', c2, Hd, c, data, «$res0», %H2⟩ |
    ⟨%Hv, Hd, «$res0», Type', %Hn⟩) <;> subst Hv
  rotate_left
  · wp_auto
    iapply HΦ
    rw [Hn]
    iframe
    isplitr
    · ipureintro; exact Herrn
    iapply ccV1_combine p Hpn
    iframe
  have hik : (sint.nat i2 : Int) = sint.Z i2 := by word
  wp_auto
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (i3 : w64) (o3 : Option w64) (q3 : Loc),
        "i" ∷ i_ptr ↦ i3 ∗ "NodeId" ∷ p.[raftpb.ConfChange, go!"NodeId"] ↦ q3 ∗
        "c3" ∷ ccOptCellW q3 o3 ∗ "Hd" ∷ d ↦*{dq} bs ∗ "c" ∷ c_ptr ↦ p ∗ "data" ∷ data_ptr ↦ d ∗
        "$res0" ∷ «$res0_ptr» ↦ GoInterface.nil ∗
        "%H3" ∷ ⌜ccOptField bs (sint.nat i2) (W8 24) ccVarintL = some (o3, sint.nat i3) ∧ 0 ≤ sint.Z i3 ∧
          sint.Z i3 ≤ bs.length⌝) ∨
      (⌜v = returnVal #()⌝ ∗ "Hd" ∷ d ↦*{dq} bs ∗ "$res0" ∷ «$res0_ptr» ↦ err ∗
        "NodeId" ∷ p.[raftpb.ConfChange, go!"NodeId"] ↦ (zero_val raftpb.ConfChange).NodeId' ∗ "%Hn" ∷ ⌜ccDecodeV1 bs = none⌝)))
    at next with [i NodeId Hd c data «$res0»]
  · wp_if_destruct
    · -- in range
      have hlt : sint.nat i2 < bs.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, bs[sint.nat i2]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
      simp only [show 0 ≤ sint.Z i2 ∧ sint.Z i2 < sint.Z d.len from ⟨H2.2.1, by omega⟩]
      wp_apply wp_load_slice_index d (sint.Z i2) bs dq c H2.2.1 $$ [Hd] as Hd
      · iframe; ipureintro; exact hc
      have hin : sint.nat (i2 + W64 1) = sint.nat i2 + 1 := by word
      have hiZ0 : 0 ≤ sint.Z (i2 + W64 1) := by word
      have hiZ1 : sint.Z (i2 + W64 1) ≤ bs.length := by word
      have hcI : bs[sint.nat i2]? = some c := hc
      wp_if_destruct
      · -- the tag
        wp_apply wp_consumeVarint d dq bs (i2 + W64 1) hiZ0 hiZ1 $$ [$Hd] as %v %j %ok ⟨Hd, %Hr⟩
        have hO : ccOptField bs (sint.nat i2) (W8 24) ccVarintL =
            (ccVarintL bs (sint.nat i2 + 1)).map (fun p => (some p.1, p.2)) := by
          unfold ccOptField; rw [ite_eq_left hcI]
        rw [hin] at Hr
        cases he : ccVarintL bs (sint.nat i2 + 1) with
        | none =>
          rw [he] at Hr
          subst Hr
          wp_auto
          iright
          iframe
          ipureintro
          unfold ccDecodeV1
          rw [H1.1]; simp only [Option.bind_some]; rw [H2.1]; simp only [Option.bind_some]; rw [hO, he]; simp
        | some pr =>
          rw [he] at Hr
          obtain ⟨v', j'⟩ := pr
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
        isplitr
        · ipureintro; first | rfl | trivial
        iframe
        iexists none
        simp only [ccOptCellW]
        isplitr
        · ipureintro; rfl
        ipureintro
        refine ⟨?_, H2.2.1, H2.2.2⟩
        rw [ccOptField_none _ _ _ _ (by rw [hc]; simpa using Hif)]
        try rfl
    · ileft
      isplitr
      · ipureintro; first | rfl | trivial
      iframe
      iexists none
      simp only [ccOptCellW]
      isplitr
      · ipureintro; rfl
      ipureintro
      refine ⟨?_, H2.2.1, H2.2.2⟩
      rw [ccOptField_none _ _ _ _ (by rw [List.getElem?_eq_none (by omega)]; simp)]
      try rfl
  iintro (⟨%Hv, %i3, %o3, %q3, i, NodeId, c3, Hd, c, data, «$res0», %H3⟩ |
    ⟨%Hv, Hd, «$res0», NodeId, %Hn⟩) <;> subst Hv
  rotate_left
  · wp_auto
    iapply HΦ
    rw [Hn]
    iframe
    isplitr
    · ipureintro; exact Herrn
    iapply ccV1_combine p Hpn
    iframe
  have hik : (sint.nat i3 : Int) = sint.Z i3 := by word
  wp_auto
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (i4 : w64) (o4 : Option (List w8)) (q4 : GoSlice),
        "i" ∷ i_ptr ↦ i4 ∗ "Context" ∷ p.[raftpb.ConfChange, go!"Context"] ↦ q4 ∗
        "c4" ∷ ccOptBytesW q4 o4 ∗ "Hd" ∷ d ↦*{dq} bs ∗ "c" ∷ c_ptr ↦ p ∗ "data" ∷ data_ptr ↦ d ∗
        "$res0" ∷ «$res0_ptr» ↦ GoInterface.nil ∗
        "%H4" ∷ ⌜ccOptField bs (sint.nat i3) (W8 34) ccFieldL = some (o4, sint.nat i4) ∧ 0 ≤ sint.Z i4 ∧
          sint.Z i4 ≤ bs.length⌝) ∨
      (⌜v = returnVal #()⌝ ∗ "Hd" ∷ d ↦*{dq} bs ∗ "$res0" ∷ «$res0_ptr» ↦ err ∗
        "Context" ∷ p.[raftpb.ConfChange, go!"Context"] ↦ (zero_val raftpb.ConfChange).Context' ∗ "%Hn" ∷ ⌜ccDecodeV1 bs = none⌝)))
    at next with [i Context Hd c data «$res0»]
  · wp_if_destruct
    · -- in range
      have hlt : sint.nat i3 < bs.length := by omega
      obtain ⟨c, hc⟩ : ∃ c, bs[sint.nat i3]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
      simp only [show 0 ≤ sint.Z i3 ∧ sint.Z i3 < sint.Z d.len from ⟨H3.2.1, by omega⟩]
      wp_apply wp_load_slice_index d (sint.Z i3) bs dq c H3.2.1 $$ [Hd] as Hd
      · iframe; ipureintro; exact hc
      have hin : sint.nat (i3 + W64 1) = sint.nat i3 + 1 := by word
      have hiZ0 : 0 ≤ sint.Z (i3 + W64 1) := by word
      have hiZ1 : sint.Z (i3 + W64 1) ≤ bs.length := by word
      have hcI : bs[sint.nat i3]? = some c := hc
      wp_if_destruct
      · -- the tag
        wp_apply wp_consumeBytes d dq bs (i3 + W64 1) hiZ0 hiZ1 $$ [$Hd] as %v %j %ok ⟨Hd, Hr⟩
        have hO : ccOptField bs (sint.nat i3) (W8 34) ccFieldL =
            (ccFieldL bs (sint.nat i3 + 1)).map (fun p => (some p.1, p.2)) := by
          unfold ccOptField; rw [ite_eq_left hcI]
        rw [hin]
        cases he : ccFieldL bs (sint.nat i3 + 1) with
        | none =>
          simp only
          icases Hr with %Hr
          subst Hr
          wp_auto
          iright
          iframe
          ipureintro
          unfold ccDecodeV1
          rw [H1.1]; simp only [Option.bind_some]; rw [H2.1]; simp only [Option.bind_some]; rw [H3.1]; simp only [Option.bind_some]; rw [hO, he]; simp
        | some pr =>
          obtain ⟨v', j'⟩ := pr
          simp only
          icases Hr with ⟨%Hr, Hv⟩
          obtain ⟨rfl, hj⟩ := Hr
          have hb := ccFieldL_bound he
          wp_auto
          ileft
          isplitr
          · ipureintro; rfl
          iexists j, some v', _
          simp only [ccOptBytesW]
          iframe
          ipureintro
          refine ⟨?_, by omega, by omega⟩
          rw [hO, he, show sint.nat j = j' from by
            rw [show sint.nat j = (sint.Z j).toNat from rfl, hj]; simp]
          rfl
      · ileft
        isplitr
        · ipureintro; first | rfl | trivial
        iframe
        iexists none
        simp only [ccOptBytesW]
        isplitr
        · ipureintro; rfl
        ipureintro
        refine ⟨?_, H3.2.1, H3.2.2⟩
        rw [ccOptField_none _ _ _ _ (by rw [hc]; simpa using Hif)]
        try rfl
    · ileft
      isplitr
      · ipureintro; first | rfl | trivial
      iframe
      iexists none
      simp only [ccOptBytesW]
      isplitr
      · ipureintro; rfl
      ipureintro
      refine ⟨?_, H3.2.1, H3.2.2⟩
      rw [ccOptField_none _ _ _ _ (by rw [List.getElem?_eq_none (by omega)]; simp)]
      try rfl
  iintro (⟨%Hv, %i4, %o4, %q4, i, Context, c4, Hd, c, data, «$res0», %H4⟩ |
    ⟨%Hv, Hd, «$res0», Context, %Hn⟩) <;> subst Hv
  rotate_left
  · wp_auto
    iapply HΦ
    rw [Hn]
    iframe
    isplitr
    · ipureintro; exact Herrn
    iapply ccV1_combine p Hpn
    iframe
  have hik : (sint.nat i4 : Int) = sint.Z i4 := by word
  wp_auto
  have hD : ccDecodeV1 bs = if sint.nat i4 = bs.length then
      some ⟨o2.getD (W32 0), o3.getD (W64 0), o4.getD [], o1.getD (W64 0)⟩ else none := by
    unfold ccDecodeV1
    rw [H1.1]; simp only [Option.bind_some]
    rw [H2.1]; simp only [Option.bind_some]
    rw [H3.1]; simp only [Option.bind_some]
    rw [H4.1]; simp only [Option.bind_some]
  imod ccOptCellW_persist q1 o1 ⊤ $$ c1 with #c1
  imod ccOptCellW_persist q2 o2 ⊤ $$ c2 with #c2
  imod ccOptCellW_persist q3 o3 ⊤ $$ c3 with #c3
  imod ccOptBytesW_persist q4 o4 ⊤ $$ c4 with #c4
  iapply wp_fupd
  wp_if_destruct
  · ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod pbMsg_alloc raftpb.ConfChange p _ _ slice.nil [] ⊤ (ufWire_nil _)
      $$ [state sizeCache unknownFields Hnil] with #Hpbm
    · iframe
    imodintro
    iapply HΦ
    rw [hD, ite_eq_left Hlen.1.symm]
    iframe
    isplitr
    · ipureintro; rfl
    unfold ownConfChange
    iexists q2, q3, q1, q4, []
    ihave #HcT : (cellRO q2 (o2.getD (W32 0)) : IProp GF) $$ [c2]
    · rw [show W32 0 = zero_val w32 from rfl]; iapply (nx_optCell_cellRO q2 o2); iexact c2
    ihave #HcN : (cellRO q3 (o3.getD (W64 0)) : IProp GF) $$ [c3]
    · rw [show W64 0 = zero_val w64 from rfl]; iapply (nx_optCell_cellRO q3 o3); iexact c3
    ihave #HcI : (cellRO q1 (o1.getD (W64 0)) : IProp GF) $$ [c1]
    · rw [show W64 0 = zero_val w64 from rfl]; iapply (nx_optCell_cellRO q1 o1); iexact c1
    simp only
    iframe Type' NodeId Id Context HcT HcN HcI c4 Hpbm
    ipureintro; exact Hpn
  · have hne : sint.nat i4 ≠ bs.length := fun h => Hif (by word)
    imodintro
    iapply HΦ
    rw [hD, ite_eq_right hne]
    iframe
    isplitr
    · ipureintro; exact Herrn
    iapply ccV1_combine p Hpn
    iframe


end proof

end EtcdGrove
end Perennial
