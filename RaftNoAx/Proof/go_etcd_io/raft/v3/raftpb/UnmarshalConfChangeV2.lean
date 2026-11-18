/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/UnmarshalConfChangeV2.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-part.md`).
-/
module

public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.UnmarshalConfChangeV2
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeEnum
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeField
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeBytes
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.unmarshalConfChangeSingle
public import RaftNoAx.Proof.go_etcd_io.raft.v3.raftpb.UnmarshalConfChangeV1

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

theorem ccV2_combine (p : Loc) (hp : p ≠ null) (st : google_golang_org.protobuf.internal.impl.MessageState)
    (pt : Loc) (chs cs us : GoSlice) (sc : w32) :
    (p.[raftpb.ConfChangeV2, go!"state"] ↦ st ∗ p.[raftpb.ConfChangeV2, go!"Transition"] ↦ pt ∗
      p.[raftpb.ConfChangeV2, go!"Changes"] ↦ chs ∗ p.[raftpb.ConfChangeV2, go!"Context"] ↦ cs ∗
      p.[raftpb.ConfChangeV2, go!"unknownFields"] ↦ us ∗
      p.[raftpb.ConfChangeV2, go!"sizeCache"] ↦ sc : IProp GF) ⊢
    ∃ x' : raftpb.ConfChangeV2, p ↦ x' := by
  iintro ⟨H1, H2, H3, H4, H5, H6⟩
  iexists raftpb.ConfChangeV2.mk st pt chs cs us sc
  iapply typedPointsto_combine _ _ _ hp
  simp only [TypedPointsto.typedPointstoDef]
  iframe

theorem raftpb.UnmarshalConfChangeV2.wp_proof
    (wp_consumeEnum : raftpb.consumeEnum.spec (GF := GF) (hG := hG))
    (wp_consumeField : raftpb.consumeField.spec (GF := GF) (hG := hG))
    (wp_unmarshalConfChangeSingle : raftpb.unmarshalConfChangeSingle.spec (GF := GF) (hG := hG))
    (wp_consumeBytes : raftpb.consumeBytes.spec (GF := GF) (hG := hG)) :
    raftpb.UnmarshalConfChangeV2.spec (GF := GF) (hG := hG) := by
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
  icases typedPointsto_split _ _ _ $$ Hp with Hm
  simp only [TypedPointsto.typedPointstoDef]
  icases Hm with ⟨state, Transition, Changes, Context, unknownFields, sizeCache, -⟩
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (i1 : w64) (o1 : Option w32) (q1 : Loc),
        "i" ∷ i_ptr ↦ i1 ∗ "Transition" ∷ p.[raftpb.ConfChangeV2, go!"Transition"] ↦ q1 ∗
        "c1" ∷ ccOptCellW q1 o1 ∗ "Hd" ∷ d ↦*{dq} bs ∗ "c" ∷ c_ptr ↦ p ∗ "data" ∷ data_ptr ↦ d ∗
        "$res0" ∷ «$res0_ptr» ↦ GoInterface.nil ∗
        "%H1" ∷ ⌜ccOptField bs 0 (W8 8) ccEnumL = some (o1, sint.nat i1) ∧ 0 ≤ sint.Z i1 ∧
          sint.Z i1 ≤ bs.length⌝) ∨
      (⌜v = returnVal #()⌝ ∗ "Hd" ∷ d ↦*{dq} bs ∗ "$res0" ∷ «$res0_ptr» ↦ err ∗
        "Transition" ∷ p.[raftpb.ConfChangeV2, go!"Transition"] ↦ (zero_val raftpb.ConfChangeV2).Transition' ∗ "%Hn" ∷ ⌜ccDecodeV2 bs = none⌝)))
    at next with [i Transition Hd c data «$res0»]
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
        wp_apply wp_consumeEnum d dq bs (W64 0 + W64 1) hiZ0 hiZ1 $$ [$Hd] as %v %j %ok ⟨Hd, %Hr⟩
        have hO : ccOptField bs 0 (W8 8) ccEnumL =
            (ccEnumL bs (0 + 1)).map (fun p => (some p.1, p.2)) := by
          unfold ccOptField; rw [ite_eq_left hcI]
        rw [hin] at Hr
        cases he : ccEnumL bs (0 + 1) with
        | none =>
          rw [he] at Hr
          subst Hr
          wp_auto
          iright
          iframe
          ipureintro
          unfold ccDecodeV2
          rw [hO, he]; simp
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
  iintro (⟨%Hv, %i1, %o1, %q1, i, Transition, c1, Hd, c, data, «$res0», %H1⟩ |
    ⟨%Hv, Hd, «$res0», Transition, %Hn⟩) <;> subst Hv
  rotate_left
  · wp_auto
    iapply HΦ
    rw [Hn]
    iframe
    isplitr
    · ipureintro; exact Herrn
    iapply ccV2_combine p Hpn
    iframe
  have hik : (sint.nat i1 : Int) = sint.Z i1 := by word
  wp_auto
  ihave Hnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hnilc : ownSliceCap (GF := GF) Loc slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (ic : w64) (fuel : Nat) (acc : List ConfChangeSingleM) (chsl : GoSlice)
      (ls : List Loc),
      "i" ∷ i_ptr ↦ ic ∗ "Changes" ∷ p.[raftpb.ConfChangeV2, go!"Changes"] ↦ chsl ∗
      "Hchs" ∷ chsl ↦* ls ∗ "Hchc" ∷ ownSliceCap Loc chsl (DFrac.own 1) ∗
      "#Hls" ∷ ([∗list] q;cc ∈ ls;acc, ccsRO q cc) ∗
      "%HL" ∷ ⌜ccChangesLoop bs (bs.length + 1) (sint.nat i1) [] =
          ccChangesLoop bs fuel (sint.nat ic) acc ∧ bs.length - sint.nat ic < fuel ∧
        0 ≤ sint.Z ic ∧ sint.Z ic ≤ bs.length⌝) $$ [i Changes Hnil Hnilc]
  · iexists i1, bs.length + 1, [], slice.nil, []
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
    ipureintro
    exact ⟨rfl, by omega, H1.2.1, H1.2.2⟩
  wp_for IH
  have hicZ : (sint.nat ic : Int) = sint.Z ic := by word
  wp_join (Q := fun v => iprop(⌜v = #(decide (bs[sint.nat ic]? = some (W8 18)))⌝ ∗
      "Hd" ∷ d ↦*{dq} bs ∗ "data" ∷ data_ptr ↦ d ∗ "i" ∷ i_ptr ↦ ic)) with [Hd data i]
  · have hlt : sint.nat ic < bs.length := by omega
    obtain ⟨c, hc⟩ : ∃ c, bs[sint.nat ic]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [show 0 ≤ sint.Z ic ∧ sint.Z ic < sint.Z d.len from ⟨HL.2.2.1, by omega⟩]
    wp_apply wp_load_slice_index d (sint.Z ic) bs dq c HL.2.2.1 $$ [Hd] as Hd
    · iframe; ipureintro; exact hc
    iframe
    ipureintro
    rw [hc]
    simp
  · iframe
    ipureintro
    rw [List.getElem?_eq_none (by omega)]
    simp
  iintro ⟨%Hv, Hd, data, i⟩
  subst Hv
  obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  subst hf
  have hdecV2 : ccDecodeV2 bs = (ccChangesLoop bs (f + 1) (sint.nat ic) acc).bind fun p2 =>
      (ccOptField bs p2.2 (W8 26) ccFieldL).bind fun p3 =>
      if p3.2 = bs.length then some ⟨o1.getD (W32 0), p2.1, p3.1.getD []⟩ else none := by
    unfold ccDecodeV2; rw [H1.1]; simp only [Option.bind_some]; rw [HL.1]
  by_cases htag : bs[sint.nat ic]? = some (W8 18)
  · simp only [htag, decide_true, ite_true]
    wp_auto
    have hlt : sint.nat ic < bs.length := (List.getElem?_eq_some_iff.mp htag).1
    have hlt' : sint.Z ic < bs.length := by omega
    have hic1 : sint.Z (ic + W64 1) = sint.Z ic + 1 := by word
    have hicn : sint.nat (ic + W64 1) = sint.nat ic + 1 := by word
    wp_apply wp_consumeField d dq bs (ic + W64 1) (by omega) (by omega) $$ [$Hd] as %v %j %ok Hr
    rw [hicn]
    cases hfl : ccFieldL bs (sint.nat ic + 1) with
    | none =>
      have hst : ccChangesLoop bs (f + 1) (sint.nat ic) acc = none := by
        rw [ccChangesLoop.eq_2, ite_eq_left htag, hfl]
      simp only
      icases Hr with ⟨%Hok, Hd⟩
      subst Hok
      wp_auto
      wp_for_post
      iapply HΦ
      rw [hdecV2, hst]
      simp only [Option.bind_none]
      iframe
      isplitr
      · ipureintro; exact Herrn
      iapply ccV2_combine p Hpn
      iframe
    | some pr =>
      obtain ⟨sub, j'⟩ := pr
      have hfb := ccFieldL_bound hfl
      simp only
      icases Hr with ⟨%Hok, Hv, Hback⟩
      obtain ⟨rfl, hj⟩ := Hok
      wp_auto
      wp_apply wp_unmarshalConfChangeSingle v dq sub $$ [$Hv] as %sp %ok2 ⟨Hv, Hs⟩
      ihave Hd := Hback $$ Hv
      cases hsd : ccDecodeSingle sub with
      | none =>
        have hst : ccChangesLoop bs (f + 1) (sint.nat ic) acc = none := by
          rw [ccChangesLoop.eq_2, ite_eq_left htag, hfl]; simp only [hsd]
        simp only
        icases Hs with %Hok2
        subst Hok2
        wp_auto
        wp_for_post
        iapply HΦ
        rw [hdecV2, hst]
        simp only [Option.bind_none]
        iframe
        isplitr
        · ipureintro; exact Herrn
        iapply ccV2_combine p Hpn
        iframe
      | some cc =>
        have hst : ccChangesLoop bs (f + 1) (sint.nat ic) acc = ccChangesLoop bs f j' (acc ++ [cc]) := by
          rw [ccChangesLoop.eq_2, ite_eq_left htag, hfl]; simp only [hsd]
        simp only
        icases Hs with ⟨%Hok2, #Hs⟩
        subst Hok2
        wp_auto
        wp_apply wp_slice_literal (V := Loc) [sp]
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        wp_apply wp_slice_append $$ [$Hchs $Hchc $Hsl2] as %chsl2 ⟨Hchs, Hchc, -⟩
        wp_for_post
        iframe
        ihave #Hls2 : ([∗list] q;cc ∈ ls ++ [sp];acc ++ [cc], ccsRO (GF := GF) q cc) $$ [Hls Hs]
        · iapply BigSepL2.bigSepL2_snoc.2
          iframe Hls Hs
        iexists j, f, acc ++ [cc], chsl2, ls ++ [sp]
        iframe
        isplitr
        · iexact Hls2
        ipureintro
        have hjn : sint.nat j = j' := by
          rw [show sint.nat j = (sint.Z j).toNat from rfl, hj]; simp
        refine ⟨?_, by omega, by omega, by omega⟩
        rw [HL.1, hst, hjn]
  · have HLx : ccChangesLoop bs (bs.length + 1) (sint.nat i1) [] = some (acc, sint.nat ic) := by
      rw [HL.1, ccChangesLoop.eq_2, ite_eq_right htag]
    simp only [htag, decide_false]
    rw [ite_eq_right (by intro h; exact absurd (GoGlobalContext.intoVal_inj_bool (of_decide_eq_true h)) (by decide))]
    simp only [decide_true, ite_true]
    wp_auto
    wp_join (Q := fun v => iprop(
        (⌜v = executeVal⌝ ∗ ∃ (i3 : w64) (o3 : Option (List w8)) (q3 : GoSlice),
          "i" ∷ i_ptr ↦ i3 ∗ "Context" ∷ p.[raftpb.ConfChangeV2, go!"Context"] ↦ q3 ∗
          "c3" ∷ ccOptBytesW q3 o3 ∗ "Hd" ∷ d ↦*{dq} bs ∗ "c" ∷ c_ptr ↦ p ∗ "data" ∷ data_ptr ↦ d ∗
          "$res0" ∷ «$res0_ptr» ↦ GoInterface.nil ∗
          "%H3" ∷ ⌜ccOptField bs (sint.nat ic) (W8 26) ccFieldL = some (o3, sint.nat i3) ∧ 0 ≤ sint.Z i3 ∧
            sint.Z i3 ≤ bs.length⌝) ∨
        (⌜v = returnVal #()⌝ ∗ "Hd" ∷ d ↦*{dq} bs ∗ "$res0" ∷ «$res0_ptr» ↦ err ∗
          "Context" ∷ p.[raftpb.ConfChangeV2, go!"Context"] ↦ (zero_val raftpb.ConfChangeV2).Context' ∗ "%Hn" ∷ ⌜ccDecodeV2 bs = none⌝)))
      at next with [i Context Hd c data «$res0»]
    · wp_if_destruct
      · -- in range
        have hlt : sint.nat ic < bs.length := by omega
        obtain ⟨c, hc⟩ : ∃ c, bs[sint.nat ic]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
        simp only [show 0 ≤ sint.Z ic ∧ sint.Z ic < sint.Z d.len from ⟨HL.2.2.1, by omega⟩]
        wp_apply wp_load_slice_index d (sint.Z ic) bs dq c HL.2.2.1 $$ [Hd] as Hd
        · iframe; ipureintro; exact hc
        have hin : sint.nat (ic + W64 1) = sint.nat ic + 1 := by word
        have hiZ0 : 0 ≤ sint.Z (ic + W64 1) := by word
        have hiZ1 : sint.Z (ic + W64 1) ≤ bs.length := by word
        have hcI : bs[sint.nat ic]? = some c := hc
        wp_if_destruct
        · -- the tag
          wp_apply wp_consumeBytes d dq bs (ic + W64 1) hiZ0 hiZ1 $$ [$Hd] as %v %j %ok ⟨Hd, Hr⟩
          have hO : ccOptField bs (sint.nat ic) (W8 26) ccFieldL =
              (ccFieldL bs (sint.nat ic + 1)).map (fun p => (some p.1, p.2)) := by
            unfold ccOptField; rw [ite_eq_left hcI]
          rw [hin]
          cases he : ccFieldL bs (sint.nat ic + 1) with
          | none =>
            simp only
            icases Hr with %Hr
            subst Hr
            wp_auto
            iright
            iframe
            ipureintro
            unfold ccDecodeV2
            rw [H1.1]; simp only [Option.bind_some]; rw [HLx]; simp only [Option.bind_some]; rw [hO, he]; simp
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
          refine ⟨?_, HL.2.2.1, HL.2.2.2⟩
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
        refine ⟨?_, HL.2.2.1, HL.2.2.2⟩
        rw [ccOptField_none _ _ _ _ (by rw [List.getElem?_eq_none (by omega)]; simp)]
        try rfl
    iintro (⟨%Hv, %i3, %o3, %q3, i, Context, c3, Hd, c, data, «$res0», %H3⟩ |
      ⟨%Hv, Hd, «$res0», Context, %Hn⟩) <;> subst Hv
    rotate_left
    · wp_auto
      iapply HΦ
      rw [Hn]
      iframe
      isplitr
      · ipureintro; exact Herrn
      iapply ccV2_combine p Hpn
      iframe
    have hik : (sint.nat i3 : Int) = sint.Z i3 := by word
    wp_auto
    have hD : ccDecodeV2 bs = if sint.nat i3 = bs.length then
        some ⟨o1.getD (W32 0), acc, o3.getD []⟩ else none := by
      unfold ccDecodeV2
      rw [H1.1]; simp only [Option.bind_some]
      rw [HLx]; simp only [Option.bind_some]
      rw [H3.1]; simp only [Option.bind_some]
    imod ccOptCellW_persist q1 o1 ⊤ $$ c1 with #c1
    imod ccOptBytesW_persist q3 o3 ⊤ $$ c3 with #c3
    iapply wp_fupd
    wp_if_destruct
    · ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
      · iapply ownSlice_nil
      imod pbMsg_alloc raftpb.ConfChangeV2 p _ _ slice.nil [] ⊤ (ufWire_nil _)
        $$ [state sizeCache unknownFields Hnil] with #Hpbm
      · iframe
      imodintro
      iapply HΦ
      rw [hD, ite_eq_left Hlen.1.symm]
      iframe
      isplitr
      · ipureintro; rfl
      unfold ownConfChangeV2
      iexists q1, chsl, ls, q3, []
      ihave #HcT : (cellRO q1 (o1.getD (W32 0)) : IProp GF) $$ [c1]
      · rw [show W32 0 = zero_val w32 from rfl]; iapply (nx_optCell_cellRO q1 o1); iexact c1
      simp only
      iframe Transition Changes Hchs Hls Context HcT c3 Hpbm
      ipureintro; exact Hpn
    · have hne : sint.nat i3 ≠ bs.length := fun h => Hif (by word)
      imodintro
      iapply HΦ
      rw [hD, ite_eq_right hne]
      iframe
      isplitr
      · ipureintro; exact Herrn
      iapply ccV2_combine p Hpn
      iframe

end proof

end EtcdGrove
end Perennial
