/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/toConfChangeSingle.lean`. Lean-first (no Rocq
counterpart). (2026-10-15, raft v3.7 retarget, stage R2: the `ConfState` a pointer, each change a
fresh `*pb.ConfChangeSingle` made read-only.)
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.toConfChangeSingle
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__Enum

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

theorem confchange.toConfChangeSingle.wp_proof
    (wp_ConfChangeType_Enum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG)) :
    confchange.toConfChangeSingle.spec (GF := GF) (hG := hG) := by
  -- `int32` (`ConfChangeType`'s underlying type) is not an interface: Perennial states
  -- `NotInterface` per type constructor, and `go.int32` is a non-reducible definition
  -- (as in `raftpb/ConfChange__AsV2.lean`).
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  intro cs c dq
  wp_start as Hcs
  iNamed Hcs
  -- `in` is a Lean keyword: name its cell by hand before `wp_auto` names the others
  wp_pures
  wp_alloc in_ptr as Hin
  wp_auto
  ihave %Holen := ownSlice_len $$ Ho
  ihave Hnil : (slice.nil ↦* ([] : List Loc)) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap Loc slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  -- `for _, id := range cs.VotersOutgoing { out = append(out, &{AddNode, new(id)}) }`
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64) (lo : List Loc),
      "i" ∷ i_ptr ↦ n ∗
      "out" ∷ out_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* lo ∗
      "#Hc" ∷ ([∗list] q;y ∈ lo;(c.VotersOutgoing'.take (sint.nat n)).map addNodeCC, ccsRO q y) ∗
      "Hcap" ∷ ownSliceCap Loc s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (c.VotersOutgoing'.length : Int)⌝) $$ [i out id Hnil Hcap]
  · iexists W64 0, slice.nil, zero_val w64, []
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil]
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z so.len := by simpa using Hif
    have Hlt : sint.nat n < c.VotersOutgoing'.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, c.VotersOutgoing'[sint.nat n]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z so.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index so (sint.Z n) _ _ x Hn.1 $$ [Ho] with Ho
    · iframe Ho; ipureintro; exact Hx
    rw [show raftpb.ConfChangeAddNode = #(W32 0) from rfl]
    wp_apply wp_ConfChangeType_Enum (W32 0)
    iintro %pty Hpt
    wp_auto
    imod cellRO_alloc _ _ $$ Hpt with #cty
    imod cellRO_alloc _ _ $$ «$v1» with #cnd
    imod ccsRO_of_struct «$sl0_ptr»
      { state' := zeroValDef, Type' := pty, NodeId' := «$v1_ptr», unknownFields' := slice.nil,
        sizeCache' := 0 }
      (addNodeCC x) ⊤ rfl $$ [«$sl0»] with #Hq
    · dsimp only
      iframe
      iframe cty cnd
    wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s3 ⟨Hs, Hcap, -⟩
    wp_for_post
    have Htake : c.VotersOutgoing'.take (sint.nat (n + W64 1)) =
        c.VotersOutgoing'.take (sint.nat n) ++ [x] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]; rfl
    iframe
    iexists n + W64 1, s3, x, lo ++ [«$sl0_ptr»]
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil]
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_snoc.2
      iframe Hc Hq
    ipureintro; constructor <;> word
  have Hif' : ¬ sint.Z n < sint.Z so.len := by simpa using Hif
  have Hn' : sint.nat n = c.VotersOutgoing'.length := by word
  rw [Hn', List.take_length]
  irename Hs => Hos
  irename Hc => Hoc
  iclear Hcap
  ihave Hnil : (slice.nil ↦* ([] : List Loc)) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap Loc slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave %Hlen := ownSlice_len $$ Ho
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64) (li : List Loc),
      "i" ∷ i_ptr ↦ n ∗
      "Hin" ∷ in_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* li ∗
      "#Hc" ∷ ([∗list] q;y ∈ li;(c.VotersOutgoing'.take (sint.nat n)).map removeNodeCC, ccsRO q y) ∗
      "Hcap" ∷ ownSliceCap Loc s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (c.VotersOutgoing'.length : Int)⌝) $$ [i Hin id Hnil Hcap]
  · iexists W64 0, slice.nil, zero_val w64, []
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil]
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z so.len := by simpa using Hif
    have Hlt : sint.nat n < c.VotersOutgoing'.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, c.VotersOutgoing'[sint.nat n]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z so.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index so (sint.Z n) _ _ x Hn.1 $$ [Ho] with Ho
    · iframe Ho; ipureintro; exact Hx
    rw [show raftpb.ConfChangeRemoveNode = #(W32 1) from rfl]
    wp_apply wp_ConfChangeType_Enum (W32 1)
    iintro %pty Hpt
    wp_auto
    imod cellRO_alloc _ _ $$ Hpt with #cty
    imod cellRO_alloc _ _ $$ «$v1» with #cnd
    imod ccsRO_of_struct «$sl0_ptr»
      { state' := zeroValDef, Type' := pty, NodeId' := «$v1_ptr», unknownFields' := slice.nil,
        sizeCache' := 0 }
      (removeNodeCC x) ⊤ rfl $$ [«$sl0»] with #Hq
    · dsimp only
      iframe
      iframe cty cnd
    wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s3 ⟨Hs, Hcap, -⟩
    wp_for_post
    have Htake : c.VotersOutgoing'.take (sint.nat (n + W64 1)) =
        c.VotersOutgoing'.take (sint.nat n) ++ [x] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]; rfl
    iframe
    iexists n + W64 1, s3, x, li ++ [«$sl0_ptr»]
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil]
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_snoc.2
      
      iframe Hc Hq
    ipureintro; constructor <;> word
  have Hif' : ¬ sint.Z n < sint.Z so.len := by simpa using Hif
  have Hn' : sint.nat n = c.VotersOutgoing'.length := by word
  rw [Hn', List.take_length]
  ihave %Hlen := ownSlice_len $$ Hv
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64) (li : List Loc),
      "i" ∷ i_ptr ↦ n ∗
      "Hin" ∷ in_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* li ∗
      "#Hc" ∷ ([∗list] q;y ∈ li;c.VotersOutgoing'.map removeNodeCC ++ (c.Voters'.take (sint.nat n)).map addNodeCC, ccsRO q y) ∗
      "Hcap" ∷ ownSliceCap Loc s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (c.Voters'.length : Int)⌝) $$ [i Hin id Hs Hcap]
  · iexists W64 0, s', zero_val w64, li
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, List.append_nil]
    iframe
    iframe Hc
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z sv.len := by simpa using Hif
    have Hlt : sint.nat n < c.Voters'.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, c.Voters'[sint.nat n]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sv.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index sv (sint.Z n) _ _ x Hn.1 $$ [Hv] with Hv
    · iframe Hv; ipureintro; exact Hx
    rw [show raftpb.ConfChangeAddNode = #(W32 0) from rfl]
    wp_apply wp_ConfChangeType_Enum (W32 0)
    iintro %pty Hpt
    wp_auto
    imod cellRO_alloc _ _ $$ Hpt with #cty
    imod cellRO_alloc _ _ $$ «$v1» with #cnd
    imod ccsRO_of_struct «$sl0_ptr»
      { state' := zeroValDef, Type' := pty, NodeId' := «$v1_ptr», unknownFields' := slice.nil,
        sizeCache' := 0 }
      (addNodeCC x) ⊤ rfl $$ [«$sl0»] with #Hq
    · dsimp only
      iframe
      iframe cty cnd
    wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s3 ⟨Hs, Hcap, -⟩
    wp_for_post
    have Htake : c.Voters'.take (sint.nat (n + W64 1)) =
        c.Voters'.take (sint.nat n) ++ [x] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]; rfl
    iframe
    iexists n + W64 1, s3, x, li ++ [«$sl0_ptr»]
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil]
    iframe
    isplitr
    · rw [← List.append_assoc]
      iapply BigSepL2.bigSepL2_snoc.2
      iframe Hc Hq
    ipureintro; constructor <;> word
  have Hif' : ¬ sint.Z n < sint.Z sv.len := by simpa using Hif
  have Hn' : sint.nat n = c.Voters'.length := by word
  rw [Hn', List.take_length]
  ihave %Hlen := ownSlice_len $$ Hl
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64) (li : List Loc),
      "i" ∷ i_ptr ↦ n ∗
      "Hin" ∷ in_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* li ∗
      "#Hc" ∷ ([∗list] q;y ∈ li;c.VotersOutgoing'.map removeNodeCC ++ c.Voters'.map addNodeCC ++ (c.Learners'.take (sint.nat n)).map addLearnerCC, ccsRO q y) ∗
      "Hcap" ∷ ownSliceCap Loc s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (c.Learners'.length : Int)⌝) $$ [i Hin id Hs Hcap]
  · iexists W64 0, s', zero_val w64, li
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, List.append_nil]
    iframe
    iframe Hc
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z sl.len := by simpa using Hif
    have Hlt : sint.nat n < c.Learners'.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, c.Learners'[sint.nat n]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index sl (sint.Z n) _ _ x Hn.1 $$ [Hl] with Hl
    · iframe Hl; ipureintro; exact Hx
    rw [show raftpb.ConfChangeAddLearnerNode = #(W32 3) from rfl]
    wp_apply wp_ConfChangeType_Enum (W32 3)
    iintro %pty Hpt
    wp_auto
    imod cellRO_alloc _ _ $$ Hpt with #cty
    imod cellRO_alloc _ _ $$ «$v1» with #cnd
    imod ccsRO_of_struct «$sl0_ptr»
      { state' := zeroValDef, Type' := pty, NodeId' := «$v1_ptr», unknownFields' := slice.nil,
        sizeCache' := 0 }
      (addLearnerCC x) ⊤ rfl $$ [«$sl0»] with #Hq
    · dsimp only
      iframe
      iframe cty cnd
    wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s3 ⟨Hs, Hcap, -⟩
    wp_for_post
    have Htake : c.Learners'.take (sint.nat (n + W64 1)) =
        c.Learners'.take (sint.nat n) ++ [x] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]; rfl
    iframe
    iexists n + W64 1, s3, x, li ++ [«$sl0_ptr»]
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil]
    iframe
    isplitr
    · rw [← List.append_assoc]
      iapply BigSepL2.bigSepL2_snoc.2
      iframe Hc Hq
    ipureintro; constructor <;> word
  have Hif' : ¬ sint.Z n < sint.Z sl.len := by simpa using Hif
  have Hn' : sint.nat n = c.Learners'.length := by word
  rw [Hn', List.take_length]
  ihave %Hlen := ownSlice_len $$ Hn
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64) (li : List Loc),
      "i" ∷ i_ptr ↦ n ∗
      "Hin" ∷ in_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* li ∗
      "#Hc" ∷ ([∗list] q;y ∈ li;c.VotersOutgoing'.map removeNodeCC ++ c.Voters'.map addNodeCC ++ c.Learners'.map addLearnerCC ++ (c.LearnersNext'.take (sint.nat n)).map addLearnerCC, ccsRO q y) ∗
      "Hcap" ∷ ownSliceCap Loc s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (c.LearnersNext'.length : Int)⌝) $$ [i Hin id Hs Hcap]
  · iexists W64 0, s', zero_val w64, li
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, List.append_nil]
    iframe
    iframe Hc
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z sn.len := by simpa using Hif
    have Hlt : sint.nat n < c.LearnersNext'.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, c.LearnersNext'[sint.nat n]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sn.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index sn (sint.Z n) _ _ x Hn.1 $$ [Hn] with Hn
    · iframe Hn; ipureintro; exact Hx
    rw [show raftpb.ConfChangeAddLearnerNode = #(W32 3) from rfl]
    wp_apply wp_ConfChangeType_Enum (W32 3)
    iintro %pty Hpt
    wp_auto
    imod cellRO_alloc _ _ $$ Hpt with #cty
    imod cellRO_alloc _ _ $$ «$v1» with #cnd
    imod ccsRO_of_struct «$sl0_ptr»
      { state' := zeroValDef, Type' := pty, NodeId' := «$v1_ptr», unknownFields' := slice.nil,
        sizeCache' := 0 }
      (addLearnerCC x) ⊤ rfl $$ [«$sl0»] with #Hq
    · dsimp only
      iframe
      iframe cty cnd
    wp_apply wp_slice_literal (V := Loc) [«$sl0_ptr»]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s3 ⟨Hs, Hcap, -⟩
    wp_for_post
    have Htake : c.LearnersNext'.take (sint.nat (n + W64 1)) =
        c.LearnersNext'.take (sint.nat n) ++ [x] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]; rfl
    iframe
    iexists n + W64 1, s3, x, li ++ [«$sl0_ptr»]
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil]
    iframe
    isplitr
    · rw [← List.append_assoc]
      iapply BigSepL2.bigSepL2_snoc.2
      iframe Hc Hq
    ipureintro; constructor <;> word
  have Hif' : ¬ sint.Z n < sint.Z sn.len := by simpa using Hif
  have Hn' : sint.nat n = c.LearnersNext'.length := by word
  rw [Hn', List.take_length]
  iapply HΦ
  simp only [restoreOutCC, restoreInCC]
  iframe Hos Hoc Hs Hc Hcap
  simp only [ownCSM]
  iunfold csPts
  iexists sv, sl, so, sn, pa
  isplitr
  · ipureintro; exact Hnn
  iframe HV Hv HL Hl HO Ho HN Hn HA cA Hpb
  ipureintro; exact Hal

end proof

end EtcdGrove
end Perennial
