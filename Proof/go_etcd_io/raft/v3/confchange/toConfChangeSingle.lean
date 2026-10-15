/-
Proof of `Spec/confchange_toConfChangeSingle.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.toConfChangeSingle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem wp_load_idlist_index (sl : GoSlice) (i : Int) (l : List w64) (dq : DFrac) (v : w64)
    (hpos : 0 ≤ i) (Hl : l[i.toNat]? = some v) :
    {{ ownIdList (GF := GF) sl dq l }}
      (App (Val (GoInstruction (GoLoad go.uint64))) (Val #(sliceIndexRef w64 i sl)))
    {{ RET #v; ownIdList sl dq l }} := by
  iintro %Φ Hl HΦ
  unfold ownIdList
  icases Hl with (⟨%H0, %He⟩ | Hs)
  · subst He; simp at Hl
  wp_apply wp_load_slice_index sl i l dq v hpos $$ [Hs] with Hs
  · iframe Hs; ipureintro; exact Hl
  iapply HΦ
  iright; iexact Hs

theorem confchange.toConfChangeSingle.wp_proof :
    confchange.toConfChangeSingle.spec (GF := GF) (hG := hG) := by
  intro cs voters learners outgoing learnersNext dq dql dqo dqn
  wp_start as ⟨Hvs, Hls, Hlo, Hln⟩
  -- `in` is a Lean keyword: name its cell by hand before `wp_auto` names the others
  wp_pures
  wp_alloc in_ptr as Hin
  wp_auto
  icases ownIdList_len _ _ _ $$ Hlo with ⟨Hlo, %Hlolen⟩
  ihave Hnil : (slice.nil ↦* ([] : List raftpb.ConfChangeSingle)) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap raftpb.ConfChangeSingle slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  -- `for _, id := range cs.VotersOutgoing { out = append(out, AddNode id) }`
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64),
      "i" ∷ i_ptr ↦ n ∗
      "out" ∷ out_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* (outgoing.take (sint.nat n)).map addNodeCC ∗
      "Hcap" ∷ ownSliceCap raftpb.ConfChangeSingle s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (outgoing.length : Int)⌝) $$ [i out id Hnil Hcap]
  · iexists W64 0, slice.nil, zero_val w64
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z cs.VotersOutgoing'.len := by simpa using Hif
    have Hlt : sint.nat n < outgoing.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, outgoing[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cs.VotersOutgoing'.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_idlist_index cs.VotersOutgoing' (sint.Z n) _ _ x Hn.1 Hx $$ [$Hlo] as Hlo
    wp_apply wp_slice_literal (V := raftpb.ConfChangeSingle) [addNodeCC x]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s3 ⟨Hs, Hcap, -⟩
    wp_for_post
    have Htake : outgoing.take (sint.nat (n + W64 1)) = outgoing.take (sint.nat n) ++ [x] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]; rfl
    iframe
    iexists n + W64 1, s3, x
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil]
    iframe
    ipureintro; constructor <;> word
  have Hif' : ¬ sint.Z n < sint.Z cs.VotersOutgoing'.len := by simpa using Hif
  have Hn' : sint.nat n = outgoing.length := by word
  rw [Hn', List.take_length]
  irename Hs => Ho
  iclear Hcap
  icases ownIdList_len _ _ _ $$ Hlo with ⟨Hlo, %Houtgoinglen⟩
  ihave Hnil : (slice.nil ↦* ([] : List raftpb.ConfChangeSingle)) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap raftpb.ConfChangeSingle slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64),
      "i" ∷ i_ptr ↦ n ∗
      "Hin" ∷ in_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* ((outgoing.take (sint.nat n)).map removeNodeCC) ∗
      "Hcap" ∷ ownSliceCap raftpb.ConfChangeSingle s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (outgoing.length : Int)⌝) $$ [i Hin id Hnil Hcap]
  · iexists W64 0, slice.nil, zero_val w64
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z cs.VotersOutgoing'.len := by simpa using Hif
    have Hlt : sint.nat n < outgoing.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, outgoing[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cs.VotersOutgoing'.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_idlist_index cs.VotersOutgoing' (sint.Z n) _ _ x Hn.1 Hx $$ [$Hlo] as Hlo
    wp_apply wp_slice_literal (V := raftpb.ConfChangeSingle) [removeNodeCC x]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s3 ⟨Hs, Hcap, -⟩
    wp_for_post
    have Htake : outgoing.take (sint.nat (n + W64 1)) = outgoing.take (sint.nat n) ++ [x] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]; rfl
    iframe
    iexists n + W64 1, s3, x
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil]
    iframe
    ipureintro; constructor <;> word
  have Hif' : ¬ sint.Z n < sint.Z cs.VotersOutgoing'.len := by simpa using Hif
  have Hn' : sint.nat n = outgoing.length := by word
  rw [Hn', List.take_length]
  ihave %Hvoterslen := ownSlice_len $$ Hvs
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64),
      "i" ∷ i_ptr ↦ n ∗
      "Hin" ∷ in_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* (outgoing.map removeNodeCC ++ (voters.take (sint.nat n)).map addNodeCC) ∗
      "Hcap" ∷ ownSliceCap raftpb.ConfChangeSingle s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (voters.length : Int)⌝) $$ [i Hin id Hs Hcap]
  · iexists W64 0, s', zero_val w64
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z cs.Voters'.len := by simpa using Hif
    have Hlt : sint.nat n < voters.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, voters[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cs.Voters'.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_slice_index cs.Voters' (sint.Z n) _ _ x Hn.1 $$ [Hvs] with Hvs
    · iframe Hvs; ipureintro; exact Hx
    wp_apply wp_slice_literal (V := raftpb.ConfChangeSingle) [addNodeCC x]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s3 ⟨Hs, Hcap, -⟩
    wp_for_post
    have Htake : voters.take (sint.nat (n + W64 1)) = voters.take (sint.nat n) ++ [x] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]; rfl
    iframe
    iexists n + W64 1, s3, x
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  have Hif' : ¬ sint.Z n < sint.Z cs.Voters'.len := by simpa using Hif
  have Hn' : sint.nat n = voters.length := by word
  rw [Hn', List.take_length]
  icases ownIdList_len _ _ _ $$ Hls with ⟨Hls, %Hlearnerslen⟩
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64),
      "i" ∷ i_ptr ↦ n ∗
      "Hin" ∷ in_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* (outgoing.map removeNodeCC ++ voters.map addNodeCC ++ (learners.take (sint.nat n)).map addLearnerCC) ∗
      "Hcap" ∷ ownSliceCap raftpb.ConfChangeSingle s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (learners.length : Int)⌝) $$ [i Hin id Hs Hcap]
  · iexists W64 0, s', zero_val w64
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z cs.Learners'.len := by simpa using Hif
    have Hlt : sint.nat n < learners.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, learners[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cs.Learners'.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_idlist_index cs.Learners' (sint.Z n) _ _ x Hn.1 Hx $$ [$Hls] as Hls
    wp_apply wp_slice_literal (V := raftpb.ConfChangeSingle) [addLearnerCC x]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s3 ⟨Hs, Hcap, -⟩
    wp_for_post
    have Htake : learners.take (sint.nat (n + W64 1)) = learners.take (sint.nat n) ++ [x] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]; rfl
    iframe
    iexists n + W64 1, s3, x
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  have Hif' : ¬ sint.Z n < sint.Z cs.Learners'.len := by simpa using Hif
  have Hn' : sint.nat n = learners.length := by word
  rw [Hn', List.take_length]
  icases ownIdList_len _ _ _ $$ Hln with ⟨Hln, %HlearnersNextlen⟩
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64),
      "i" ∷ i_ptr ↦ n ∗
      "Hin" ∷ in_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* (outgoing.map removeNodeCC ++ voters.map addNodeCC ++ learners.map addLearnerCC ++ (learnersNext.take (sint.nat n)).map addLearnerCC) ∗
      "Hcap" ∷ ownSliceCap raftpb.ConfChangeSingle s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (learnersNext.length : Int)⌝) $$ [i Hin id Hs Hcap]
  · iexists W64 0, s', zero_val w64
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hif' : sint.Z n < sint.Z cs.LearnersNext'.len := by simpa using Hif
    have Hlt : sint.nat n < learnersNext.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, learnersNext[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cs.LearnersNext'.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd', _root_.and_self]
    wp_apply wp_load_idlist_index cs.LearnersNext' (sint.Z n) _ _ x Hn.1 Hx $$ [$Hln] as Hln
    wp_apply wp_slice_literal (V := raftpb.ConfChangeSingle) [addLearnerCC x]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl2] as %s3 ⟨Hs, Hcap, -⟩
    wp_for_post
    have Htake : learnersNext.take (sint.nat (n + W64 1)) = learnersNext.take (sint.nat n) ++ [x] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]; rfl
    iframe
    iexists n + W64 1, s3, x
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  have Hif' : ¬ sint.Z n < sint.Z cs.LearnersNext'.len := by simpa using Hif
  have Hn' : sint.nat n = learnersNext.length := by word
  rw [Hn', List.take_length]
  iapply HΦ
  simp only [restoreOutCC, restoreInCC]
  iframe

end proof

end EtcdGrove
end Perennial
