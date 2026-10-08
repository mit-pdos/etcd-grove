/-
Proof of `Spec/confchange_toConfChangeSingle.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Raft.Spec.confchange_toConfChangeSingle

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

theorem confchange.toConfChangeSingle.wp_proof :
    confchange.toConfChangeSingle.spec (GF := GF) (hG := hG) := by
  intro cs voters dq Hvo Hl Hln
  wp_start as Hvs
  -- `in` is a Lean keyword: name its cell by hand before `wp_auto` names the others
  wp_pures
  wp_alloc in_ptr as Hin
  wp_auto
  -- `for _, id := range cs.VotersOutgoing` (twice), `cs.Learners`, `cs.LearnersNext`: the
  -- slices are empty, so each loop exits at its first test
  wp_for
  wp_if_destruct
  · exfalso; rw [Hvo] at Hif; word
  wp_for
  wp_if_destruct
  · exfalso; rw [Hvo] at Hif; word
  -- `for _, id := range cs.Voters { in = append(in, AddNode id) }`: after `n` iterations
  -- `in` holds the first `n` voters' changes
  ihave Hnil : (slice.nil ↦* ([] : List raftpb.ConfChangeSingle)) $$ []
  · iapply ownSlice_nil
  ihave Hcap : ownSliceCap raftpb.ConfChangeSingle slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave %Hvlen := ownSlice_len $$ Hvs
  ihave IH : iprop(∃ (n : w64) (s' : GoSlice) (x : w64),
      "i" ∷ i_ptr ↦ n ∗
      "Hin" ∷ in_ptr ↦ s' ∗
      "id" ∷ id_ptr ↦ x ∗
      "Hs" ∷ s' ↦* (voters.take (sint.nat n)).map addNodeCC ∗
      "Hcap" ∷ ownSliceCap raftpb.ConfChangeSingle s' (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (voters.length : Int)⌝) $$ [i Hin id Hnil Hcap]
  · iexists W64 0, slice.nil, zero_val w64
    simp only [named, show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < voters.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, voters[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cs.Voters'.len := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self]
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
    iframe HΦ Hvs out cs
    iexists n + W64 1, s3, x
    simp only [named, Htake, List.map_append, List.map_cons, List.map_nil]
    iframe
    ipureintro; constructor <;> word
  · -- the loop is over: `in` holds every voter's change. Two more empty ranges, then
    -- `return out, in`
    have Hn' : sint.nat n = voters.length := by word
    rw [Hn', List.take_length]
    wp_for
    wp_if_destruct
    · exfalso; rw [Hl] at Hif; word
    wp_for
    wp_if_destruct
    · exfalso; rw [Hln] at Hif; word
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
