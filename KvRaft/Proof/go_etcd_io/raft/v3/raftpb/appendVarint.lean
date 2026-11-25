-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/appendVarint.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/appendVarint.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.appendVarint

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

theorem raftpb.appendVarint.wp_proof :
    raftpb.appendVarint.spec (GF := GF) (hG := hG) := by
  intro b B v
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  ihave IH : iprop(∃ (cur : GoSlice) (vc : w64) (e : List w8),
      "b" ∷ b_ptr ↦ cur ∗ "v" ∷ v_ptr ↦ vc ∗ "Hb" ∷ cur ↦* (B ++ e) ∗
      "Hcap" ∷ ownSliceCap w8 cur (DFrac.own 1) ∗
      "%He" ∷ ⌜e ++ varintEnc (uint.nat vc) = ccVarint v⌝) $$ [b v Hb Hcap]
  · iexists b, v, []
    simp only [List.append_nil]
    iframe
    ipureintro
    rfl
  wp_for IH
  wp_if_destruct
  · wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, -⟩
    wp_for_post
    iframe
    iexists b2, _, e ++ [W8 (uint.Z vc) ||| W8 128]
    rw [List.append_assoc]
    iframe
    ipureintro
    have hn : ¬ uint.nat vc < 128 := by word
    have hsh : uint.nat (vc >>> (W64 7)) = uint.nat vc / 128 := by word
    rw [← He, cc_varintEnc_ge _ hn, cc_w8_or_128, hsh]
    simp
  · wp_apply wp_slice_literal (V := w8) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, -⟩
    iapply HΦ
    iframe
    have hn : uint.nat vc < 128 := by word
    have hw : W8 (uint.Z vc) = W8 ((uint.nat vc : Nat) : Int) := by word
    rw [← He, cc_varintEnc_lt _ hn, hw, List.append_assoc]
    iframe

end proof

end EtcdGrove
end Perennial
