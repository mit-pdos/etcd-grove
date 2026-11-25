-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/consumeVarint.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/consumeVarint.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeVarint

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

theorem raftpb.consumeVarint.wp_proof :
    raftpb.consumeVarint.spec (GF := GF) (hG := hG) := by
  intro b dq bs i Hi0 Hilen
  wp_start as Hb
  ihave %Hlen := ownSlice_len $$ Hb
  wp_auto
  ihave IH : iprop(∃ (n i' vv sh : w64),
      "n" ∷ n_ptr ↦ n ∗ "i" ∷ i_ptr ↦ i' ∗ "v" ∷ v_ptr ↦ vv ∗ "shift" ∷ shift_ptr ↦ sh ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 10 ∧ 0 ≤ sint.Z i' ∧ sint.Z i' ≤ bs.length ∧
        ccVarintL bs (sint.nat i) =
          ccVarintLoop bs (10 - sint.nat n) (sint.nat n) (sint.nat i') vv sh⌝) $$ [n i v shift]
  · iexists W64 0, i, W64 0, W64 0
    iframe
    ipureintro
    exact ⟨by decide, by decide, Hi0, Hilen, rfl⟩
  wp_for IH
  wp_if_destruct
  · have hn10 : sint.nat n < 10 := by word
    obtain ⟨f, hf⟩ : ∃ f, 10 - sint.nat n = f + 1 := ⟨9 - sint.nat n, by omega⟩
    wp_if_destruct
    · wp_for_post
      iapply HΦ
      iframe
      ipureintro
      rw [Hinv.2.2.2.2, hf]
      simp only [ccVarintLoop]
      rw [List.getElem?_eq_none (by word)]
      trivial
    · have hlt : sint.nat i' < bs.length := by word
      obtain ⟨c, hc⟩ : ∃ c, bs[sint.nat i']? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
      simp only [show 0 ≤ sint.Z i' ∧ sint.Z i' < sint.Z b.len from ⟨Hinv.2.2.1, by word⟩]
      wp_apply wp_load_slice_index b (sint.Z i') bs dq c Hinv.2.2.1 $$ [Hb] as Hb
      · iframe; ipureintro; exact hc
      have Hst := Hinv.2.2.2.2
      rw [hf] at Hst
      simp only [ccVarintLoop, hc] at Hst
      have hb9 : ¬ (sint.nat n = 9 ∧ 1 < uint.Z c) →
          ccVarintL bs (sint.nat i) = (if uint.Z c < 128 then
            some (vv ||| W64 (uint.Z (c &&& W8 127)) <<< sh, sint.nat i' + 1)
            else ccVarintLoop bs f (sint.nat n + 1) (sint.nat i' + 1)
              (vv ||| W64 (uint.Z (c &&& W8 127)) <<< sh) (sh + W64 7)) := by
        intro h; rw [Hst, ite_eq_right h]
      -- (`word` only here, before the case splits: its cache leaks between sibling branches,
      -- `notes/perennial-changes.md`)
      have hZn : (sint.nat n : Int) = sint.Z n := by word
      have hZi : (sint.nat i' : Int) = sint.Z i' := by word
      have hj : sint.Z (i' + W64 1) = sint.Z i' + 1 := by word
      have hn1 : sint.Z (n + W64 1) = sint.Z n + 1 := by word
      have hsn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      have hsi1 : sint.nat (i' + W64 1) = sint.nat i' + 1 := by word
      have h9 : sint.nat n = 9 → n = W64 9 := by intro h; word
      have hs9 : sint.Z (W64 9) = 9 := rfl
      have hs0 : sint.Z (W64 0) = 0 := rfl
      have hs10 : sint.Z (W64 10) = 10 := rfl
      have hu1 : uint.Z (W8 1) = 1 := rfl
      have hu0 : uint.Z (W8 0) = 0 := rfl
      have hu128 : uint.Z (W8 128) = 128 := rfl
      have hcZ : 0 ≤ uint.Z c := by word
      have hlen' : (bs.length : Int) = sint.Z b.len := by word
      wp_if_destruct
      · -- n = 9
        wp_if_destruct
        · wp_for_post
          iapply HΦ
          iframe
          ipureintro
          rw [Hst, ite_eq_left ⟨by omega, by omega⟩]
        · have hc1 : uint.Z c ≤ 1 := by omega
          have Hs2 := hb9 (by omega)
          wp_if_destruct
          · wp_for_post
            iapply HΦ
            iframe
            ipureintro
            rw [Hs2, ite_eq_left (by omega)]
            exact ⟨rfl, rfl, by omega⟩
          · exfalso; omega
      · -- n ≠ 9
        have hn9 : sint.nat n ≠ 9 := fun h => Hif (h9 h)
        have Hs2 := hb9 (by rintro ⟨h, _⟩; exact hn9 h)
        wp_if_destruct
        · wp_for_post
          iapply HΦ
          iframe
          ipureintro
          rw [Hs2, ite_eq_left (by omega)]
          exact ⟨rfl, rfl, by omega⟩
        · wp_for_post
          iframe
          iexists n + W64 1, i' + W64 1, _, sh + W64 7
          iframe
          ipureintro
          refine ⟨by omega, ?_, by omega, by omega, ?_⟩
          · omega
          rw [Hs2, ite_eq_right (by omega), hsn1, hsi1, show 10 - (sint.nat n + 1) = f by omega]
  · iapply HΦ
    iframe
    ipureintro
    rw [Hinv.2.2.2.2, show 10 - sint.nat n = 0 by word]
    simp [ccVarintLoop]

end proof

end EtcdGrove
end Perennial
