/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/SplitAddrs.lean`: the loop over `s`, the addresses so far followed by the pieces of the rest from `start` being `splitAddrs s` (`splitBy_append_free`), no comma in `s[start:i]`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.SplitAddrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem SplitAddrs.wp_proof : SplitAddrs.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  try wp_auto
  ihave HI : (∃ (j st : w64) (av : GoSlice) (L : List GoString),
      "i" ∷ i_ptr ↦ j ∗ "start" ∷ start_ptr ↦ st ∗ "addrs" ∷ addrs_ptr ↦ av ∗
      "Hav" ∷ av ↦* L ∗ "Hcap" ∷ ownSliceCap GoString av (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z st ∧ sint.Z st ≤ sint.Z j ∧ sint.nat j ≤ s.length ∧
        L ++ splitBy 44 (s.drop (sint.nat st)) [] = splitAddrs s ∧
        (44 : w8) ∉ (s.drop (sint.nat st)).take (sint.nat j - sint.nat st)⌝ : IProp GF)
    $$ [i start addrs]
  · iexists W64 0, W64 0, slice.nil, []
    iframe
    isplitl; · iapply ownSlice_nil
    isplitl; · iapply ownSliceCap_nil
    ipureintro
    refine ⟨by decide, by decide, by simp, ?_, by simp⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp [splitAddrs]
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · obtain ⟨Hst0, Hstj, Hjl, HL, Hfree⟩ := Hj
    have Hc : sint.Z j < sint.Z (W64 (s.length : Int)) := of_decide_eq_true (go.intoVal_inj Hif)
    have Hj0 : 0 ≤ sint.Z j := by omega
    have hjl : sint.nat j < s.length := by word
    obtain ⟨d, hd⟩ : ∃ d, s[sint.nat j]? = some d := ⟨_, List.getElem?_eq_getElem hjl⟩
    repeat (first | (simp only [Hj0, ↓reduceIte, hd]) | wp_auto)
    have hdd : (s.drop (sint.nat st))[sint.nat j - sint.nat st]? = some d := by
      rw [List.getElem?_drop, show sint.nat st + (sint.nat j - sint.nat st) = sint.nat j by word]
      exact hd
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    wp_if_destruct
    · rw [if_pos ⟨Hst0, Hstj, by word⟩]
      try wp_auto
      wp_apply wp_slice_literal (V := GoString) [(s.drop (sint.nat st)).take (sint.nat j - sint.nat st)]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hav $Hcap $Hsl2] as %sl' ⟨Hav, Hcap, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, j + W64 1, sl', _
      iframe
      ipureintro
      have hsplit := list_split_at _ _ _ hdd
      rw [show W8 44 = (44 : w8) from rfl] at hsplit
      refine ⟨by word, Int.le_refl _, by word, ?_, by simp⟩
      have key : splitBy 44 (List.drop (sint.nat st) s) [] =
          (List.drop (sint.nat st) s).take (sint.nat j - sint.nat st) ::
            splitBy 44 (List.drop (sint.nat (j + W64 1)) s) [] := by
        conv => lhs; rw [hsplit]
        rw [splitBy_free_sep _ _ _ Hfree, List.drop_drop, hj1,
          show sint.nat st + (sint.nat j - sint.nat st + 1) = sint.nat j + 1 by word]
      rw [← HL, key]
      simp
    · try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, st, av, L
      iframe
      ipureintro
      refine ⟨Hst0, by word, by word, HL, ?_⟩
      rw [hj1, show sint.nat j + 1 - sint.nat st = (sint.nat j - sint.nat st) + 1 by word,
        take_succ_of _ _ _ hdd]
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hfree, fun e => Hif e.symm⟩
  · obtain ⟨Hst0, Hstj, Hjl, HL, Hfree⟩ := Hj
    have Hge : ¬ sint.Z j < sint.Z (W64 (s.length : Int)) := fun h => Hif (by rw [decide_eq_true h])
    have hjl : sint.nat j = s.length := by word
    rw [decide_eq_false Hge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    rw [if_pos ⟨Hst0, by word, by word⟩]
    try wp_auto
    wp_apply wp_slice_literal (V := GoString) [_]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hav $Hcap $Hsl2] as %sl' ⟨Hav, Hcap, -⟩
    try wp_auto
    iapply HΦ
    rw [hjl] at Hfree
    have hw : sint.nat (W64 (s.length : Int)) = s.length := by word
    rw [hw, ← HL, List.take_of_length_le (by simp), splitBy_free _ _ (by
      rwa [List.take_of_length_le (by simp)] at Hfree)]
    iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
