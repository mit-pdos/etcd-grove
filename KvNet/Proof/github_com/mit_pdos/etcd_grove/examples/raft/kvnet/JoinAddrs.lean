/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/JoinAddrs.lean`: the loop over the addresses, `s` the first `i` of them joined (`intercalate_snoc`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.JoinAddrs

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

theorem JoinAddrs.wp_proof : JoinAddrs.spec (GF := GF) (hG := hG) := by
  intro addrs dq l
  wp_start as Hsl
  try wp_auto
  rename Loc => iq_ptr
  irename : (iq_ptr ↦ W64 0 : IProp GF) => Hiq
  irename : (i_ptr ↦ zero_val w64 : IProp GF) => Hk
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (j k : w64) (x : GoString),
      "Hiq" ∷ iq_ptr ↦ j ∗ "Hk" ∷ i_ptr ↦ k ∗ "a" ∷ a_ptr ↦ x ∗
      "s" ∷ s_ptr ↦ List.intercalate [(44 : w8)] (l.take (sint.nat j)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z addrs.len⌝)
    $$ [Hiq Hk a s]
  · iexists W64 0, _, _
    iframe
    ipureintro; exact ⟨by decide, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hc : sint.Z j < sint.Z addrs.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hjl : sint.nat j < l.length := by rw [Hlen.1]; word
    obtain ⟨x0, Hx0⟩ : ∃ x0, l[sint.nat j]? = some x0 := ⟨_, List.getElem?_eq_getElem Hjl⟩
    try wp_auto
    rw [ite_eq_left (by omega)]
    wp_apply wp_load_slice_index addrs (sint.Z j) l dq x0 Hj.1 $$ [$Hsl] as Hsl
    · ipureintro; exact Hx0
    try wp_auto
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htk : l.take (sint.nat j + 1) = l.take (sint.nat j) ++ [x0] := by
      rw [List.take_add_one, Hx0]; rfl
    wp_if_destruct
    · try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, j, x0
      have hne : l.take (sint.nat j) ≠ [] := by
        intro h
        have := congrArg List.length h
        rw [List.length_take, List.length_nil] at this
        word
      rw [hj1, htk, intercalate_snoc, if_neg hne]
      iframe
      ipureintro; constructor <;> word
    · try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, j, x0
      have hj0 : sint.nat j = 0 := by word
      rw [hj1, htk, hj0]
      simp only [List.take_zero, List.nil_append, List.intercalate_singleton]
      iframe
      ipureintro; constructor <;> word
  · have Hjk : sint.nat j = l.length := by rw [Hlen.1]; word
    rw [Hjk, List.take_length]
    try wp_auto
    unfold joinAddrs
    iapply HΦ
    iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
