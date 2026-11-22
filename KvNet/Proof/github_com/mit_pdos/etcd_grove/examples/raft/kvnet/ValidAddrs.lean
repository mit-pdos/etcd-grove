/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/ValidAddrs.lean`: the loop over the addresses, the prefix seen valid (`AddrOk`) and without repetition, the inner loop comparing the address with those before it.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ValidAddrs
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.AddrOk

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

theorem ValidAddrs.wp_proof (wp_AddrOk : AddrOk.spec (GF := GF) (hG := hG)) : ValidAddrs.spec (GF := GF) (hG := hG) := by
  intro addrs dq l voters hlen
  wp_start as Hsl
  try wp_auto
  rename Loc => iq_ptr
  irename : (iq_ptr ↦ W64 0 : IProp GF) => Hiq
  irename : (i_ptr ↦ zero_val w64 : IProp GF) => Hk
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (j k : w64) (x : GoString),
      "Hiq" ∷ iq_ptr ↦ j ∗ "Hk" ∷ i_ptr ↦ k ∗ "a" ∷ a_ptr ↦ x ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z addrs.len ∧
        (∀ b ∈ l.take (sint.nat j), addrOk b = true) ∧ (l.take (sint.nat j)).Nodup⌝)
    $$ [Hiq Hk a]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by decide, by word, ?_, ?_⟩ <;> simp [show sint.nat (0#64 : w64) = 0 from rfl]
  wp_for IH
  wp_if_destruct
  · obtain ⟨Hj0, Hjl', Hok, Hnd⟩ := Hj
    have Hc : sint.Z j < sint.Z addrs.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hjl : sint.nat j < l.length := by rw [Hlen.1]; word
    obtain ⟨x0, Hx0⟩ : ∃ x0, l[sint.nat j]? = some x0 := ⟨_, List.getElem?_eq_getElem Hjl⟩
    try wp_auto
    rw [ite_eq_left (by omega)]
    wp_apply wp_load_slice_index addrs (sint.Z j) l dq x0 Hj0 $$ [$Hsl] as Hsl
    · ipureintro; exact Hx0
    try wp_auto
    wp_apply wp_AddrOk _ (hlen x0 (List.mem_of_getElem? Hx0))
    have hmem : x0 ∈ l := List.mem_of_getElem? Hx0
    cases hb : addrOk x0
    · simp only [Bool.not_false]
      try wp_auto
      wp_for_post
      rw [validAddrs_bad l _ x0 hmem hb]
      iapply HΦ
      iframe
    simp only [Bool.not_true]
    try wp_auto
    rename Loc => m_ptr
    ihave IH2 : iprop(∃ (m : w64), "j" ∷ m_ptr ↦ m ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z j ∧ ∀ q, q < sint.nat m → l[q]? ≠ some x0⌝)
      $$ [j]
    · iexists W64 0
      iframe
      ipureintro
      refine ⟨by decide, Hj0, ?_⟩
      intro q hq; simp [show sint.nat (0#64 : w64) = 0 from rfl] at hq
    wp_for IH2
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    wp_if_destruct
    · obtain ⟨Hm0, Hmj, Hne⟩ := Hm
      have hml : sint.nat m < l.length := by word
      obtain ⟨y, Hy⟩ : ∃ y, l[sint.nat m]? = some y := ⟨_, List.getElem?_eq_getElem hml⟩
      try wp_auto
      rw [ite_eq_left (by omega)]
      wp_apply wp_load_slice_index addrs (sint.Z m) l dq y Hm0 $$ [$Hsl] as Hsl
      · ipureintro; exact Hy
      try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_for_post
        wp_for_post
        have e : y = x0 := by first | exact Hif | exact Hif.symm
        rw [validAddrs_dup l _ x0 (sint.nat m) (sint.nat j) (by word) (e ▸ Hy) Hx0]
        iapply HΦ
        iframe
      · try wp_auto
        wp_for_post
        iframe
        iexists m + W64 1
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        intro q hq
        rcases (show q < sint.nat m ∨ q = sint.nat m by word) with hq | rfl
        · exact Hne q hq
        · rw [Hy]; intro e; exact Hif (Option.some.inj e)
    · obtain ⟨Hm0, Hmj, Hne⟩ := Hm
      have hmj : sint.nat m = sint.nat j := by word
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, j, x0
      iframe
      ipureintro
      rw [hj1, take_succ_gs _ _ _ Hx0]
      refine ⟨by word, by word, ?_, ?_⟩
      · intro b hb'
        rcases List.mem_append.mp hb' with h | h
        · exact Hok b h
        · rw [List.mem_singleton.mp h]; exact hb
      · apply List.nodup_append.mpr
        refine ⟨Hnd, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro a ha b hb' e
        rw [List.mem_singleton.mp hb'] at e
        subst e
        exact not_mem_take_of (by rw [← hmj]; exact Hne) ha
  · obtain ⟨Hj0, Hjl', Hok, Hnd⟩ := Hj
    have Hjk : sint.nat j = l.length := by rw [Hlen.1]; word
    rw [Hjk, List.take_length] at Hok Hnd
    have Hv : ∀ b : Bool, b = decide (l.length < 2 ^ 32 ∧ 1 ≤ uint.nat voters ∧ uint.nat voters ≤ l.length) →
        b = validAddrs l (uint.nat voters) := by
      intro b hb; rw [hb]; unfold validAddrs
      apply decide_eq_decide.mpr
      exact ⟨fun h => ⟨Hok, Hnd, h⟩, fun h => h.2.2⟩
    have Hl1 := Hlen.1
    have Hl2 := Hlen.2
    wp_if_destruct
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        rw [Hv _ (decide_eq_decide.mpr ⟨fun h => ⟨by word, by word, by word⟩, fun h => by word⟩)]
        iapply HΦ; iframe
      · try wp_auto
        rw [Hv _ (decide_eq_false (fun h => by word)).symm]
        iapply HΦ; iframe
    · try wp_auto
      rw [Hv _ (decide_eq_false (fun h => by word)).symm]
      iapply HΦ; iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
