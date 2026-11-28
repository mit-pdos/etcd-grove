/-
(hraft_robust R3) The proof of `disk.bytesEq`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.disk

theorem dk_bytesEq_take_succ (xs bs : List w8) (i : Nat) (x : w8) (ha : xs[i]? = some x) (hb : bs[i]? = some x)
    (h : xs.take i = bs.take i) : xs.take (i + 1) = bs.take (i + 1) := by
  rw [List.take_add_one, List.take_add_one, ha, hb, h]

theorem dk_bytesEq_ne (xs bs : List w8) (i : Nat) (x y : w8) (ha : xs[i]? = some x) (hb : bs[i]? = some y)
    (hne : x ≠ y) : xs ≠ bs := by
  intro h; subst h; rw [ha] at hb; cases hb; exact hne rfl

theorem dk_bytesEq_eq (xs bs : List w8) (h1 : xs.length = bs.length) (h : xs.take xs.length = bs.take xs.length) :
    xs = bs := by
  rw [List.take_length] at h; rw [h, h1, List.take_length]

theorem github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.disk.bytesEq.spec (GF := GF) (hG := hG) := by
  intro a b dqa dqb xs bs
  wp_start as ⟨Ha, Hb⟩
  ihave %Hal := ownSlice_len _ _ _ $$ Ha
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_if_destruct
  · have hlen : xs.length = bs.length := by rw [Hal.1, Hbl.1, Hif]
    ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "Ha" ∷ a ↦*{dqa} xs ∗ "Hb" ∷ b ↦*{dqb} bs ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.len ∧ xs.take (sint.nat i) = bs.take (sint.nat i)⌝ : IProp GF)
        $$ [i Ha Hb]
    · iexists W64 0; iframe; ipureintro; exact ⟨by word, Hal.2, rfl⟩
    wp_for HI
    wp_if_destruct
    · have hlt := Hif
      have hil : sint.nat i < xs.length := dk_idx_lt i a.len _ Hal Hi.1 Hif
      have hil' : sint.nat i < bs.length := by omega
      list_elem xs (sint.nat i) as x
      list_elem bs (sint.nat i) as y
      have hb2 : sint.Z i < sint.Z b.len := by
        have : sint.nat i < sint.nat b.len := by rw [← Hbl.1]; exact hil'
        word
      simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.len from ⟨Hi.1, Hif⟩, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index a (sint.Z i) xs dqa x Hi.1) $$ [$Ha] as Ha
      · ipureintro; rw [dk_toNat_sint]; exact Hx_lookup
      simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len from ⟨Hi.1, hb2⟩, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index b (sint.Z i) bs dqb y Hi.1) $$ [$Hb] as Hb
      · ipureintro; rw [dk_toNat_sint]; exact Hy_lookup
      wp_if_destruct
      · wp_for_post
        iframe
        iexists i + W64 1
        obtain ⟨hs1, hs2, hs3⟩ := dk_idx_succ i a.len Hi.1 hlt
        iframe
        ipureintro
        refine ⟨hs2, hs3, ?_⟩
        rw [hs1]
        subst Hif
        exact dk_bytesEq_take_succ xs bs _ x Hx_lookup Hy_lookup Hi.2.2
      · have hne : xs ≠ bs := dk_bytesEq_ne xs bs _ x y Hx_lookup Hy_lookup Hif
        rw [decide_eq_false hne]
        wp_for_post
        iapply HΦ; iframe
    · have heq : xs = bs := by
        have := dk_idx_eq i a.len _ Hal Hi.2.1 Hif
        rw [this] at Hi
        exact dk_bytesEq_eq xs bs hlen Hi.2.2
      rw [decide_eq_true heq]
      iapply HΦ; iframe
  · have hne : xs ≠ bs := by
      intro h; subst h; apply Hif; rw [Hal.1] at Hbl; word
    rw [decide_eq_false hne]
    iapply HΦ; iframe

end proof

end Perennial
