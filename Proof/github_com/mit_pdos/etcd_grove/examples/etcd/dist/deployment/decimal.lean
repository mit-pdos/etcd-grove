/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/decimal.lean`: the guard (empty,
more than five digits, a leading zero), then the loop over the digits, `n` the value of the prefix
read (`digitsVal`), below `10 ^ i` (no overflow: at most five digits).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.decimal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Assumptions]

set_option hygiene false in
/-- `decimal`'s loop, from either way past the guard (`hg`). -/
local macro "decimal_loop" : tactic => `(tactic| (
  ihave HI : (∃ (i n : w64), "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ n ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ s.length ∧
        digitsVal (s.take (sint.nat i)) 0 = some (uint.nat n) ∧ uint.nat n < 10 ^ sint.nat i⌝ : IProp GF)
    $$ [i n]
  · iexists W64 0, W64 0
    iframe
    ipureintro
    refine ⟨by decide, by word, ?_, by decide⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; rfl
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · obtain ⟨Hi0, Hil, Hdv, Hlt⟩ := Hi
    have Hc : sint.Z i < sint.Z (W64 (s.length : Int)) := of_decide_eq_true (go.intoVal_inj Hif)
    have hil : sint.nat i < s.length := by word
    obtain ⟨d, hd⟩ : ∃ d, s[sint.nat i]? = some d := ⟨_, List.getElem?_eq_getElem hil⟩
    try wp_auto
    repeat (first | (simp only [Hi0, ↓reduceIte, hd]) | wp_auto)
    wp_if_destruct
    all_goals repeat (first | (simp only [Hi0, ↓reduceIte, hd]) | wp_auto)
    all_goals try wp_if_destruct
    all_goals repeat (first | (simp only [Hi0, ↓reduceIte, hd]) | wp_auto)
    rotate_left 2
    all_goals first
      | (wp_for_post
         iapply HΦ
         ipureintro
         simp only [Bool.false_eq_true, ↓reduceIte]
         rw [decimalM_ok _ _ hg, list_split_at s _ d hd, digitsVal_bad _ _ _ _ (isDigit_false_of (by word))]
         done)
      | (have hd48 : 48 ≤ d.toNat := by word
         have hd57 : d.toNat ≤ 57 := by word
         have hi4 : sint.nat i ≤ 4 := by
           have : s.length ≤ 5 := Nat.le_of_not_lt (fun h => hg (Or.inr (Or.inl h)))
           omega
         have hn : uint.nat n < 10000 :=
           Nat.lt_of_lt_of_le Hlt (Nat.pow_le_pow_right (by decide) hi4)
         have hv : uint.nat (n * W64 10 + W64 (uint.Z (d - W8 48))) = uint.nat n * 10 + (d.toNat - 48) := by
           word
         have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
         wp_for_post
         iframe
         iexists (i + W64 1), (n * W64 10 + W64 (uint.Z (d - W8 48)))
         iframe
         ipureintro
         refine ⟨by word, by word, ?_, ?_⟩
         · rw [hi1, hv, take_succ_of s _ d hd, digitsVal_snoc _ _ _ _ Hdv (isDigit_true_of hd48 hd57)]
         · rw [hi1, hv, Nat.pow_succ]
           omega)
  · obtain ⟨Hi0, Hil, Hdv, Hlt⟩ := Hi
    have Hge : ¬ sint.Z i < sint.Z (W64 (s.length : Int)) := fun h => Hif (by rw [decide_eq_true h])
    rw [decide_eq_false Hge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    iapply HΦ
    ipureintro
    have hil : sint.nat i = s.length := by word
    rw [hil, List.take_length] at Hdv
    rw [decimalM_ok _ _ hg, Hdv]
    by_cases hm : uint.nat n ≤ uint.nat mx
    · rw [decide_eq_true (by word : uint.Z n ≤ uint.Z mx)]; simp [hm]
    · rw [decide_eq_false (by word : ¬ uint.Z n ≤ uint.Z mx)]; simp [hm]
  ))

theorem deployment.decimal.wp_proof : etcd_dist.deployment.decimal.spec (GF := GF) (hG := hG) := by
  intro s mx
  wp_start
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · iapply HΦ
    ipureintro
    rw [decimalM_guard]
    · rfl
    · left; word
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · iapply HΦ
    ipureintro
    rw [decimalM_guard]
    · rfl
    · right; left; word
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · obtain ⟨c, t, hs⟩ : ∃ c t, s = c :: t := by
      cases s with
      | nil => simp at Hif
      | cons c t => exact ⟨c, t, rfl⟩
    have hc : s[0]? = some c := by rw [hs]; rfl
    try wp_auto
    simp only [hc]
    try wp_auto
    wp_if_destruct
    · iapply HΦ
      ipureintro
      rw [decimalM_guard]
      · rfl
      · right; right; refine ⟨by word, ?_⟩; simp [hs]
    have hg : ¬(s.length = 0 ∨ 5 < s.length ∨ (1 < s.length ∧ s.head? = some (48 : w8))) := by
      rintro (h | h | ⟨-, h⟩)
      · word
      · word
      · rw [hs] at h; simp only [List.head?_cons, Option.some.injEq] at h; exact Hif h
    decimal_loop
  · have hg : ¬(s.length = 0 ∨ 5 < s.length ∨ (1 < s.length ∧ s.head? = some (48 : w8))) := by
      rintro (h | h | ⟨h, -⟩) <;> word
    decimal_loop

end proof

end etcd_dist
end EtcdGrove
end Perennial
