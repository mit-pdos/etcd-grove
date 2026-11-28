/- Lean-first (no Rocq counterpart).

`rvOfMsg`'s proof (notes/k8s-dist-k9.md §2.7, G14): the loop tries every start `i` with
`i + 32 ≤ len(msg)` in order, so its first match is `rvOfMsgL`'s `find?`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvOfMsg
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section pure

theorem find_range_some (p : Nat → Bool) (j : Nat) (hj : p j = true)
    (hk : ∀ k < j, p k = false) : ∀ n, j < n → (List.range n).find? p = some j
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.find?_append]
    rcases Nat.lt_or_ge j n with h' | h'
    · rw [find_range_some p j hj hk n h']; rfl
    · have hjn : j = n := by omega
      subst hjn
      rw [List.find?_eq_none.2 (fun k hk' => by simp [hk k (List.mem_range.1 hk')])]
      simp [hj]

/-- No match before `j`, none at or after it (too short): `rvOfMsgL` is `0`. -/
theorem rvOfMsgL_none (msg : GoString) (j : Nat) (hk : ∀ k < j, ¬ rvPatL <+: msg.drop k)
    (hj : msg.length < j + 32) : rvOfMsgL msg = 0 := by
  unfold rvOfMsgL
  rw [List.find?_eq_none.2]
  intro k _ hd
  have hp := of_decide_eq_true hd
  rcases Nat.lt_or_ge k j with h | h
  · exact hk k h hp
  · have := hp.length_le
    simp [rvPatL_length] at this
    omega

/-- The first match at `j`. -/
theorem rvOfMsgL_some (msg : GoString) (j : Nat) (hk : ∀ k < j, ¬ rvPatL <+: msg.drop k)
    (hj : rvPatL <+: msg.drop j) :
    rvOfMsgL msg = (parseRVD (msg.drop (j + 32))).getD 0 := by
  unfold rvOfMsgL
  have hlt : j < msg.length := by
    have := hj.length_le
    simp [rvPatL_length] at this
    omega
  rw [find_range_some _ j (decide_eq_true hj) (fun k hk' => decide_eq_false (hk k hk')) _ hlt]
  rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem rvOfMsg.wp_proof (wp_parseRV : parseRV.spec (GF := GF) (hG := hG)) :
    rvOfMsg.spec (GF := GF) (hG := hG) := by
  intro msg
  wp_start as -
  wp_auto
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ msg.length ∧
        ∀ k < sint.nat j, ¬ rvPatL <+: msg.drop k⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    refine ⟨by word, by word, fun k hk => ?_⟩
    exact absurd hk (by word)
  wp_for HI
  wp_apply (github_com.mit_pdos.perennial.goose.model.strings.wp_string_len_maxAddr msg) as %Hlen
  (try wp_auto)
  have hmax : (msg.length : Int) ≤ 2 ^ 47 := Hlen
  have hj32 : sint.Z (j + W64 32) = sint.Z j + 32 := by word
  have hnt : ¬ ((#false : val) = #true) := fun h => by have := go.intoVal_inj h; simp at this
  by_cases hlt : sint.Z (j + W64 32) ≤ sint.Z (W64 (msg.length : Int))
  case neg =>
    rw [decide_eq_false hlt, if_neg (by simpa using hnt)]
    (try wp_auto)
    (try rw [if_pos (by simp)])
    (try wp_auto)
    rw [rvOfMsgL_none msg (sint.nat j) Hj.2.2 (by word), show (0 : w64) = W64 0 from rfl]
    (try simp only [Option.getD_none, Option.getD_some, show (0 : w64) = W64 0 from rfl])
    iapply HΦ
    ipureintro; trivial
  rw [decide_eq_true hlt, if_pos (by simp)]
  have hs1 : 0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z (j + W64 32) ∧
      sint.Z (j + W64 32) ≤ (msg.length : Int) := ⟨Hj.1, by word, by word⟩
  iterate 3 ((try simp only [hs1, ↓reduceIte]); (try wp_auto))
  rw [show sint.nat (j + W64 32) - sint.nat j = rvPatL.length by rw [rvPatL_length]; word]
  rw [show (go!"ResourceVersion in object meta: " : GoString) = rvPatL from rfl]
  by_cases hm : rvPatL <+: msg.drop (sint.nat j)
  case neg =>
    rw [decide_eq_false (fun h => hm (List.prefix_iff_eq_take.2 h.symm))]
    (try wp_auto)
    wp_for_post
    iframe
    iexists (j + W64 1)
    iframe
    ipureintro
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    refine ⟨by word, by word, fun k hk => ?_⟩
    rw [hj1] at hk
    rcases Nat.lt_or_ge k (sint.nat j) with h | h
    · exact Hj.2.2 k h
    · rw [show k = sint.nat j by omega]; exact hm
  rw [decide_eq_true (List.prefix_iff_eq_take.1 hm).symm]
  (try wp_auto)
  wp_apply (github_com.mit_pdos.perennial.goose.model.strings.wp_string_len msg) as %Hlen2
  have hs2 : 0 ≤ sint.Z (j + W64 32) ∧ sint.Z (j + W64 32) ≤ sint.Z (W64 (msg.length : Int)) ∧
      sint.Z (W64 (msg.length : Int)) ≤ (msg.length : Int) := ⟨by word, hlt, by word⟩
  iterate 2 ((try simp only [hs2, ↓reduceIte]); (try wp_auto))
  have hres := rvOfMsgL_some msg (sint.nat j) Hj.2.2 hm
  have hd : List.take (sint.nat (W64 (msg.length : Int)) - sint.nat (j + W64 32))
      (List.drop (sint.nat (j + W64 32)) msg) = List.drop (sint.nat j + 32) msg := by
    rw [show sint.nat (j + W64 32) = sint.nat j + 32 by word]
    apply List.take_of_length_le
    simp only [List.length_drop]
    word
  rw [hd]
  wp_apply wp_parseRV as %r %err Hp
  rw [hres]
  rcases hp : parseRVD (List.drop (sint.nat j + 32) msg) with _ | m
  · icases Hp with ⟨%Hne, -, %Hr⟩
    subst Hr
    cases err with
    | nil => exact absurd rfl Hne
    | ok e =>
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    (try simp only [Option.getD_none, Option.getD_some, show (0 : w64) = W64 0 from rfl])
    iapply HΦ
    ipureintro; trivial
  · icases Hp with %Hp
    obtain ⟨rfl, rfl⟩ := Hp
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    (try simp only [Option.getD_none, Option.getD_some, show (0 : w64) = W64 0 from rfl])
    iapply HΦ
    ipureintro; trivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
