/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/nameOk.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.nameOk

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

theorem nameOk.wp_proof :
    etcd_dist.nameOk.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  wp_if_destruct
  · rw [show typed.nameOk [] = false from rfl]
    wp_end
  · have Hne := Hif
    wp_apply wp_string_to_bytes n as %sl ⟨Hsl, -⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    ihave HI : (∃ (j : Nat) (cv : w8), "i" ∷ i_ptr ↦ W64 j ∗ "c" ∷ c_ptr ↦ cv ∗ "Hsl" ∷ sl ↦* n ∗
        "%Hj" ∷ ⌜j ≤ n.length ∧ (n.take j).all nameByteOk = true⌝ : IProp GF) $$ [i c Hsl]
    · iexists 0, _
      iframe
      ipureintro; simp
    wp_for HI
    obtain ⟨Hj1, Hj2⟩ := Hj
    wp_if_destruct
    · have hj : j < n.length := by word
      have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
      have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
      simp only [h0, hc, and_self, ↓reduceIte]
      have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
      obtain ⟨b, hb⟩ : ∃ b, n[j]? = some b := ⟨_, List.getElem?_eq_getElem hj⟩
      wp_apply (wp_load_slice_index sl (sint.Z (W64 (j : Int))) n (DFrac.own 1) b h0) $$ [Hsl] as Hsl
      · iframe; ipureintro; rw [hsj]; exact hb
      have htake : n.take (j + 1) = n.take j ++ [b] := by
        rw [List.take_add_one, hb]; rfl
      have hbz : uint.Z b = (b.toNat : Int) := rfl
      have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
      by_cases hok : nameByteOk b = true
      · have hok' := (nameByteOk_iff b).1 hok
        repeat' wp_if_destruct
        all_goals first
          | (exfalso; word)
          | (exfalso; simp_all; omega)
          | skip
        all_goals
          wp_for_post
          iframe
          iexists (j + 1), _
          rw [hw]
          iframe
          ipureintro
          refine ⟨hj, ?_⟩
          rw [htake, List.all_append, Hj2]
          simpa using hok
      · have e : typed.nameOk n = false := by
          have hm : b ∈ n := List.mem_of_getElem? hb
          unfold typed.nameOk
          rw [Bool.and_eq_false_iff]
          right
          rw [List.all_eq_false]
          exact ⟨b, hm, by simpa [nameByteOk] using hok⟩
        rw [e]
        have hok' : ¬ ((48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨
            (97 ≤ b.toNat ∧ b.toNat ≤ 122) ∨ b.toNat = 45) := fun h => hok ((nameByteOk_iff b).2 h)
        repeat' wp_if_destruct
        all_goals first
          | (exfalso; word)
          | (exfalso; simp_all; omega)
          | skip
        all_goals
          wp_for_post
          wp_end
    · have hjl : j = n.length := by word
      subst hjl
      rw [List.take_length] at Hj2
      have e : typed.nameOk n = true := by
        unfold typed.nameOk
        simp only [Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨by simpa [List.isEmpty_iff] using Hne, Hj2⟩
      rw [e]
      wp_end

end proof

end etcd_dist
end EtcdGrove
end Perennial
