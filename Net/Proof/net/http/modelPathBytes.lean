/-
The proof of `modelPathBytes` (`Net/Spec/net/http/modelPathBytes.lean`): the loop checks each byte
with `modelPathByte`.
-/
module

public import Net.Spec.net.http.modelPathBytes
public import Net.Spec.net.http.modelPathByte
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace net.http

theorem all_take_succ (s : List w8) (p : w8 → Bool) (i : Nat) (x : w8) (hx : s[i]? = some x) :
    (s.take (i + 1)).all p = ((s.take i).all p && p x) := by
  rw [List.take_add_one, hx]; simp [List.all_append]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem modelPathBytes.wp_proof (Hbyte : modelPathByte.spec (GF := GF) (hG := hG)) :
    modelPathBytes.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ s.length ∧ (s.take (sint.nat i)).all pathByte = true⌝ :
      IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_apply wp_string_len as %Hl
  by_cases hlt : sint.Z i < sint.Z (W64 (s.length : Int))
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    have hlen : sint.Z (W64 (s.length : Int)) = s.length := by word
    have hi : sint.nat i < s.length := by word
    obtain ⟨x, hx⟩ : ∃ x, s[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx]
    wp_auto
    wp_apply Hbyte
    cases hb : pathByte x
    · simp only [Bool.not_false]
      wp_auto
      wp_for_post
      have : s.all pathByte = false := by
        rw [List.all_eq_false]
        exact ⟨x, List.mem_of_getElem? hx, by simp [hb]⟩
      rw [this]
      iapply HΦ; itrivial
    · simp only [Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hn, all_take_succ s pathByte _ x hx, Hi.2.2, hb]
      refine ⟨by word, by omega, rfl⟩
  · simp only [hlt, decide_false, false_neq_true, _root_.decide_true,
      Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have hi : sint.nat i = s.length := by word
    have := Hi.2.2
    rw [hi, List.take_length] at this
    rw [this]
    iapply HΦ; itrivial

end proof

end net.http
end Perennial
