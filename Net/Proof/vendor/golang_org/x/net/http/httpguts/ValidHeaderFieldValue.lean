/-
The proof of `httpguts.ValidHeaderFieldValue`
(`Net/Spec/vendor/golang_org/x/net/http/httpguts/ValidHeaderFieldValue.lean`): the loop checks each
byte with `isCTL` and `isLWS` (proved here).
-/
module

public import Net.Spec.vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldValue
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace vendor.golang_org.x.net.http.httpguts

/-- The byte test `ValidHeaderFieldValue` makes. -/
def hvByte (c : w8) : Bool := decide (32 ≤ c.toNat ∧ c.toNat ≠ 127) || decide (c = W8 9)

theorem all_take_succ_v (s : List w8) (p : w8 → Bool) (i : Nat) (x : w8) (hx : s[i]? = some x) :
    (s.take (i + 1)).all p = ((s.take i).all p && p x) := by
  rw [List.take_add_one, hx]; simp [List.all_append]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : vendor.golang_org.x.net.http.httpguts.Assumptions]

theorem wp_isCTL (b : w8) :
    {{ (True : IProp GF) }}
      (App (Val (@! vendor.golang_org.x.net.http.httpguts.isCTL)) (Val #b))
    {{ RET #(decide (b.toNat < 32 ∨ b.toNat = 127)); True }} := by
  wp_start
  wp_auto
  all_goals repeat (first | wp_if_destruct | wp_auto)
  · rw [decide_eq_true (Or.inl (by word))]; iapply HΦ; itrivial
  · have : decide (b.toNat < 32 ∨ b.toNat = 127) = decide (b = W8 127) := by
      apply decide_eq_decide.mpr
      constructor
      · rintro (h | h)
        · exfalso; revert h; word
        · revert h; word
      · intro h; right; subst h; rfl
    rw [this]; iapply HΦ; itrivial

theorem wp_isLWS (b : w8) :
    {{ (True : IProp GF) }}
      (App (Val (@! vendor.golang_org.x.net.http.httpguts.isLWS)) (Val #b))
    {{ RET #(decide (b = W8 32 ∨ b = W8 9)); True }} := by
  wp_start
  wp_auto
  all_goals repeat (first | wp_if_destruct | wp_auto)
  · simp only [true_or, decide_true]; iapply HΦ; itrivial
  · have : decide (b = W8 32 ∨ b = W8 9) = decide (b = W8 9) := by
      apply decide_eq_decide.mpr
      constructor
      · rintro (h | h)
        · exfalso; simp_all
        · exact h
      · intro h; right; exact h
    rw [this]; iapply HΦ; itrivial

theorem hv_bad_all : ∀ x : w8, (x.toNat < 32 ∨ x.toNat = 127) → ¬ (x = W8 32 ∨ x = W8 9) →
    hvByte x = false := by decide

theorem hv_good_all : ∀ x : w8, ¬ ((x.toNat < 32 ∨ x.toNat = 127) ∧ ¬ (x = W8 32 ∨ x = W8 9)) →
    hvByte x = true := by decide

theorem hv_bad (x : w8) (h1 : x.toNat < 32 ∨ x.toNat = 127) (h2 : ¬ (x = W8 32 ∨ x = W8 9)) :
    hvByte x = false := hv_bad_all x h1 h2

theorem hv_good (x : w8) (h : ¬ ((x.toNat < 32 ∨ x.toNat = 127) ∧ ¬ (x = W8 32 ∨ x = W8 9))) :
    hvByte x = true := hv_good_all x h

theorem ValidHeaderFieldValue.wp_proof : ValidHeaderFieldValue.spec (GF := GF) (hG := hG) := by
  intro v
  show {{ _ }} _ {{ RET #(v.all hvByte); True }}
  wp_start
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ v.length ∧ (v.take (sint.nat i)).all hvByte = true⌝ :
      IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for HI
  wp_apply wp_string_len as %Hl
  by_cases hlt : sint.Z i < sint.Z (W64 (v.length : Int))
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    have hi : sint.nat i < v.length := by word
    obtain ⟨x, hx⟩ : ∃ x, v[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx]
    wp_auto
    wp_apply wp_isCTL
    by_cases hc : x.toNat < 32 ∨ x.toNat = 127
    · rw [decide_eq_true hc]
      wp_auto
      wp_apply wp_isLWS
      by_cases hw : x = W8 32 ∨ x = W8 9
      · rw [decide_eq_true hw]
        wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        rw [hn, all_take_succ_v v hvByte _ x hx, Hi.2.2, hv_good x (fun h => h.2 hw)]
        refine ⟨by word, by omega, rfl⟩
      · rw [decide_eq_false hw]
        wp_auto
        wp_for_post
        have : v.all hvByte = false := by
          rw [List.all_eq_false]
          exact ⟨x, List.mem_of_getElem? hx, by simp [hv_bad x hc hw]⟩
        rw [this]
        iapply HΦ; itrivial
    · rw [decide_eq_false hc]
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hn, all_take_succ_v v hvByte _ x hx, Hi.2.2, hv_good x (fun h => hc h.1)]
      refine ⟨by word, by omega, rfl⟩
  · simp only [hlt, decide_false, false_neq_true, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have hi : sint.nat i = v.length := by word
    have := Hi.2.2
    rw [hi, List.take_length] at this
    rw [this]
    iapply HΦ; itrivial

end proof

end vendor.golang_org.x.net.http.httpguts
end Perennial
