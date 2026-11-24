/-
The proof of `httpguts.ValidHeaderFieldName`
(`Net/Spec/vendor/golang_org/x/net/http/httpguts/ValidHeaderFieldName.lean`): the loop reads each
byte's entry of `isTokenTable`.
-/
module

public import Net.Spec.vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldName
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace vendor.golang_org.x.net.http.httpguts

theorem all_take_succ' (s : List w8) (p : w8 → Bool) (i : Nat) (x : w8) (hx : s[i]? = some x) :
    (s.take (i + 1)).all p = ((s.take i).all p && p x) := by
  rw [List.take_add_one, hx]; simp [List.all_append]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : vendor.golang_org.x.net.http.httpguts.Assumptions]

theorem ValidHeaderFieldName.wp_proof : ValidHeaderFieldName.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start as #Htab
  iunfold tokenTable at Htab
  icases Htab with ⟨%t, #Ht, %Htv⟩
  wp_auto
  wp_apply wp_string_len as %Hl0
  by_cases hv : v = []
  · subst hv
    simp only [List.length_nil, Int.cast_ofNat_Int, _root_.decide_true]
    wp_auto
    simp only [List.isEmpty_nil, Bool.not_true, Bool.false_and]
    iapply HΦ; itrivial
  have hne : (W64 (v.length : Int)) ≠ W64 0 := by
    intro h; apply hv; apply List.eq_nil_of_length_eq_zero; word
  simp only [hne, decide_false]
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ v.length ∧ (v.take (sint.nat i)).all net.http.fieldByte = true⌝ :
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
    have hb : 0 ≤ sint.Z (W64 (uint.Z x)) ∧ sint.Z (W64 (uint.Z x)) < 256 := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    have hidx : sint.Z (W64 (uint.Z x)) = (x.toNat : Int) := by word
    rw [hidx]
    have htx : t.arr[(x.toNat : Int).toNat]? = some (net.http.fieldByte x) := by
      simpa using Htv x
    ihave Hel := array_acc (globalAddr isTokenTable) (x.toNat : Int) DfracDiscarded 256 t
      (net.http.fieldByte x) (by omega) htx $$ Ht
    icases Hel with ⟨Hel, -⟩
    wp_auto
    cases hb : net.http.fieldByte x
    · simp only [Bool.not_false]
      wp_auto
      wp_for_post
      have : v.all net.http.fieldByte = false := by
        rw [List.all_eq_false]
        exact ⟨x, List.mem_of_getElem? hx, by simp [hb]⟩
      rw [this, Bool.and_false]
      iapply HΦ; itrivial
    · simp only [Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hn, all_take_succ' v net.http.fieldByte _ x hx, Hi.2.2, hb]
      refine ⟨by word, by omega, rfl⟩
  · simp only [hlt, decide_false, false_neq_true, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have hi : sint.nat i = v.length := by word
    have := Hi.2.2
    rw [hi, List.take_length] at this
    have hve : v.isEmpty = false := by cases v <;> simp_all
    rw [this, hve]; simp only [Bool.not_false, Bool.and_self]
    iapply HΦ; itrivial

end proof

end vendor.golang_org.x.net.http.httpguts
end Perennial
