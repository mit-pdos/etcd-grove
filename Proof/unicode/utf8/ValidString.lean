/-
Proof of `Spec/unicode/utf8/ValidString.lean` (until 2026-10-26 an axiom, the package names-only).
Lean-first.
-/
module

public import Spec.unicode.utf8.ValidString
public import Spec.unicode.utf8.word
public import Proof.unicode.utf8.ValidTable

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.unicode.utf8.Assumptions]

set_option hygiene false in
/-- `return false`, `Hsr` saying that the string is not valid. -/
local macro "ret_false" : tactic => `(tactic| (
  iapply HΦ
  ipureintro
  try simp at Hsr
  simp [utf8Valid, Hsr]))

set_option hygiene false in
/-- A failing check `if <cond> { return false }`: `h : t` (the check passes) after it, `Hsr` saying
that the string is not valid in the failing case. -/
local macro "chk" h:ident " : " t:term : tactic => `(tactic| (
  wp_if_destruct
  · have hn : ¬ ($t) := by revert Hif; word
    simp [hn] at Hsr
    wp_for_post
    ret_false
  have $h : $t := by revert Hif; word))

/-- A slice `s[k:]` of a string `s` with `k ≤ len(s)`, its length `Hl : s.length < 2 ^ 63` in
the context: in bounds, and `s.drop k`. -/
local macro "slice_ok" : tactic => `(tactic| (
  rw [ite_eq_left (by simp only [List.length_cons] at *; refine ⟨?_, ?_, ?_⟩ <;> word)]
  rw [List.take_of_length_le (by simp only [List.length_drop, List.length_cons] at *; word)]))

theorem utf8.ValidString.wp_proof (wp_word : utf8.word.spec (GF := GF) (hG := hG)) :
    utf8.ValidString.spec (GF := GF) (hG := hG) := fun str => by
  wp_start
  ihave #Hi : (utf8.utf8Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨#Hfirst, #Hacc⟩
  wp_auto
  ihave HI : (∃ (sr : GoString), "s" ∷ s_ptr ↦ sr ∗
      "%Hsr" ∷ ⌜utf8ValidB sr = utf8ValidB str⌝ : IProp GF) $$ [s]
  · iexists str
    iframe
    ipureintro; rfl
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · obtain ⟨b, rest, rfl⟩ : ∃ b rest, sr = b :: rest := by
      match sr, Hif with
      | b :: rest, _ => exact ⟨b, rest, rfl⟩
      | [], h => exact absurd (go.intoVal_inj h) Bool.false_ne_true
    simp only [List.getElem?_cons_zero]
    wp_auto
    wp_if_destruct
    · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      slice_ok
      simp only [List.drop_succ_cons, List.drop_zero]
      have Hr : utf8ValidB rest = utf8ValidB str := by
        rw [← Hsr, utf8ValidB_cons_ascii b rest (by revert Hif; word)]
      wp_auto
      wp_join iprop(∃ (sr : GoString), s_ptr ↦ sr ∗ ⌜utf8ValidB sr = utf8ValidB str⌝) at next
        with [s] as ⟨%sr2, s, %Hsr2⟩
      · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl1
        wp_if_destruct
        · have H8 := Hif
          clear Hif
          wp_apply (wp_word rest (by revert H8; word))
          wp_if_destruct
          · -- `rest`'s first eight bytes are ASCII: `s = rest[8:]`
            have Hr1 := utf8.validB_drop8_at rest 0 (by revert H8; word) (by simpa using Hif)
            simp only [List.drop_zero, Nat.zero_add] at Hr1
            have Hv1 : utf8ValidB (rest.drop 8) = utf8ValidB str := by rw [Hr1, Hr]
            clear Hif
            wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
            slice_ok
            wp_auto
            wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl2
            wp_if_destruct
            · have H16 := Hif
              clear Hif
              wp_apply (wp_word (rest.drop 8) (by simp only [List.length_drop] at *; word))
              wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
              slice_ok
              wp_apply (wp_word ((rest.drop 8).drop 8) (by simp only [List.length_drop] at *; word))
              wp_if_destruct
              · -- sixteen more ASCII bytes: `s = s[16:]`, then the loop
                obtain ⟨Hm1, Hm2⟩ := utf8.or_mask _ _ _ Hif
                have Ha := utf8.validB_drop8_at (rest.drop 8) 0
                  (by simp only [List.length_drop] at *; word) (by simpa using Hm1)
                have Hb := utf8.validB_drop8_at (rest.drop 8) 8
                  (by simp only [List.length_drop] at *; word) Hm2
                simp only [List.drop_zero, Nat.zero_add, Nat.reduceAdd] at Ha Hb
                clear Hif
                wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
                slice_ok
                wp_auto
                ihave HJ : (∃ (sr : GoString), "s" ∷ s_ptr ↦ sr ∗
                    "%Hj" ∷ ⌜utf8ValidB sr = utf8ValidB str⌝ : IProp GF) $$ [s]
                · iexists _
                  iframe
                  ipureintro
                  rw [Hb, Ha, Hv1]
                wp_for HJ
                wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl4
                wp_if_destruct
                · have H32 := Hif
                  clear Hif
                  wp_apply (wp_word sr (by revert H32; word))
                  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
                  slice_ok
                  wp_apply (wp_word (sr.drop 8) (by simp only [List.length_drop] at *; word))
                  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
                  slice_ok
                  wp_apply (wp_word (sr.drop 16) (by simp only [List.length_drop] at *; word))
                  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
                  slice_ok
                  wp_apply (wp_word (sr.drop 24) (by simp only [List.length_drop] at *; word))
                  wp_if_destruct
                  · -- 32 ASCII bytes: `s = s[32:]`
                    obtain ⟨Hm12, Hm34⟩ := utf8.or_mask _ _ _ (of_decide_eq_true (go.intoVal_inj Hif))
                    obtain ⟨Hm1, Hm2⟩ := utf8.or_mask _ _ _ Hm12
                    obtain ⟨Hm3, Hm4⟩ := utf8.or_mask _ _ _ Hm34
                    have Ha := utf8.validB_drop8_at sr 0 (by revert H32; word) (by simpa using Hm1)
                    have Hb := utf8.validB_drop8_at sr 8 (by revert H32; word) Hm2
                    have Hc := utf8.validB_drop8_at sr 16 (by revert H32; word) Hm3
                    have Hd := utf8.validB_drop8_at sr 24 (by revert H32; word) Hm4
                    simp only [List.drop_zero, Nat.zero_add, Nat.reduceAdd] at Ha Hb Hc Hd
                    clear Hif
                    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
                    slice_ok
                    wp_auto
                    wp_for_post
                    iframe
                    iexists (sr.drop 32)
                    iframe
                    ipureintro
                    rw [Hd, Hc, Hb, Ha, Hj]
                  · rw [ite_eq_right (fun h => Hif (by rw [h]))]
                    isplitl []
                    · itrivial
                    iexists sr
                    iframe
                    ipureintro; exact Hj
                · isplitl []
                  · itrivial
                  iexists sr
                  iframe
                  ipureintro; exact Hj
              · wp_join_done
                iexists (rest.drop 8)
                iframe
                ipureintro; exact Hv1
            · wp_join_done
              iexists (rest.drop 8)
              iframe
              ipureintro; exact Hv1
          · wp_join_done
            iexists rest
            iframe
            ipureintro; exact Hr
        · wp_join_done
          iexists rest
          iframe
          ipureintro; exact Hr
      wp_for_post
      iframe
      iexists sr2
      iframe
      ipureintro; exact Hsr2
    · -- a leading byte: the tables
      have Hb80 : 0x80 ≤ b.toNat := by revert Hif; word
      have Hbi : sint.Z (W64 (uint.Z b)) = (b.toNat : Int) := by word
      rw [ite_eq_left (by rw [Hbi]; have := b.isLt; omega)]
      icases array_acc (GF := GF) _ (sint.Z (W64 (uint.Z b))) _ _ _ (utf8.firstEntry b.toNat)
        (by rw [Hbi]; omega)
        (by rw [Hbi]; exact utf8.firstTable_lookup b.toNat b.isLt) $$ Hfirst with ⟨#Hx, -⟩
      wp_auto
      have Hk := utf8.firstEntry_hi b.toNat b.isLt
      have Hki : sint.Z (W64 (uint.Z (utf8.firstEntry b.toNat >>> W64 4))) =
          (((utf8.firstEntry b.toNat).toNat / 16 : Nat) : Int) := by
        rw [utf8.shr4]; word
      rw [ite_eq_left (by rw [Hki]; omega)]
      icases array_acc (GF := GF) _ (sint.Z (W64 (uint.Z (utf8.firstEntry b.toNat >>> W64 4)))) _ _ _
        (⟨(utf8.accPair ((utf8.firstEntry b.toNat).toNat / 16)).1,
          (utf8.accPair ((utf8.firstEntry b.toNat).toNat / 16)).2⟩ : unicode.utf8.acceptRange)
        (by rw [Hki]; omega)
        (by rw [Hki]; exact utf8.acceptTable_lookup _ Hk) $$ Hacc with ⟨#Ha, -⟩
      rw [utf8.validB_lead b rest Hb80] at Hsr
      wp_auto
      wp_if_destruct
      · have Hsz : (utf8.firstEntry b.toNat &&& W8 7).toNat = 2 := by revert Hif; word
        simp only [Hsz, ↓reduceIte] at Hsr
        generalize utf8.accPair ((utf8.firstEntry b.toNat).toNat / 16) = p at Hsr ⊢
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
        wp_if_destruct
        · obtain rfl : rest = [] := by
            rcases rest with _ | ⟨c, r⟩
            · rfl
            · simp only [List.length_cons] at Hif Hl; word
          wp_for_post
          ret_false
        · obtain ⟨c1, r, rfl⟩ : ∃ c1 r, rest = c1 :: r := by
            rcases rest with _ | ⟨c, r⟩
            · simp only [List.length_cons, List.length_nil] at Hif Hl; word
            · exact ⟨c, r, rfl⟩
          simp only at Hsr
          wp_auto
          chk h1 : p.1.toNat ≤ c1.toNat
          chk h2 : c1.toNat ≤ p.2.toNat
          simp [h1, h2] at Hsr
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
          slice_ok
          simp only [List.drop_succ_cons, List.drop_zero]
          wp_auto
          wp_for_post
          iframe
          iexists r
          iframe
          ipureintro; exact Hsr
      have Hsz2 : (utf8.firstEntry b.toNat &&& W8 7).toNat ≠ 2 := by revert Hif; word
      wp_if_destruct
      · have Hsz : (utf8.firstEntry b.toNat &&& W8 7).toNat = 3 := by revert Hif; word
        simp only [Hsz, ↓reduceIte] at Hsr
        generalize utf8.accPair ((utf8.firstEntry b.toNat).toNat / 16) = p at Hsr ⊢
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
        wp_if_destruct
        · rcases rest with _ | ⟨c1, _ | ⟨c2, r⟩⟩
          · wp_for_post
            ret_false
          · wp_for_post
            ret_false
          · exfalso; simp only [List.length_cons] at Hif Hl; word
        · obtain ⟨c1, c2, r, rfl⟩ : ∃ c1 c2 r, rest = c1 :: c2 :: r := by
            rcases rest with _ | ⟨c1, _ | ⟨c2, r⟩⟩
            · simp only [List.length_cons, List.length_nil] at Hif Hl; word
            · simp only [List.length_cons, List.length_nil] at Hif Hl; word
            · exact ⟨c1, c2, r, rfl⟩
          simp only at Hsr
          wp_auto
          chk h1 : p.1.toNat ≤ c1.toNat
          chk h2 : c1.toNat ≤ p.2.toNat
          chk h3 : 0x80 ≤ c2.toNat
          chk h4 : c2.toNat ≤ 0xBF
          simp [h1, h2, h3, h4] at Hsr
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
          slice_ok
          simp only [List.drop_succ_cons, List.drop_zero]
          wp_auto
          wp_for_post
          iframe
          iexists r
          iframe
          ipureintro; exact Hsr
      have Hsz3 : (utf8.firstEntry b.toNat &&& W8 7).toNat ≠ 3 := by revert Hif; word
      wp_if_destruct
      · have Hsz : (utf8.firstEntry b.toNat &&& W8 7).toNat = 4 := by revert Hif; word
        simp only [Hsz, ↓reduceIte] at Hsr
        generalize utf8.accPair ((utf8.firstEntry b.toNat).toNat / 16) = p at Hsr ⊢
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
        wp_if_destruct
        · rcases rest with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, r⟩⟩⟩
          · wp_for_post
            ret_false
          · wp_for_post
            ret_false
          · wp_for_post
            ret_false
          · exfalso; simp only [List.length_cons] at Hif Hl; word
        · obtain ⟨c1, c2, c3, r, rfl⟩ : ∃ c1 c2 c3 r, rest = c1 :: c2 :: c3 :: r := by
            rcases rest with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, r⟩⟩⟩
            · simp only [List.length_cons, List.length_nil] at Hif Hl; word
            · simp only [List.length_cons, List.length_nil] at Hif Hl; word
            · simp only [List.length_cons, List.length_nil] at Hif Hl; word
            · exact ⟨c1, c2, c3, r, rfl⟩
          simp only at Hsr
          wp_auto
          chk h1 : p.1.toNat ≤ c1.toNat
          chk h2 : c1.toNat ≤ p.2.toNat
          chk h3 : 0x80 ≤ c2.toNat
          chk h4 : c2.toNat ≤ 0xBF
          chk h5 : 0x80 ≤ c3.toNat
          chk h6 : c3.toNat ≤ 0xBF
          simp [h1, h2, h3, h4, h5, h6] at Hsr
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
          slice_ok
          simp only [List.drop_succ_cons, List.drop_zero]
          wp_auto
          wp_for_post
          iframe
          iexists r
          iframe
          ipureintro; exact Hsr
      -- no sequence starts with `b`
      have Hsz4 : (utf8.firstEntry b.toNat &&& W8 7).toNat ≠ 4 := by revert Hif; word
      simp only [Hsz2, Hsz3, Hsz4, ↓reduceIte] at Hsr
      wp_for_post
      ret_false
  · -- `s` is empty: valid
    have H0 : ¬ sint.Z (W64 0) < sint.Z (W64 (sr.length : Int)) :=
      fun h => Hif (by rw [decide_eq_true h])
    rw [ite_eq_right (by simpa using H0)]
    obtain rfl : sr = [] := List.eq_nil_of_length_eq_zero (by revert H0; word)
    wp_auto
    iapply HΦ
    ipureintro
    simp [utf8Valid, ← Hsr, utf8ValidB]

end proof

end EtcdGrove
end Perennial
