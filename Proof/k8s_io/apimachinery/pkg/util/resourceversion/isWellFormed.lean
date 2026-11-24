/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/resourceversion/isWellFormed.lean`, over the real
code (`resourceversion.go`; until 2026-11-21 an axiom, names only for Goose's gap C1, the range over
a string). The loop tests the byte at each rune's start index (`go.runes`); while those bytes are
digits, every rune is one byte long (`decodeRune` of a byte below `0x80`), so the loop sees every
byte, and it returns what the byte loop would: `wellFormed s`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.resourceversion.isWellFormed
public import Spec.k8s_io.apimachinery.pkg.util.resourceversion.isDigit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace resourceversion

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.resourceversion

/-! ## The rune start indices of a string -/

/-- Every iteration of a range loop over `s` starts inside `s`. -/
private theorem runesFrom_lt (s : GoString) (fuel k : Nat) :
    ∀ p ∈ go.runesFrom s fuel k, p.1 < s.length := by
  induction fuel generalizing k with
  | zero => simp [go.runesFrom]
  | succ f ih =>
    simp only [go.runesFrom]
    split
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · assumption
      · exact ih _ p hp
    · simp

/-- A digit is below `0x80`, so it is a rune by itself. -/
private theorem decodeRune_digit (s : GoString) (k : Nat)
    (hd : digitB (s.getD k 0) = true) : (go.decodeRune s k).2 = k + 1 := by
  have h := digit_toNat hd
  have hb : (s.drop k).getD 0 0 = s.getD k 0 := by
    simp [List.getD_eq_getElem?_getD]
  have hlt : uint.Z (s.getD k 0) < 0x80 := by
    have : uint.Z (s.getD k 0) = (s.getD k 0).toNat := rfl
    omega
  unfold go.decodeRune
  simp only [hb, if_pos hlt]

/-- If the byte at every rune start from `k` on is a digit, so is every byte from `k` on. -/
private theorem all_digit_of_runesFrom (s : GoString) (fuel k : Nat) (hf : s.length - k ≤ fuel)
    (h : ∀ p ∈ go.runesFrom s fuel k, digitB (s.getD p.1 0) = true) :
    ∀ m, k ≤ m → m < s.length → digitB (s.getD m 0) = true := by
  induction fuel generalizing k with
  | zero => intro m h1 h2; omega
  | succ f ih =>
    intro m h1 h2
    have hk : k < s.length := by omega
    simp only [go.runesFrom, hk, ↓reduceIte, List.mem_cons, forall_eq_or_imp] at h
    have hd := h.1
    rw [decodeRune_digit s k hd] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact hd
    · exact ih (k + 1) (by omega) h.2 m (by omega) h2

/-- If the byte at every rune start is a digit, every byte is. -/
private theorem all_digit_of_runes (s : GoString)
    (h : ∀ p ∈ go.runes s, digitB (s.getD p.1 0) = true) : s.all digitB = true := by
  have := all_digit_of_runesFrom s s.length 0 (by omega) h
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
  have := this m (Nat.zero_le _) hm
  simpa [List.getD_eq_getElem?_getD, hm] using this

/-- `wellFormed` of a non-empty string without a leading `0`: all its bytes are digits. -/
private theorem wellFormed_iff (s : GoString) (hne : s ≠ []) (h0 : s.getD 0 0 ≠ W8 48) :
    wellFormed s = s.all digitB := by
  cases s with
  | nil => contradiction
  | cons c t =>
    simp only [List.getD_cons_zero] at h0
    simp only [wellFormed, decide_eq_true h0, Bool.true_and]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.resourceversion.Assumptions]

theorem isWellFormed.wp_proof
    (wp_isDigit : isDigit.spec (GF := GF) (hG := hG)) :
    isWellFormed.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  wp_func_call
  wp_call
  by_cases hlen : ((s).length : Int) ≤ maxAddr
  case neg =>
    rw [if_neg hlen]
    wp_apply wp_AngelicExit
  rw [if_pos hlen]
  have hlen_lt : (s).length < 2 ^ 63 := by unfold maxAddr at hlen; omega
  wp_auto
  wp_if_destruct
  · -- `len(s) == 0`
    have hs : s = [] := by
      apply List.eq_nil_of_length_eq_zero
      revert Hif; word
    subst hs
    rw [show wellFormed [] = false from rfl]
    iapply HΦ; itrivial
  have hne : s ≠ [] := by
    intro e; subst e; apply Hif; rfl
  have hpos : 0 < s.length := List.length_pos_iff.2 hne
  have h0 : s[0]? = some (s.getD 0 0) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos]
  rw [h0]
  wp_auto
  wp_if_destruct
  · -- `s[0] == '0'`
    have hw : wellFormed s = false := by
      cases s with
      | nil => contradiction
      | cons c t => simp_all [wellFormed]
    rw [hw]
    iapply HΦ; itrivial
  wp_apply (wp_string_for_range s _ (fun j => iprop(
      s_ptr ↦ s ∗ (∃ v : w64, i_ptr ↦ v) ∗ (∃ v : Bool, «$res0_ptr» ↦ v) ∗
      (True -∗ Φ #(wellFormed s)) ∗
      ⌜∀ p ∈ (go.runes s).take j, digitB (s.getD p.1 0) = true⌝))) $$ [s i «$res0» HΦ]
  · iframe s HΦ
    isplitl [i]
    · iexists _; iexact i
    isplitl [«$res0»]
    · iexists _; iexact «$res0»
    ipureintro
    simp
  · imodintro
    iintro %j %k %r %hk ⟨Hs, ⟨%v, Hi⟩, ⟨%rv, Hres⟩, HΦ, %Hall⟩
    have hkmem : (k, r) ∈ go.runes s := List.mem_of_getElem? hk
    have hklt : k < s.length := runesFrom_lt s s.length 0 _ hkmem
    have hidx : s[sint.nat (W64 (k : Int))]? = some (s.getD k 0) := by
      rw [show sint.nat (W64 (k : Int)) = k by word]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklt]
    have hnn : (0 : Int) ≤ sint.Z (W64 (k : Int)) := by word
    wp_auto
    simp only [hnn, ↓reduceIte, hidx]
    wp_auto
    wp_apply wp_isDigit
    cases hd : digitB (s.getD k 0)
    · -- not a digit: `return false`
      wp_auto
      iapply forRangePostcondition_return
      wp_auto
      have hw : wellFormed s = false := by
        rw [wellFormed_iff s hne Hif]
        rw [Bool.eq_false_iff]
        intro hall
        rw [List.all_eq_true] at hall
        have := hall (s.getD k 0) (by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklt])
        rw [hd] at this; contradiction
      rw [hw]
      iapply HΦ; itrivial
    · wp_auto
      iapply forRangePostcondition_do
      iframe
      ipureintro
      intro p hp
      rw [List.take_add_one, hk] at hp
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact Hall p hp
      · exact hd
  · iintro ⟨Hs, Hi, ⟨%rv, Hres⟩, HΦ, %Hall⟩
    rw [List.take_length] at Hall
    wp_auto
    have hw : wellFormed s = true := by
      rw [wellFormed_iff s hne Hif]
      exact all_digit_of_runes s Hall
    rw [hw]
    iapply HΦ; itrivial

end proof

end resourceversion
end EtcdGrove
end Perennial
