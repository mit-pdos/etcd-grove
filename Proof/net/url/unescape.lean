/-
The proof of `unescape.spec` (`Spec/net/url/unescape.lean`), over Perennial's `strings.Builder.Grow`,
`WriteByte` and `String`. `len(s) + 1` is within `int` as a string is no longer than the address
space (`wp_string_len_maxAddr`).
-/
module

public import Spec.net.url.unescape
public import Spec.net.url.ishex
public import Spec.net.url.unhex
public import Spec.net.url.shouldEscape
public import Perennial.Spec.strings.Builder__Grow
public import Perennial.Spec.strings.Builder__WriteByte
public import Perennial.Spec.strings.Builder__String
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len wp_string_len_maxAddr)

namespace net.url

/-! ### Lists -/

theorem drop_cons_of (s : List w8) (i : Nat) (c : w8) (h : s[i]? = some c) :
    s.drop i = c :: s.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.drop_eq_getElem_cons hi

/-! ### `unescape`'s check and results -/

theorem unescRes_of_check [GooseExts] [GoGlobalContext] {s : List w8} {mode : w8} {e : UnescErr} (h : unescCheck mode s = some e) :
    unescRes s mode = ([], unescErrV e) := by
  simp [unescRes, unescapeF, h]

theorem unescCheck_pct_short (mode : w8) (rest : List w8) (h : rest.length < 2) :
    unescCheck mode (W8 37 :: rest) = some (.escape (W8 37 :: rest)) := by
  match rest, h with
  | [], _ => simp [unescCheck]
  | [_], _ => simp [unescCheck]

theorem take_succ_of (s : List w8) (k : Nat) (x : w8) (hx : s[k]? = some x) :
    s.take (k + 1) = s.take k ++ [x] := by
  rw [List.take_add_one, hx]; rfl

theorem getElem?_of_drop {s : List w8} {j : Nat} {l : List w8} (h : s.drop j = l) (k : Nat) :
    s[j + k]? = l[k]? := by
  rw [← h, List.getElem?_drop]

theorem unescCheck_pct_none {mode : w8} {rest : List w8} (h : unescCheck mode (W8 37 :: rest) = none) :
    ∃ a b r, rest = a :: b :: r ∧ unescCheck mode r = none := by
  match rest, h with
  | [], h => simp [unescCheck] at h
  | [_], h => simp [unescCheck] at h
  | a :: b :: r, h =>
    refine ⟨a, b, r, rfl, ?_⟩
    simp only [unescCheck, beq_self_eq_true, ↓reduceIte] at h
    revert h
    repeat' split
    all_goals first | exact id | (intro h; cases h)

theorem unescCheck_cons_none {mode c : w8} {rest : List w8} (hc : c ≠ W8 37)
    (h : unescCheck mode (c :: rest) = none) : unescCheck mode rest = none := by
  have hc' : (c == W8 37) = false := by simpa using hc
  unfold unescCheck at h
  simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
  revert h
  repeat' split
  all_goals first | exact id | (intro h; cases h)

theorem unescCheck_plus (mode : w8) (rest : List w8) :
    unescCheck mode (W8 43 :: rest) = unescCheck mode rest := by
  conv => lhs; unfold unescCheck
  simp

/-- The default case's error condition on a byte `c`: an ASCII byte a host or zone may not hold. -/
abbrev hostByteErr (mode c : w8) : Prop :=
  (mode = mHost ∨ mode = mZone) ∧ c.toNat < 128 ∧ shouldEscapeRef c mode = true

theorem unescCheck_other (mode c : w8) (rest : List w8) (h37 : c ≠ W8 37) (h43 : c ≠ W8 43) :
    unescCheck mode (c :: rest) =
      if hostByteErr mode c then some (.host [c]) else unescCheck mode rest := by
  have h37' : (c == W8 37) = false := by simpa using h37
  have h43' : (c == W8 43) = false := by simpa using h43
  conv => lhs; unfold unescCheck
  simp only [h37', h43', Bool.false_eq_true, ↓reduceIte]
  unfold hostByteErr
  by_cases h : (mode = mHost ∨ mode = mZone) ∧ c.toNat < 128 ∧ shouldEscapeRef c mode = true
  · rw [ite_eq_left h, ite_eq_left ?_]
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · rw [ite_eq_right h, ite_eq_right ?_]
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq]
    exact fun h' => h ⟨h'.1.1, h'.1.2, h'.2⟩

theorem unescDecode_plus (mode : w8) (rest : List w8) :
    unescDecode mode (W8 43 :: rest) =
      (if mode == mQueryComponent then W8 32 else W8 43) :: unescDecode mode rest := by
  conv => lhs; unfold unescDecode
  simp

theorem unescDecode_other (mode c : w8) (rest : List w8) (h37 : c ≠ W8 37) (h43 : c ≠ W8 43) :
    unescDecode mode (c :: rest) = c :: unescDecode mode rest := by
  have h37' : ¬c = 37#8 := h37
  have h43' : ¬c = 43#8 := h43
  conv => lhs; unfold unescDecode
  simp [h37', h43']

/-- The host check's error condition on `%ab`: a byte below 8 escaped, other than `%25`. -/
def hostErr (mode a b : w8) : Prop := mode = mHost ∧ (unhexF a).toNat < 8 ∧ ¬(a = W8 50 ∧ b = W8 53)

/-- The zone check's: an escaped byte the host component could not hold, other than `%25` and ` `. -/
def zoneErr (mode a b : w8) : Prop :=
  mode = mZone ∧ ¬(a = W8 50 ∧ b = W8 53) ∧ (unhexF a <<< W64 4 ||| unhexF b) ≠ W8 32 ∧
    shouldEscapeRef (unhexF a <<< W64 4 ||| unhexF b) mHost = true

theorem unescCheck_pct_err (mode a b : w8) (rest : List w8) (hA : ishexRef a = true)
    (hB : ishexRef b = true) (h : hostErr mode a b ∨ (¬hostErr mode a b ∧ zoneErr mode a b)) :
    unescCheck mode (W8 37 :: a :: b :: rest) = some (.escape [W8 37, a, b]) := by
  unfold hostErr zoneErr at h
  simp only [unescCheck, beq_self_eq_true, ↓reduceIte, hA, hB, Bool.and_self, Bool.not_true,
    Bool.false_eq_true]
  rcases h with ⟨h1, h2, h3⟩ | ⟨hn, h1, h2, h3, h4⟩
  · refine ite_eq_left ?_
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Nat.blt_eq]
    exact ⟨⟨h1, h2⟩, by simpa using h3⟩
  · rw [ite_eq_right ?_]
    · refine ite_eq_left ?_
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, ne_eq]
      exact ⟨⟨⟨h1, by simpa using h2⟩, h3⟩, h4⟩
    · intro h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Nat.blt_eq] at h
      exact hn ⟨h.1.1, h.1.2, by simpa using h.2⟩

theorem unescCheck_pct_ok (mode a b : w8) (rest : List w8) (hA : ishexRef a = true)
    (hB : ishexRef b = true) (hh : ¬hostErr mode a b) (hz : ¬zoneErr mode a b) :
    unescCheck mode (W8 37 :: a :: b :: rest) = unescCheck mode rest := by
  unfold hostErr at hh
  unfold zoneErr at hz
  simp only [unescCheck, beq_self_eq_true, ↓reduceIte, hA, hB, Bool.and_self, Bool.not_true,
    Bool.false_eq_true]
  rw [ite_eq_right ?_, ite_eq_right ?_]
  · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, ne_eq]
    rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact hz ⟨h1, by simpa using h2, h3, h4⟩
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Nat.blt_eq] at h
    exact hh ⟨h.1.1, h.1.2, by simpa using h.2⟩

theorem unescDecode_pct (mode a b : w8) (rest : List w8) :
    unescDecode mode (W8 37 :: a :: b :: rest) =
      (unhexF a <<< W64 4 ||| unhexF b) :: unescDecode mode rest := by
  simp [unescDecode]

set_option hygiene false in
/-- The end of a byte other than `%` and `+` the check accepts (`hck`): `i++`, and the loop goes on. -/
local macro "other_continue" : tactic => `(tactic| (
  try wp_auto
  wp_for_post
  iframe
  iexists i + W64 1, n, hp, D ++ [x]
  iframe
  ipureintro
  have hn1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
  refine ⟨by word, by word, Hi.2.2.1, by word, ?_, ?_, Hi.2.2.2.2.2.2.1, ?_⟩
  · rw [Hi.2.2.2.2.1, hdrop, hn1, hck]
  · rw [Hi.2.2.2.2.2.1, hdrop, hn1, unescDecode_other _ _ _ h37 h43, List.append_assoc]; rfl
  · intro h0 hp0
    rw [Hi.2.2.2.2.2.2.2 h0 hp0, hn1, take_succ_of s _ _ hx]))

set_option hygiene false in
/-- A byte other than `%` and `+` in a host or zone (`hHZ`), from its `s[i] < 0x80` check on. -/
local macro "hostbyte_case" : tactic => `(tactic| (
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx]
  wp_auto
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx]
    wp_auto
    wp_apply wp_shouldEscape
    rw [encTable_mode x mode hmode]
    cases hse : shouldEscapeRef x mode
    · have hne : ¬hostByteErr mode x := fun h => by
        have h2 := h.2.2; rw [hse] at h2; exact Bool.false_ne_true h2
      rw [ite_eq_right hne] at hck
      other_continue
    · have he : hostByteErr mode x := ⟨hHZ, by word, hse⟩
      rw [ite_eq_left he] at hck
      have hc : unescCheck mode s = some (.host [x]) := by rw [Hi.2.2.2.2.1, hdrop, hck]
      wp_auto
      simp only [show (0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (i + W64 1) ∧
          sint.Z (i + W64 1) ≤ (s.length : Int)) from ⟨Hi.1, by word, by word⟩, _root_.and_self,
        ↓reduceIte,
        show List.take (sint.nat (i + W64 1) - sint.nat i) (List.drop (sint.nat i) s) = [x] by
          rw [hdrop, show sint.nat (i + W64 1) - sint.nat i = 1 by word]; rfl]
      wp_auto
      wp_for_post
      rw [unescRes_of_check hc]; simp only [unescErrV]
      iapply HΦ; itrivial
  · have hne : ¬hostByteErr mode x := fun h => Hif (by have := h.2.1; word)
    rw [ite_eq_right hne] at hck
    other_continue))

set_option hygiene false in
/-- `unescape`'s return of `EscapeError(s[i:][:3])` for a `%` not followed by two hex digits, once
`hc` says the check finds that error. -/
local macro "badhex_tail" : tactic => `(tactic| (
  wp_apply wp_string_len as %_
  simp only [hsl, and_self, ↓reduceIte, htk]
  wp_auto
  wp_apply wp_string_len as %_
  wp_if_destruct
  · simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 3) ∧
        sint.Z (W64 3) ≤ ((List.drop (sint.nat i) s).length : Int)) from
        ⟨by word, by word, by simp only [List.length_drop] at Hif ⊢; word⟩, ↓reduceIte]
    rw [show List.take (3 - 0) (List.drop 0 (List.drop (sint.nat i) s)) = [W8 37, a, b] by
      rw [hd2]; rfl]
    wp_auto
    wp_for_post
    rw [unescRes_of_check hc]; simp only [unescErrV]
    iapply HΦ; itrivial
  · have h0 : List.drop (sint.nat i + 3) s = [] := by
      simp only [List.drop_eq_nil_iff]; simp only [List.length_drop] at Hif; word
    rw [show List.drop (sint.nat i) s = [W8 37, a, b] by rw [hd2, h0]]
    wp_for_post
    rw [unescRes_of_check hc]; simp only [unescErrV]
    iapply HΦ; itrivial))

set_option hygiene false in
/-- The end of a `%ab` the check accepts (`hnh`, `hnz`): `i += 3`, and the loop goes on. -/
local macro "pct_continue" : tactic => `(tactic| (
  try wp_auto
  wp_for_post
  iframe
  iexists i + W64 3, n + W64 1, hp, D ++ [unhexF a <<< W64 4 ||| unhexF b]
  iframe
  ipureintro
  have hn3 : sint.nat (i + W64 3) = sint.nat i + 3 := by word
  refine ⟨by word, by word, by word, by word, ?_, ?_, Hi.2.2.2.2.2.2.1, fun h0 => absurd h0 (by word)⟩
  · rw [Hi.2.2.2.2.1, hd2, hn3]; exact unescCheck_pct_ok _ a b _ hA hB hnh hnz
  · rw [Hi.2.2.2.2.2.1, hd2, hn3, unescDecode_pct, List.append_assoc]; rfl))

set_option hygiene false in
/-- `unescape`'s return of `EscapeError(s[i:i+3])`, once `hc` says the check finds that error. -/
local macro "pct_err" : tactic => `(tactic| (
  try wp_auto
  simp only [hs3c, and_self, ↓reduceIte, hs3]
  wp_auto
  wp_for_post
  rw [unescRes_of_check hc]; simp only [unescErrV]
  iapply HΦ; itrivial))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : net.url.Assumptions]
variable [package_sem_strings : _root_.Perennial.strings.Assumptions]

set_option maxHeartbeats 1000000 in
theorem unescape.wp_proof (wp_ishex : ishex.spec (GF := GF) (hG := hG))
    (wp_unhex : unhex.spec (GF := GF) (hG := hG))
    (wp_shouldEscape : shouldEscape.spec (GF := GF) (hG := hG))
    (wp_Grow : _root_.Perennial.strings.Builder.Grow.spec (GF := GF) (hG := hG))
    (wp_WriteByte : _root_.Perennial.strings.Builder.WriteByte.spec (GF := GF) (hG := hG))
    (wp_String : _root_.Perennial.strings.Builder.String.spec (GF := GF) (hG := hG)) :
    unescape.spec (GF := GF) (hG := hG) := by
  intro s mode hmode
  wp_start as #Hpkg
  wp_auto
  ihave HI : (∃ (i n : w64) (hp : Bool) (D : List w8), "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ n ∗
      "hasPlus" ∷ hasPlus_ptr ↦ hp ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ s.length ∧ 0 ≤ sint.Z n ∧ 3 * sint.nat n ≤ sint.nat i ∧
        unescCheck mode s = unescCheck mode (s.drop (sint.nat i)) ∧
        unescDecode mode s = D ++ unescDecode mode (s.drop (sint.nat i)) ∧
        (hp = true → mode = mQueryComponent) ∧
        (sint.Z n = 0 → hp = false → D = s.take (sint.nat i))⌝ : IProp GF) $$ [i n hasPlus]
  · iexists W64 0, W64 0, false, []
    iframe
    ipureintro
    refine ⟨by word, by word, by word, by word, rfl, rfl, by simp, fun _ _ => by simp⟩
  wp_for HI
  wp_apply wp_string_len_maxAddr as %HlM
  have Hl : s.length < 2 ^ 63 := by unfold maxAddr at HlM; omega
  have hlen : s.length + 1 < 2 ^ 63 := by unfold maxAddr at HlM; omega
  by_cases hlt : sint.Z i < sint.Z (W64 (s.length : Int))
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    have hi : sint.nat i < s.length := by word
    obtain ⟨x, hx⟩ : ∃ x, s[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    have hdrop := drop_cons_of s _ x hx
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hx]
    wp_auto
    by_cases h37 : x = W8 37
    · subst h37
      wp_auto
      wp_apply wp_string_len as %_
      have hsl : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (W64 (s.length : Int)) ∧
          sint.Z (W64 (s.length : Int)) ≤ (s.length : Int) := by
        exact ⟨Hi.1, by word, by word⟩
      have htk : List.take (sint.nat (W64 (s.length : Int)) - sint.nat i) (List.drop (sint.nat i) s) =
          s.drop (sint.nat i) := by
        rw [List.take_of_length_le]; simp only [List.length_drop]; word
      by_cases h2 : sint.nat i + 2 < s.length
      · obtain ⟨a, ha⟩ : ∃ a, s[sint.nat i + 1]? = some a :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨b, hb⟩ : ∃ b, s[sint.nat i + 2]? = some b :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hd2 : s.drop (sint.nat i) = W8 37 :: a :: b :: s.drop (sint.nat i + 3) := by
          rw [hdrop, drop_cons_of s _ a ha, drop_cons_of s _ b hb]
        have hz1 : 0 ≤ sint.Z (i + W64 1) := by word
        have hn1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        have hz2 : 0 ≤ sint.Z (i + W64 2) := by word
        have hn2 : sint.nat (i + W64 2) = sint.nat i + 2 := by word
        wp_if_destruct
        · exfalso; word
        rw [ite_eq_left_of_eq_true _ _ (eq_true hz1), hn1, ha]
        wp_auto
        wp_apply wp_ishex
        cases hA : ishexRef a
        · have hc : unescCheck mode s = some (.escape [W8 37, a, b]) := by
            rw [Hi.2.2.2.2.1, hd2]; simp [unescCheck, hA]
          wp_auto
          badhex_tail
        · wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true hz2), hn2, hb]
          wp_auto
          wp_apply wp_ishex
          cases hB : ishexRef b
          · have hc : unescCheck mode s = some (.escape [W8 37, a, b]) := by
              rw [Hi.2.2.2.2.1, hd2]; simp [unescCheck, hA, hB]
            wp_auto
            badhex_tail
          · wp_auto
            have hs3c : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (i + W64 3) ∧
                sint.Z (i + W64 3) ≤ (s.length : Int) := ⟨Hi.1, by word, by word⟩
            have hs3 : List.take (sint.nat (i + W64 3) - sint.nat i) (List.drop (sint.nat i) s) =
                [W8 37, a, b] := by
              rw [hd2, show sint.nat (i + W64 3) - sint.nat i = 3 by word]; rfl
            by_cases hH : mode = W8 4
            · subst hH
              wp_auto
              rw [ite_eq_left_of_eq_true _ _ (eq_true hz1), hn1, ha]
              wp_auto
              wp_apply wp_unhex
              wp_if_destruct
              · simp only [hs3c, and_self, ↓reduceIte, hs3]
                wp_auto
                wp_if_destruct
                · have hnh : ¬hostErr (W8 4) a b := by
                    rintro ⟨-, -, h⟩; apply h; simp at Hif; exact Hif
                  have hnz : ¬zoneErr (W8 4) a b := by rintro ⟨h, -⟩; exact absurd h (by decide)
                  pct_continue
                · have hc : unescCheck (W8 4) s = some (.escape [W8 37, a, b]) := by
                    rw [Hi.2.2.2.2.1, hd2]
                    refine unescCheck_pct_err _ a b _ hA hB (Or.inl ⟨rfl, ?_, ?_⟩)
                    · word
                    · intro h; apply Hif; rw [h.1, h.2]; rfl
                  pct_err
              · have hnh : ¬hostErr (W8 4) a b := by
                  rintro ⟨-, h, -⟩; apply Hif; word
                have hnz : ¬zoneErr (W8 4) a b := by rintro ⟨h, -⟩; exact absurd h (by decide)
                pct_continue
            · have dH : decide (mode = W8 4) = false := decide_eq_false hH
              simp only [dH]
              wp_auto
              by_cases hZ : mode = W8 8
              · subst hZ
                wp_auto
                rw [ite_eq_left_of_eq_true _ _ (eq_true hz1), hn1, ha]
                wp_auto
                wp_apply wp_unhex
                rw [ite_eq_left_of_eq_true _ _ (eq_true hz2), hn2, hb]
                wp_auto
                wp_apply wp_unhex
                simp only [hs3c, and_self, ↓reduceIte, hs3]
                wp_auto
                have hnh : ¬hostErr (W8 8) a b := fun h => absurd h.1 (by decide)
                wp_if_destruct
                · have hnz : ¬zoneErr (W8 8) a b := by
                    rintro ⟨-, h, -⟩; apply h; simp at Hif; exact Hif
                  pct_continue
                · have Hpct := Hif
                  wp_if_destruct
                  · have hnz : ¬zoneErr (W8 8) a b := by
                      rintro ⟨-, -, h, -⟩; exact h Hif
                    pct_continue
                  · wp_apply wp_shouldEscape
                    rw [encTable_mode _ mHost (by decide)]
                    cases hse : shouldEscapeRef (unhexF a <<< W64 4 ||| unhexF b) mHost
                    · have hnz : ¬zoneErr (W8 8) a b := by
                        rintro ⟨-, -, -, h⟩; rw [hse] at h; exact Bool.false_ne_true h
                      pct_continue
                    · have hc : unescCheck (W8 8) s = some (.escape [W8 37, a, b]) := by
                        rw [Hi.2.2.2.2.1, hd2]
                        refine unescCheck_pct_err _ a b _ hA hB (Or.inr ⟨hnh, rfl, ?_, Hif, hse⟩)
                        intro h; apply Hpct; rw [h.1, h.2]; rfl
                      pct_err
              · have dZ : decide (mode = W8 8) = false := decide_eq_false hZ
                simp only [dZ]
                have hnh : ¬hostErr mode a b := fun h => hH h.1
                have hnz : ¬zoneErr mode a b := fun h => hZ h.1
                pct_continue
      · wp_if_destruct
        · wp_apply wp_string_len as %_
          simp only [hsl, and_self, ↓reduceIte, htk]
          wp_auto
          wp_apply wp_string_len as %_
          wp_if_destruct
          · exfalso; simp only [List.length_drop] at Hif; word
          · wp_for_post
            have hc : unescCheck mode s = some (.escape (s.drop (sint.nat i))) := by
              rw [Hi.2.2.2.2.1, hdrop]; apply unescCheck_pct_short; simp only [List.length_drop]; word
            rw [unescRes_of_check hc]; simp only [unescErrV]
            iapply HΦ; itrivial
        · exfalso; apply Hif; word
    · have d37 : decide (x = W8 37) = false := decide_eq_false h37
      simp only [d37]
      wp_auto
      by_cases h43 : x = W8 43
      · subst h43
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, n, decide (mode = W8 32),
          D ++ [if mode == mQueryComponent then W8 32 else W8 43]
        iframe
        ipureintro
        have hn1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        refine ⟨by word, by word, Hi.2.2.1, by word, ?_, ?_, ?_, ?_⟩
        · rw [Hi.2.2.2.2.1, hdrop, hn1, unescCheck_plus]
        · rw [Hi.2.2.2.2.2.1, hdrop, hn1, unescDecode_plus, List.append_assoc]; rfl
        · intro h; simpa using h
        · intro h0 hq
          have hm : mode ≠ mQueryComponent := by simpa using hq
          have hp0 : hp = false := by
            cases hp
            · rfl
            · exact absurd (Hi.2.2.2.2.2.2.1 rfl) hm
          rw [Hi.2.2.2.2.2.2.2 h0 hp0, hn1, take_succ_of s _ _ hx]
          have : (mode == mQueryComponent) = false := by simpa using hm
          rw [this]; rfl
      · have d43 : decide (x = W8 43) = false := decide_eq_false h43
        simp only [d43]
        wp_auto
        have hck := unescCheck_other mode x (s.drop (sint.nat i + 1)) h37 h43
        by_cases hHZ : mode = W8 4 ∨ mode = W8 8
        · rcases hHZ' : hHZ with hm | hm
          · simp only [decide_eq_true hm]
            hostbyte_case
          · have d4 : decide (mode = W8 4) = false := by rw [hm]; decide
            simp only [d4]
            wp_auto
            simp only [decide_eq_true hm]
            hostbyte_case
        · have d4 : decide (mode = W8 4) = false := decide_eq_false (fun h => hHZ (Or.inl h))
          have d8 : decide (mode = W8 8) = false := decide_eq_false (fun h => hHZ (Or.inr h))
          simp only [d4]
          wp_auto
          simp only [d8]
          wp_auto
          have hne : ¬hostByteErr mode x := fun h => hHZ h.1
          rw [ite_eq_right hne] at hck
          other_continue
  · simp only [hlt, decide_false, false_neq_true, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
    have hi : sint.nat i = s.length := by word
    have hdec : unescDecode mode s = D := by
      rw [Hi.2.2.2.2.2.1, hi, List.drop_length]; simp [unescDecode]
    have hchk : unescCheck mode s = none := by rw [Hi.2.2.2.2.1, hi, List.drop_length]; rfl
    have hres : unescRes s mode = (D, interface.nil) := by simp [unescRes, unescapeF, hchk, hdec]
    rw [hres]
    wp_auto
    wp_join (Q := fun v => iprop(⌜v = #(decide (n = W64 0) && !hp)⌝))
      at (if: #(decide (n = W64 0)) then _ else _) with [hasPlus] as %Hv
    · wp_if_destruct
      · ipureintro; simp
      · ipureintro; simp
    subst Hv
    cases hb : (decide (n = W64 0) && !hp)
    · wp_auto
      wp_join iprop(∃ ps : w8, unescapedPlusSign_ptr ↦ ps ∗
          ⌜ps = (if mode = mQueryComponent then W8 32 else W8 43)⌝)
        with [unescapedPlusSign] as ⟨%ps, unescapedPlusSign, %Hps⟩
      · iexists _; iframe; ipureintro; rfl
      · iexists _; iframe; ipureintro; exact (ite_eq_right Hif).symm
      wp_apply wp_string_len_maxAddr as %HlM2
      ihave t := strings.ownBuilder_zero t_ptr $$ t
      wp_apply wp_Grow t_ptr [] _ $$ [$t] as Ht
      · ipureintro; unfold maxAddr at HlM2; simp only [List.length_nil, Int.natCast_zero, Int.zero_add]
        constructor <;> word
      ihave HJ : (∃ (j : w64) (T : List w8), "i" ∷ i_ptr ↦ j ∗
          "Ht" ∷ strings.ownBuilder t_ptr T ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ s.length ∧
            unescCheck mode (s.drop (sint.nat j)) = none ∧
            D = T ++ unescDecode mode (s.drop (sint.nat j))⌝ : IProp GF) $$ [i Ht]
      · iexists W64 0, []
        iframe
        ipureintro
        refine ⟨by word, by word, hchk, by rw [← hdec]; rfl⟩
      wp_for HJ
      wp_apply wp_string_len as %_
      by_cases hlt2 : sint.Z j < sint.Z (W64 (s.length : Int))
      · simp only [hlt2, _root_.decide_true, ↓reduceIte]
        have hj : sint.nat j < s.length := by word
        obtain ⟨x, hx⟩ : ∃ x, s[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
        have hdrop := drop_cons_of s _ x hx
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true Hj.1), hx]
        wp_auto
        by_cases h37 : x = W8 37
        · subst h37
          obtain ⟨a, b, r, hr, hrok⟩ := unescCheck_pct_none (hdrop ▸ Hj.2.2.1)
          have hd : s.drop (sint.nat j) = W8 37 :: a :: b :: r := by rw [hdrop, hr]
          have ha : s[sint.nat j + 1]? = some a := by rw [getElem?_of_drop hd]; rfl
          have hb : s[sint.nat j + 2]? = some b := by rw [getElem?_of_drop hd]; rfl
          have hj2 : sint.nat j + 2 < s.length := by
            have := congrArg List.length hd; simp only [List.length_drop, List.length_cons] at this
            omega
          have hz1 : 0 ≤ sint.Z (j + W64 1) := by word
          have hn1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
          have hz2 : 0 ≤ sint.Z (j + W64 2) := by word
          have hn2 : sint.nat (j + W64 2) = sint.nat j + 2 := by word
          wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true hz1), hn1, ha]
          wp_auto
          wp_apply wp_unhex
          rw [ite_eq_left_of_eq_true _ _ (eq_true hz2), hn2, hb]
          wp_auto
          wp_apply wp_unhex
          wp_apply wp_WriteByte $$ [$Ht] as Ht
          wp_for_post
          iframe
          iexists j + W64 2 + W64 1, T ++ [unhexF a <<< W64 4 ||| unhexF b]
          iframe
          ipureintro
          have hn3 : sint.nat (j + W64 2 + W64 1) = sint.nat j + 3 := by word
          have hdr : s.drop (sint.nat j + 3) = r := by
            have := congrArg (List.drop 3) hd
            simpa [List.drop_drop, Nat.add_comm] using this
          refine ⟨by word, by word, ?_, ?_⟩
          · rw [hn3, hdr]; exact hrok
          · rw [hn3, hdr, Hj.2.2.2, hd, unescDecode_pct, List.append_assoc]; rfl
        · have hrok := unescCheck_cons_none h37 (hdrop ▸ Hj.2.2.1)
          have d37 : decide (x = W8 37) = false := decide_eq_false h37
          simp only [d37]
          wp_auto
          by_cases h43 : x = W8 43
          · subst h43
            wp_auto
            wp_apply wp_WriteByte $$ [$Ht] as Ht
            wp_for_post
            iframe
            iexists j + W64 1, T ++ [ps]
            iframe
            ipureintro
            have hn1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
            refine ⟨by word, by word, ?_, ?_⟩
            · rw [hn1]; exact hrok
            · rw [hn1, Hj.2.2.2, hdrop, unescDecode_plus, List.append_assoc, Hps]
              by_cases hq : mode = mQueryComponent <;> simp [hq]
          · have d43 : decide (x = W8 43) = false := decide_eq_false h43
            simp only [d43]
            wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true Hj.1), hx]
            wp_apply wp_WriteByte $$ [$Ht] as Ht
            wp_for_post
            iframe
            iexists j + W64 1, T ++ [x]
            iframe
            ipureintro
            have hn1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
            refine ⟨by word, by word, ?_, ?_⟩
            · rw [hn1]; exact hrok
            · rw [hn1, Hj.2.2.2, hdrop, unescDecode_other _ _ _ h37 h43, List.append_assoc]; rfl
      · simp only [hlt2, decide_false, false_neq_true, _root_.decide_true, Bool.false_eq_true,
          ↓reduceIte]
        have hj : sint.nat j = s.length := by word
        have hT : D = T := by rw [Hj.2.2.2, hj, List.drop_length]; simp [unescDecode]
        subst hT
        wp_auto
        wp_apply wp_String $$ [$Ht] as Ht
        iapply HΦ; itrivial
    · wp_auto
      have hD : D = s := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hb
        rw [Hi.2.2.2.2.2.2.2 (by rw [hb.1]; rfl) hb.2, hi, List.take_length]
      subst hD
      iapply HΦ; itrivial

end proof

end net.url
end Perennial
