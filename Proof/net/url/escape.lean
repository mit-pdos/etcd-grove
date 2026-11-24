/-
The proof of `escape.spec` (`Spec/net/url/escape.lean`).
-/
module

public import Spec.net.url.escape
public import Spec.net.url.shouldEscape
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len wp_string_len_maxAddr)

namespace net.url

/-! ### `escape`'s counts -/

/-- A space in a query component (written `+`). -/
def escSp (mode c : w8) : Bool := c == W8 32 && mode == mQueryComponent

/-- The bytes `escape` writes as `%AB`: escaped, and not a query component's space. -/
def escHex (mode : w8) : List w8 → Nat
  | [] => 0
  | c :: l => (if shouldEscapeRef c mode && !escSp mode c then 1 else 0) + escHex mode l

/-- The query component's spaces. -/
def escSpaces (mode : w8) : List w8 → Nat
  | [] => 0
  | c :: l => (if shouldEscapeRef c mode && escSp mode c then 1 else 0) + escSpaces mode l

theorem shouldEscapeRef_space (m : w8) : shouldEscapeRef (W8 32) m = true := by
  unfold shouldEscapeRef inR
  simp (config := { decide := true })

theorem escHex_append (mode : w8) (l1 l2 : List w8) :
    escHex mode (l1 ++ l2) = escHex mode l1 + escHex mode l2 := by
  induction l1 with
  | nil => simp [escHex]
  | cons c l ih => simp only [List.cons_append, escHex, ih]; omega

theorem escSpaces_append (mode : w8) (l1 l2 : List w8) :
    escSpaces mode (l1 ++ l2) = escSpaces mode l1 + escSpaces mode l2 := by
  induction l1 with
  | nil => simp [escSpaces]
  | cons c l ih => simp only [List.cons_append, escSpaces, ih]; omega

theorem escapeF_append (l1 l2 : List w8) (mode : w8) :
    escapeF (l1 ++ l2) mode = escapeF l1 mode ++ escapeF l2 mode := by
  simp [escapeF, List.flatMap_append]

theorem take_succ_of (s : List w8) (k : Nat) (x : w8) (hx : s[k]? = some x) :
    s.take (k + 1) = s.take k ++ [x] := by
  rw [List.take_add_one, hx]; rfl

/-- One byte's escape. -/
theorem escapeF_one (c mode : w8) :
    escapeF [c] mode = if escSp mode c then [W8 43] else if shouldEscapeRef c mode then
      [W8 37, hexDigit (c >>> W64 4), hexDigit (c &&& W8 15)] else [c] := by
  simp [escapeF, escSp]

theorem escapeF_cons (c : w8) (l : List w8) (mode : w8) :
    escapeF (c :: l) mode = escapeF [c] mode ++ escapeF l mode := by
  rw [show c :: l = [c] ++ l from rfl, escapeF_append]

theorem escSp_esc (mode c : w8) (h : escSp mode c = true) : shouldEscapeRef c mode = true := by
  unfold escSp at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1]; exact shouldEscapeRef_space mode

theorem escapeF_length (l : List w8) (mode : w8) :
    (escapeF l mode).length = l.length + 2 * escHex mode l := by
  induction l with
  | nil => simp [escapeF, escHex]
  | cons c l ih =>
    rw [escapeF_cons, List.length_append, ih, escapeF_one]
    simp only [escHex, List.length_cons]
    cases h1 : escSp mode c
    · cases h2 : shouldEscapeRef c mode <;> simp <;> omega
    · simp [escSp_esc mode c h1]; omega

/-- Nothing escaped: `escape` returns `s`. -/
theorem escapeF_none (l : List w8) (mode : w8) (h1 : escHex mode l = 0) (h2 : escSpaces mode l = 0) :
    escapeF l mode = l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [escHex, escSpaces] at h1 h2
    rw [escapeF_cons, ih (by omega) (by omega), escapeF_one]
    cases h3 : escSp mode c
    · cases h4 : shouldEscapeRef c mode
      · simp
      · simp [h3, h4] at h1
    · simp [h3, escSp_esc mode c h3] at h2

/-- Only spaces of a query component: `escape` writes each `+`. -/
theorem escapeF_spaces (l : List w8) (mode : w8) (h1 : escHex mode l = 0) :
    escapeF l mode = l.map (fun c => if c = W8 32 then W8 43 else c) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [escHex] at h1
    rw [escapeF_cons, ih (by omega), escapeF_one, List.map_cons]
    by_cases hc : c = W8 32
    · subst hc
      cases h3 : escSp mode (W8 32)
      · rw [shouldEscapeRef_space, h3] at h1; simp at h1
      · simp
    · have h3 : escSp mode c = false := by
        cases h : escSp mode c
        · rfl
        · exfalso; unfold escSp at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact hc h.1
      cases h4 : shouldEscapeRef c mode
      · rw [ite_cond_eq_false _ _ (eq_false hc)]; simp only [h3]; rfl
      · simp [h3, h4] at h1

theorem escHex_add_le (mode : w8) (l : List w8) : escHex mode l + escSpaces mode l ≤ l.length := by
  induction l with
  | nil => simp [escHex, escSpaces]
  | cons c l ih =>
    simp only [escHex, escSpaces, List.length_cons]
    cases shouldEscapeRef c mode <;> cases escSp mode c <;> simp <;> omega

theorem drop_cons_of (s : List w8) (i : Nat) (x : w8) (hx : s[i]? = some x) :
    s.drop i = x :: s.drop (i + 1) := by
  have hi : i < s.length := by
    rcases Nat.lt_or_ge i s.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  rw [List.drop_eq_getElem_cons hi]
  congr
  rw [List.getElem?_eq_getElem hi] at hx; exact Option.some.inj hx

theorem map_take_set (f : w8 → w8) (s : List w8) (i : Nat) (x : w8) (hx : s[i]? = some x) :
    ((s.take i).map f ++ s.drop i).set i (f x) = (s.take (i + 1)).map f ++ s.drop (i + 1) := by
  have hi : i < s.length := by
    rcases Nat.lt_or_ge i s.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  have hl : ((s.take i).map f).length = i := by simp; omega
  rw [drop_cons_of s i x hx, take_succ_of s i x hx, List.map_append, List.set_append, hl]
  simp

theorem set_rep (P : List w8) (n : Nat) (v : w8) (hn : 0 < n) :
    (P ++ List.replicate n (W8 0)).set P.length v = (P ++ [v]) ++ List.replicate (n - 1) (W8 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.set_append]
  simp [List.replicate_succ]

theorem escapeF_take_drop (s : List w8) (m : Nat) (mode : w8) :
    escapeF s mode = escapeF (s.take m) mode ++ escapeF (s.drop m) mode := by
  rw [← escapeF_append, List.take_append_drop]

theorem upperhex_get (i : w8) (h : i.toNat < 16) :
    (if 0 ≤ sint.Z (W64 (uint.Z i)) then (go!"0123456789ABCDEF")[sint.nat (W64 (uint.Z i))]?
      else none) = some (hexDigit i) := by
  have h1 : 0 ≤ sint.Z (W64 (uint.Z i)) := by word
  have h2 : sint.nat (W64 (uint.Z i)) = i.toNat := by word
  rw [if_pos h1, h2]
  unfold hexDigit
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
  rfl

theorem shr4_lt (x : w8) : (x >>> W64 4).toNat < 16 := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  have h4 : (W64 4).toNat = 4 := by decide
  rw [h4]; omega

theorem and15_lt (x : w8) : (x &&& W8 15).toNat < 16 := by
  rw [BitVec.toNat_and]
  have := Nat.and_le_right (n := x.toNat) (m := (W8 15).toNat)
  have h15 : (W8 15).toNat = 15 := by decide
  omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : net.url.Assumptions]

set_option maxHeartbeats 1000000 in
theorem escape.wp_proof (wp_shouldEscape : shouldEscape.spec (GF := GF) (hG := hG)) :
    escape.spec (GF := GF) (hG := hG) := by
  intro s mode hmode
  wp_start as #Hpkg
  wp_auto
  wp_apply wp_string_to_bytes s as %rs ⟨Hrs, -⟩
  ihave %Hrl := ownSlice_len $$ Hrs
  ihave HI : (∃ (k : w64) (cv : w8), "i" ∷ i_ptr ↦ k ∗ "c" ∷ c_ptr ↦ cv ∗
      "spaceCount" ∷ spaceCount_ptr ↦ W64 (escSpaces mode (s.take (sint.nat k)) : Int) ∗
      "hexCount" ∷ hexCount_ptr ↦ W64 (escHex mode (s.take (sint.nat k)) : Int) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ s.length⌝ : IProp GF) $$ [i c spaceCount hexCount]
  · iexists W64 0, _
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.take_zero, escSpaces, escHex]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases hlt : sint.Z k < sint.Z rs.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    have hi : sint.nat k < s.length := by rw [Hrl.1]; word
    obtain ⟨x, hx⟩ : ∃ x, s[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk.1, hlt⟩)]
    wp_apply wp_load_slice_index rs (sint.Z k) s _ x Hk.1 $$ [$Hrs]
    · ipureintro; exact hx
    iintro Hrs
    wp_auto
    wp_apply wp_shouldEscape
    rw [encTable_mode x mode hmode]
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    have htk := take_succ_of s _ x hx
    have hcnt : escHex mode (s.take (sint.nat k)) + escSpaces mode (s.take (sint.nat k)) ≤ sint.nat k := by
      have := escHex_add_le mode (s.take (sint.nat k))
      rw [List.length_take] at this; omega
    have hsp1 : escSpaces mode (s.take (sint.nat (k + W64 1))) = escSpaces mode (s.take (sint.nat k)) +
        (if shouldEscapeRef x mode && escSp mode x then 1 else 0) := by
      rw [hk1, htk, escSpaces_append]; simp [escSpaces]
    have hhx1 : escHex mode (s.take (sint.nat (k + W64 1))) = escHex mode (s.take (sint.nat k)) +
        (if shouldEscapeRef x mode && !escSp mode x then 1 else 0) := by
      rw [hk1, htk, escHex_append]; simp [escHex]
    cases hse : shouldEscapeRef x mode
    · wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      simp only [hse, Bool.false_and, ↓reduceIte, Nat.add_zero, Bool.false_eq_true] at hsp1 hhx1
      rw [hsp1, hhx1]
      iframe
      ipureintro; constructor <;> word
    · wp_auto
      by_cases hsp : escSp mode x = true
      · have hx32 : x = W8 32 ∧ mode = mQueryComponent := by
          simpa [escSp] using hsp
        obtain ⟨rfl, hm⟩ := hx32
        subst hm
        wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        simp only [hse, hsp, Bool.true_and, Bool.not_true, Bool.and_false, ↓reduceIte,
          Bool.false_eq_true, Nat.add_zero] at hsp1 hhx1
        rw [hsp1, hhx1, show (W64 ((escSpaces mQueryComponent (s.take (sint.nat k)) : Nat) : Int) + W64 1) =
          W64 ((escSpaces mQueryComponent (s.take (sint.nat k)) + 1 : Nat) : Int) by word]
        iframe
        ipureintro; constructor <;> word
      · simp only [hse, hsp, Bool.true_and, Bool.not_false, ↓reduceIte, Bool.false_eq_true,
          Nat.add_zero] at hsp1 hhx1
        by_cases hx32 : x = W8 32
        · subst hx32
          have hm : mode ≠ mQueryComponent := by
            intro h; subst h; exact hsp (by simp [escSp])
          rw [decide_eq_true (rfl : W8 32 = W8 32)]
          wp_auto
          (try rw [decide_eq_false hm])
          wp_auto
          wp_for_post
          iframe
          iexists _, _
          iframe
          rw [hsp1, hhx1, show (W64 ((escHex mode (s.take (sint.nat k)) : Nat) : Int) + W64 1) =
            W64 ((escHex mode (s.take (sint.nat k)) + 1 : Nat) : Int) by word]
          iframe
          ipureintro; constructor <;> word
        · rw [decide_eq_false hx32]
          wp_auto
          wp_for_post
          iframe
          iexists _, _
          iframe
          rw [hsp1, hhx1, show (W64 ((escHex mode (s.take (sint.nat k)) : Nat) : Int) + W64 1) =
            W64 ((escHex mode (s.take (sint.nat k)) + 1 : Nat) : Int) by word]
          iframe
          ipureintro; constructor <;> word
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hkl : sint.nat k = s.length := by rw [Hrl.1]; word
    rw [hkl, List.take_length]
    wp_auto
    have hsb := escHex_add_le mode s
    by_cases hz : escSpaces mode s = 0 ∧ escHex mode s = 0
    · obtain ⟨h1, h2⟩ := hz
      rw [show decide (W64 ((escSpaces mode s : Nat) : Int) = W64 0) = true by rw [h1]; decide]
      wp_auto
      rw [decide_eq_true (show W64 ((escHex mode s : Nat) : Int) = W64 0 by rw [h2]; rfl)]
      wp_auto
      rw [escapeF_none s mode h2 h1]
      iapply HΦ; itrivial
    have hab : escSpaces mode s ≠ 0 ∨ (escSpaces mode s = 0 ∧ escHex mode s ≠ 0) := by omega
    rcases hab with ha | ⟨ha, hb⟩
    case' inl =>
      rw [decide_eq_false (show W64 ((escSpaces mode s : Nat) : Int) ≠ W64 0 by
        intro h; apply ha; have := congrArg (fun w : w64 => sint.Z w) h; simp at this; word)]
      wp_auto
    case' inr =>
      rw [show decide (W64 ((escSpaces mode s : Nat) : Int) = W64 0) = true by rw [ha]; decide]
      wp_auto
      rw [decide_eq_false (show W64 ((escHex mode s : Nat) : Int) ≠ W64 0 by
        intro h; apply hb; have := congrArg (fun w : w64 => sint.Z w) h; simp at this; word)]
      wp_auto
    all_goals (
    wp_apply wp_string_len_maxAddr as %HlM
    have Hl : s.length < 2 ^ 63 := by unfold maxAddr at HlM; omega
    have hlen : 3 * s.length < 2 ^ 63 := by unfold maxAddr at HlM; omega
    have hreq : W64 (s.length : Int) + W64 2 * W64 ((escHex mode s : Nat) : Int) =
        W64 ((s.length + 2 * escHex mode s : Nat) : Int) := by word
    rw [hreq]
    have hR : s.length + 2 * escHex mode s < 2 ^ 63 := by omega
    have hRz : sint.Z (W64 ((s.length + 2 * escHex mode s : Nat) : Int)) =
        ((s.length + 2 * escHex mode s : Nat) : Int) := by word
    wp_join iprop(∃ tsl : GoSlice, t_ptr ↦ tsl ∗
        tsl ↦* List.replicate (s.length + 2 * escHex mode s) (W8 0) ∗
        required_ptr ↦ W64 ((s.length + 2 * escHex mode s : Nat) : Int))
      with [buf t required] as ⟨%tsl, t, Ht, required⟩
    · have hc : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 ((s.length + 2 * escHex mode s : Nat) : Int)) ∧
          sint.Z (W64 ((s.length + 2 * escHex mode s : Nat) : Int)) ≤ 64 := by
        have h0 : sint.Z (W64 0) = 0 := by decide
        have h64 : sint.Z (W64 64) = 64 := by decide
        rw [h0, hRz]; rw [hRz, h64] at Hif; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      have hz64 : (zero_val (GoArray w8 64)).arr = List.replicate 64 (W8 0) := by rfl
      ihave Hsl := slice_array (V := w8) buf_ptr 64 _ (by rw [hz64]; simp) $$ buf
      have hk : 0 ≤ sint.Z (W64 ((s.length + 2 * escHex mode s : Nat) : Int)) ∧
          sint.Z (W64 ((s.length + 2 * escHex mode s : Nat) : Int)) ≤ sint.Z (W64 64) := by
        have h64 : sint.Z (W64 64) = 64 := by decide
        rw [h64]; omega
      icases (ownSlice_split_all (W64 ((s.length + 2 * escHex mode s : Nat) : Int))
        (slice.mk buf_ptr (W64 64) (W64 64)) _ _ hk).1 $$ Hsl with ⟨Hsl, -⟩
      unfold slice.slice sliceIndexRef
      wp_auto
      have htk : List.take (sint.nat (W64 ((s.length + 2 * escHex mode s : Nat) : Int)))
          (zero_val (GoArray w8 64)).arr = List.replicate (s.length + 2 * escHex mode s) (W8 0) := by
        rw [hz64, List.take_replicate]
        congr 1
        have : sint.nat (W64 ((s.length + 2 * escHex mode s : Nat) : Int)) = s.length + 2 * escHex mode s := by
          word
        rw [this]; rw [hRz, show sint.Z (W64 64) = 64 by decide] at hk; omega
      rw [htk]
      dsimp only
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
    · wp_apply (wp_slice_make2 (V := w8) (W64 ((s.length + 2 * escHex mode s : Nat) : Int)))
        as %sl ⟨Hsl, -⟩
      · ipureintro; rw [hRz]; omega
      have : sint.nat (W64 ((s.length + 2 * escHex mode s : Nat) : Int)) = s.length + 2 * escHex mode s := by
        word
      rw [this, show (zero_val w8) = W8 0 from rfl]
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
    by_cases hh : escHex mode s = 0
    · rw [show decide (W64 ((escHex mode s : Nat) : Int) = W64 0) = true by rw [hh]; decide]
      rw [hh]
      simp only [Nat.mul_zero, Nat.add_zero]
      wp_auto
      wp_apply wp_string_to_bytes s as %rs2 ⟨Hrs2, -⟩
      wp_apply wp_slice_copy tsl _ rs2 _ _ $$ [$Ht $Hrs2] as %n ⟨-, Ht, -⟩
      simp only [List.length_replicate, List.take_length, List.drop_replicate, Nat.sub_self,
        List.replicate_zero, List.append_nil]
      ihave HJ : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
          "Ht" ∷ tsl ↦* ((s.take (sint.nat i)).map (fun c => if c = W8 32 then W8 43 else c) ++
            s.drop (sint.nat i)) ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ s.length⌝ : IProp GF) $$ [i Ht]
      · iexists W64 0
        rw [show sint.nat (W64 0) = 0 from rfl]
        simp only [List.take_zero, List.map_nil, List.nil_append, List.drop_zero]
        iframe
        ipureintro; exact ⟨by decide, Nat.zero_le _⟩
      wp_for HJ
      wp_apply wp_string_len as %Hl2
      by_cases hlt2 : sint.Z i < sint.Z (W64 (s.length : Int))
      · simp only [hlt2, _root_.decide_true, ↓reduceIte]
        have hi2 : sint.nat i < s.length := by word
        obtain ⟨y, hy⟩ : ∃ y, s[sint.nat i]? = some y := ⟨_, List.getElem?_eq_getElem hi2⟩
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true Hi.1), hy]
        wp_auto
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        have hlen2 : ((s.take (sint.nat i)).map (fun c => if c = W8 32 then W8 43 else c) ++
            s.drop (sint.nat i)).length = s.length := by simp; omega
        ihave %HtL := ownSlice_len $$ Ht
        by_cases hy32 : y = W8 32
        · subst hy32
          wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by rw [hlen2] at HtL; word⟩)]
          wp_apply wp_store_slice_index tsl (sint.Z i) _ (W8 43) $$ [Ht] as Ht
          · iframe; ipureintro; constructor; exact Hi.1; rw [hlen2]; word
          have hset := map_take_set (fun c => if c = W8 32 then W8 43 else c) s (sint.nat i) (W8 32) hy
          simp only [↓reduceIte] at hset
          rw [show (sint.Z i).toNat = sint.nat i from rfl, hset]
          wp_for_post
          iframe
          iexists _
          rw [hi1]
          iframe
          ipureintro; constructor <;> word
        · rw [decide_eq_false hy32]
          wp_auto
          wp_for_post
          iframe
          iexists _
          have hset := map_take_set (fun c => if c = W8 32 then W8 43 else c) s (sint.nat i) y hy
          simp only [hy32, ↓reduceIte] at hset
          rw [hi1, ← hset, list_set_lookup_self]
          · iframe
            ipureintro; constructor <;> word
          · rw [List.getElem?_append_right (by simp; omega)]
            simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi2), Nat.sub_self]
            rw [drop_cons_of s _ y hy]; rfl
      · simp only [hlt2, decide_false, false_neq_true, _root_.decide_true, Bool.false_eq_true,
          ↓reduceIte]
        have hil : sint.nat i = s.length := by word
        rw [hil, List.take_length, List.drop_length, List.append_nil]
        wp_auto
        wp_apply wp_bytes_to_string _ _ _ $$ Ht as Ht
        rw [escapeF_spaces s mode hh]
        iapply HΦ; itrivial
    · rw [decide_eq_false (show W64 ((escHex mode s : Nat) : Int) ≠ W64 0 by
        intro h; apply hh; have := congrArg (fun w : w64 => sint.Z w) h; simp at this; word)]
      wp_auto
      wp_apply wp_string_to_bytes s as %rs3 ⟨Hrs3, -⟩
      ihave %Hrl3 := ownSlice_len $$ Hrs3
      ihave HK : (∃ (k : w64) (cv : w8), "i" ∷ i_ptr ↦ k ∗ "c" ∷ c_ptr ↦ cv ∗
          "j" ∷ j_ptr ↦ W64 ((escapeF (s.take (sint.nat k)) mode).length : Int) ∗
          "Ht" ∷ tsl ↦* (escapeF (s.take (sint.nat k)) mode ++ List.replicate
            (s.length + 2 * escHex mode s - (escapeF (s.take (sint.nat k)) mode).length) (W8 0)) ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ s.length⌝ : IProp GF) $$ [i c j Ht]
      · iexists W64 0, _
        rw [show sint.nat (W64 0) = 0 from rfl]
        simp only [List.take_zero]
        rw [show escapeF [] mode = [] from rfl]
        simp only [List.length_nil, Nat.sub_zero, List.nil_append]
        iframe
        ipureintro; exact ⟨by decide, Nat.zero_le _⟩
      wp_for HK
      by_cases hlt3 : sint.Z k < sint.Z rs3.len
      · simp only [hlt3, _root_.decide_true, ↓reduceIte]
        have hi3 : sint.nat k < s.length := by rw [Hrl3.1]; word
        obtain ⟨x, hx⟩ : ∃ x, s[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem hi3⟩
        wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk.1, hlt3⟩)]
        wp_apply wp_load_slice_index rs3 (sint.Z k) s _ x Hk.1 $$ [$Hrs3]
        · ipureintro; exact hx
        iintro Hrs3
        wp_auto
        ihave %HtL := ownSlice_len $$ Ht
        have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        have htk := take_succ_of s _ x hx
        have hER := escapeF_take_drop s (sint.nat k + 1) mode
        rw [htk, escapeF_append] at hER
        have hRl : (escapeF s mode).length = s.length + 2 * escHex mode s := escapeF_length s mode
        rw [hER, List.length_append, List.length_append] at hRl
        have hEt : escapeF (s.take (sint.nat (k + W64 1))) mode =
            escapeF (s.take (sint.nat k)) mode ++ escapeF [x] mode := by
          rw [hk1, htk, escapeF_append]
        generalize escapeF (List.take (sint.nat k) s) mode = E at HtL hRl hEt ⊢
        have hEz : sint.Z (W64 (E.length : Int)) = (E.length : Int) := by word
        have hTl : sint.nat tsl.len = s.length + 2 * escHex mode s := by
          rw [← HtL.1]; simp; omega
        by_cases hsp : escSp mode x = true
        · have hx32 : x = W8 32 ∧ mode = mQueryComponent := by
            simpa [escSp] using hsp
          obtain ⟨rfl, hm⟩ := hx32
          subst hm
          rw [decide_eq_true (rfl : W8 32 = W8 32)]
          wp_auto
          have h1 : (escapeF [W8 32] mQueryComponent) = [W8 43] := by rw [escapeF_one, if_pos hsp]
          rw [h1] at hRl hEt
          simp only [List.length_cons, List.length_nil] at hRl
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hEz]; omega, by rw [hEz]; word⟩)]
          wp_apply wp_store_slice_index tsl _ _ (W8 43) $$ [Ht] as Ht
          · iframe; ipureintro; constructor
            · rw [hEz]; omega
            · rw [hEz]; simp only [List.length_append, List.length_replicate]; omega
          rw [show (sint.Z (W64 (E.length : Int))).toNat = E.length by rw [hEz]; omega,
            set_rep E (List.length s + 2 * escHex mQueryComponent s - E.length) (W8 43) (by omega)]
          wp_for_post
          iframe
          iexists _, _
          iframe
          rw [hEt, show W64 (E.length : Int) + W64 1 = W64 ((E ++ [W8 43]).length : Int) by simp; word,
            show List.length s + 2 * escHex mQueryComponent s - E.length - 1 =
              List.length s + 2 * escHex mQueryComponent s - (E ++ [W8 43]).length by simp; omega]
          iframe
          ipureintro; constructor <;> word
        · have hsp' : escSp mode x = false := by simpa using hsp
          by_cases hx32 : x = W8 32
          case' pos =>
            have hm : mode ≠ mQueryComponent := by
              intro h; apply hsp; simp [escSp, hx32, h]
            rw [decide_eq_true hx32]
            wp_auto
            (try rw [decide_eq_false hm])
            wp_auto
          case' neg =>
            rw [decide_eq_false hx32]
            wp_auto
          all_goals (
          wp_apply wp_shouldEscape
          rw [encTable_mode x mode hmode]
          cases hse : shouldEscapeRef x mode
          · rw [show decide (true = false) = false from rfl]
            wp_auto
            have h1 : escapeF [x] mode = [x] := by rw [escapeF_one]; simp [hsp', hse]
            rw [h1] at hRl hEt
            simp only [List.length_cons, List.length_nil] at hRl
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hEz]; omega, by rw [hEz]; word⟩)]
            wp_apply wp_store_slice_index tsl _ _ x $$ [Ht] as Ht
            · iframe; ipureintro; constructor
              · rw [hEz]; omega
              · rw [hEz]; simp only [List.length_append, List.length_replicate]; omega
            rw [show (sint.Z (W64 (E.length : Int))).toNat = E.length by rw [hEz]; omega,
              set_rep E (List.length s + 2 * escHex mode s - E.length) x (by omega)]
            wp_for_post
            iframe
            iexists _, _
            iframe
            rw [hEt, show W64 (E.length : Int) + W64 1 = W64 ((E ++ [x]).length : Int) by simp; word,
              show List.length s + 2 * escHex mode s - E.length - 1 =
                List.length s + 2 * escHex mode s - (E ++ [x]).length by simp; omega]
            iframe
            ipureintro; constructor <;> word
          · rw [show decide (true = true) = true from rfl]
            wp_auto
            have h1 : escapeF [x] mode = [W8 37, hexDigit (x >>> W64 4), hexDigit (x &&& W8 15)] := by
              rw [escapeF_one]; simp [hsp', hse]
            rw [h1] at hRl hEt
            simp only [List.length_cons, List.length_nil] at hRl
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hEz]; omega, by rw [hEz]; word⟩)]
            wp_apply wp_store_slice_index tsl _ _ (W8 37) $$ [Ht] as Ht
            · iframe; ipureintro; constructor
              · rw [hEz]; omega
              · rw [hEz]; simp only [List.length_append, List.length_replicate]; omega
            rw [show (sint.Z (W64 (E.length : Int))).toNat = E.length by rw [hEz]; omega,
              set_rep E (List.length s + 2 * escHex mode s - E.length) (W8 37) (by omega)]
            rw [upperhex_get _ (shr4_lt x)]
            wp_auto
            have hTz : sint.Z tsl.len = ((List.length s + 2 * escHex mode s : Nat) : Int) := by
              have := HtL.2
              rw [show sint.nat tsl.len = (sint.Z tsl.len).toNat from rfl] at hTl; omega
            have hE1 : W64 (E.length : Int) + W64 1 = W64 ((E ++ [W8 37]).length : Int) := by
              rw [List.length_append, List.length_singleton]; word
            have hE1z : sint.Z (W64 ((E ++ [W8 37]).length : Int)) = ((E ++ [W8 37]).length : Int) := by
              rw [List.length_append, List.length_singleton]; word
            rw [hE1, ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hE1z]; omega,
              by rw [hE1z, hTz]; simp only [List.length_append, List.length_singleton]; omega⟩)]
            wp_apply wp_store_slice_index tsl _ _ (hexDigit (x >>> W64 4)) $$ [Ht] as Ht
            · iframe; ipureintro; constructor
              · rw [hE1z]; omega
              · rw [hE1z]; simp only [List.length_append, List.length_replicate, List.length_cons,
                  List.length_nil]; omega
            rw [show (sint.Z (W64 ((E ++ [W8 37]).length : Int))).toNat = (E ++ [W8 37]).length by
                rw [hE1z]; omega,
              set_rep (E ++ [W8 37]) (List.length s + 2 * escHex mode s - E.length - 1)
                (hexDigit (x >>> W64 4)) (by omega)]
            rw [upperhex_get _ (and15_lt x)]
            wp_auto
            have hE2 : W64 (E.length : Int) + W64 2 =
                W64 ((E ++ [W8 37] ++ [hexDigit (x >>> W64 4)]).length : Int) := by
              simp only [List.length_append, List.length_singleton]; word
            have hE2z : sint.Z (W64 ((E ++ [W8 37] ++ [hexDigit (x >>> W64 4)]).length : Int)) =
                ((E ++ [W8 37] ++ [hexDigit (x >>> W64 4)]).length : Int) := by
              simp only [List.length_append, List.length_singleton]; word
            rw [hE2, ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hE2z]; omega,
              by rw [hE2z, hTz]; simp only [List.length_append, List.length_singleton]; omega⟩)]
            wp_apply wp_store_slice_index tsl _ _ (hexDigit (x &&& W8 15)) $$ [Ht] as Ht
            · iframe; ipureintro; constructor
              · rw [hE2z]; omega
              · rw [hE2z]; simp only [List.length_append, List.length_replicate, List.length_cons,
                  List.length_nil]; omega
            rw [show (sint.Z (W64 ((E ++ [W8 37] ++ [hexDigit (x >>> W64 4)]).length : Int))).toNat =
                (E ++ [W8 37] ++ [hexDigit (x >>> W64 4)]).length by rw [hE2z]; omega,
              set_rep (E ++ [W8 37] ++ [hexDigit (x >>> W64 4)])
                (List.length s + 2 * escHex mode s - E.length - 1 - 1) (hexDigit (x &&& W8 15)) (by omega)]
            wp_for_post
            iframe
            iexists _, _
            iframe
            rw [hEt, show W64 (E.length : Int) + W64 3 = W64 ((E ++ [W8 37, hexDigit (x >>> W64 4),
                hexDigit (x &&& W8 15)]).length : Int) by
                  simp only [List.length_append, List.length_cons, List.length_nil]; word,
              show List.length s + 2 * escHex mode s - E.length - 1 - 1 - 1 =
                List.length s + 2 * escHex mode s - (E ++ [W8 37, hexDigit (x >>> W64 4),
                  hexDigit (x &&& W8 15)]).length by simp; omega]
            simp only [List.append_assoc, List.cons_append, List.nil_append]
            iframe
            ipureintro; constructor <;> word)
      · simp only [hlt3, decide_false, false_neq_true, _root_.decide_true, Bool.false_eq_true,
          ↓reduceIte]
        have hkl3 : sint.nat k = s.length := by rw [Hrl3.1]; word
        rw [hkl3, List.take_length, ← escapeF_length s mode, Nat.sub_self, List.replicate_zero,
          List.append_nil]
        wp_auto
        wp_apply wp_bytes_to_string _ _ _ $$ Ht as Ht
        iapply HΦ; itrivial)
end proof

end net.url
end Perennial
