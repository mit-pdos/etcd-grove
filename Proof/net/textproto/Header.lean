/-
**`net/textproto`'s header keys and `MIMEHeader.Set`/`Get`, over their code** (prove-http3,
2026-11-21; go1.27.3 `net/textproto/reader.go:662-800`, `header.go:21-39`): what `http.Header.Set`
and `Get` call (`Proof/net/http/Proved.lean`). `CanonicalMIMEHeaderKey(s)` is `http.canonKey s`,
the definition the HTTP boundary's header specs were written in since 2026-10-23.
-/
module

public import Proof.net.http.Boundary
public import Proof.net.textproto.Base
public import Perennial.Proof.sync.Link
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace textproto

open Iris Iris.BI Iris.ProofMode
open _root_.Perennial.net.textproto

/-! ### The canonical key, step by step -/

/-- `canonicalMIMEHeaderKey`'s change of one byte, `upper` its flag: `http.canonLoop`'s. -/
def canonStep (upper : Bool) (c : w8) : w8 :=
  if upper = true ∧ 97 ≤ c.toNat ∧ c.toNat ≤ 122 then c - W8 32
  else if upper = false ∧ 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c + W8 32 else c

/-- The flag after the bytes `xs`, from `u`: whether the last one is `-`. -/
def upAfter (u : Bool) : List w8 → Bool
  | [] => u
  | c :: cs => upAfter (c == W8 45) cs

/-- A byte is `-` after its step exactly when it was. -/
theorem canonStep_dash (u : Bool) (c : w8) : (canonStep u c == W8 45) = (c == W8 45) := by
  revert u c; decide

theorem canonLoop_cons (u : Bool) (c : w8) (cs : List w8) :
    http.canonLoop u (c :: cs) = canonStep u c :: http.canonLoop (c == W8 45) cs := by
  rw [http.canonLoop, ← canonStep_dash u c]; rfl

theorem canonLoop_length (u : Bool) (xs : List w8) : (http.canonLoop u xs).length = xs.length := by
  induction xs generalizing u with
  | nil => rfl
  | cons c cs ih => rw [canonLoop_cons]; simp [ih]

theorem canonLoop_snoc (u : Bool) (xs : List w8) (c : w8) :
    http.canonLoop u (xs ++ [c]) = http.canonLoop u xs ++ [canonStep (upAfter u xs) c] := by
  induction xs generalizing u with
  | nil => rw [List.nil_append, canonLoop_cons]; rfl
  | cons x xs ih => rw [List.cons_append, canonLoop_cons, canonLoop_cons, ih]; rfl

theorem upAfter_snoc (u : Bool) (xs : List w8) (c : w8) : upAfter u (xs ++ [c]) = (c == W8 45) := by
  induction xs generalizing u with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem beq_w8 (c d : w8) : (c == d) = decide (c = d) := by
  cases h : decide (c = d) <;> simp_all

/-- The prefix of `s` of length `j + 1`. -/
theorem take_succ_of_lt (s : List w8) (j : Nat) (c : w8) (h : s[j]? = some c) :
    s.take (j + 1) = s.take j ++ [c] := by
  rw [List.take_add_one, h]; rfl

/-! The cases of `canonStep`, as the code tests them. -/
theorem canonStep_t_lo (y : w8) (h1 : uint.Z (W8 97) ≤ uint.Z y) (h2 : uint.Z y ≤ uint.Z (W8 122)) :
    canonStep true y = y - W8 32 := by revert y; decide
theorem canonStep_t_n1 (y : w8) (h1 : ¬ uint.Z (W8 97) ≤ uint.Z y) : canonStep true y = y := by
  revert y; decide
theorem canonStep_t_n2 (y : w8) (h2 : ¬ uint.Z y ≤ uint.Z (W8 122)) : canonStep true y = y := by
  revert y; decide
theorem canonStep_f_up (y : w8) (h1 : uint.Z (W8 65) ≤ uint.Z y) (h2 : uint.Z y ≤ uint.Z (W8 90)) :
    canonStep false y = y + W8 32 := by revert y; decide
theorem canonStep_f_n1 (y : w8) (h1 : ¬ uint.Z (W8 65) ≤ uint.Z y) : canonStep false y = y := by
  revert y; decide
theorem canonStep_f_n2 (y : w8) (h2 : ¬ uint.Z y ≤ uint.Z (W8 90)) : canonStep false y = y := by
  revert y; decide

/-- The bytes of `s` with the first `j` canonicalized: their `j`th is `s`'s. -/
theorem canon_lookup (s : List w8) (j : Nat) (y : w8) (h : s[j]? = some y) :
    (http.canonLoop true (s.take j) ++ s.drop j)[j]? = some y := by
  have hj : j < s.length := by
    rcases Nat.lt_or_ge j s.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have hl : (http.canonLoop true (s.take j)).length = j := by
    rw [canonLoop_length, List.length_take]; omega
  rw [List.getElem?_append_right (by omega), hl, Nat.sub_self, List.getElem?_drop, Nat.add_zero, h]

/-- Canonicalizing the `j`th byte of `s`. -/
theorem canon_set (s : List w8) (j : Nat) (y : w8) (h : s[j]? = some y) :
    (http.canonLoop true (s.take j) ++ s.drop j).set j (canonStep (upAfter true (s.take j)) y) =
      http.canonLoop true (s.take (j + 1)) ++ s.drop (j + 1) := by
  have hj : j < s.length := by
    rcases Nat.lt_or_ge j s.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have hl : (http.canonLoop true (s.take j)).length = j := by
    rw [canonLoop_length, List.length_take]; omega
  have hd : s.drop j = y :: s.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj]; congr 1
    rw [List.getElem?_eq_getElem hj] at h; exact Option.some.inj h
  rw [take_succ_of_lt s j y h, canonLoop_snoc, hd, List.set_append_right _ _ (by omega), hl,
    Nat.sub_self, List.set_cons_zero, List.append_assoc]
  rfl

/-- `canonKey` of a key with a byte that is not a token byte: the key. -/
theorem canonKey_of_not_token (s : List w8) (c : w8) (hc : c ∈ s) (h : http.hdrTokenByte c = false) :
    http.canonKey s = s := by
  unfold http.canonKey
  split
  · rename_i hall
    have := List.all_eq_true.1 hall c hc
    rw [h] at this; exact absurd this Bool.false_ne_true
  · rfl

/-- `canonKey` of a key of token bytes: `canonLoop`. -/
theorem canonKey_of_token (s : List w8) (h : ∀ c ∈ s, http.hdrTokenByte c = true) :
    http.canonKey s = http.canonLoop true s := by
  unfold http.canonKey
  simp only [List.all_eq_true.2 h, ↓reduceIte]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.net.textproto.Assumptions]

/-- The two masks of `validHeaderFieldByte` are the token bytes. -/
theorem validHeaderFieldByte_eq (c : w8) :
    (!decide (W64 1 <<< W64 (uint.Z c) &&& W64 288068722172624896 |||
        W64 1 <<< W64 (uint.Z (c - W8 64)) &&& W64 6341068274398134270 = W64 0)) =
      http.hdrTokenByte c := by
  revert c; decide

/-- `validHeaderFieldByte(c)` (`reader.go:693`): its two 64-bit masks are the token bytes,
`http.hdrTokenByte`. -/
theorem wp_validHeaderFieldByte (c : w8) :
    {{ (True : IProp GF) }}
      (App (Val (@! validHeaderFieldByte)) (Val #c))
    {{ RET #(http.hdrTokenByte c); True }} := by
  wp_start
  wp_auto
  rw [validHeaderFieldByte_eq]
  iapply HΦ; itrivial

/-- `initCommonHeader()` (`reader.go:811`): a map of forty keys, each to itself, into
`commonHeader`, which it leaves read-only. -/
theorem wp_initCommonHeader :
    {{ commonHeaderVar (GF := GF) }}
      (App (Val (@! initCommonHeader)) (Val #()))
    {{ RET #(); commonHeaderOk }} := by
  wp_start as HP
  unfold commonHeaderVar
  icases HP with ⟨%m0, Hv⟩
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %m Hm
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sl ⟨Hsl, -⟩
  try wp_auto
  ihave IH : (∃ (j : w64) (x : GoString) (M : GMap GoString GoString) (L : List GoString),
      "i" ∷ i_ptr ↦ j ∗ "v" ∷ v_ptr ↦ x ∗ "Hm" ∷ m ↦$ M ∗ "Hsl" ∷ _ ↦* L ∗
      "%HM" ∷ ⌜(∀ k w, M !! k = some w → w = k) ∧ 0 ≤ sint.Z j⌝ : IProp GF) $$ [i v Hm Hsl]
  · iexists _, _, _, _; iframe
    ipureintro; refine ⟨?_, by decide⟩; intro k w h; simp at h
  iapply wp_fupd
  wp_for IH
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_if_destruct
  · have Hj : sint.nat j < L.length := by have := HM.2; simp only at Hlen; word
    list_elem L (sint.nat j) as y
    try wp_auto
    rw [ite_eq_left (by exact ⟨HM.2, Hif⟩)]
    wp_apply wp_load_slice_index _ (sint.Z j) L _ y HM.2 $$ [Hsl] with Hsl
    · iframe Hsl; ipureintro; exact Hy_lookup
    try wp_auto
    wp_apply wp_mapInsert go.string m M y y $$ Hm as Hm
    try wp_auto
    wp_for_post
    iframe
    iexists (j + W64 1), y, _, L
    iframe
    ipureintro
    refine ⟨?_, by word⟩
    intro k w h
    rcases (GMap.lookup_insert_Some _ _ _ _ _).1 h with ⟨rfl, rfl⟩ | ⟨-, h⟩
    · rfl
    · exact HM.1 _ _ h
  · ipersist Hv
    imod (ownMap_persist m (DFrac.own 1) M) $$ Hm with #Hm
    imodintro
    iapply HΦ
    unfold commonHeaderOk
    iexists m, M
    iframe Hv Hm
    ipureintro; exact HM.1

/-- `canonicalMIMEHeaderKey(a)` (`reader.go:757`) of a slice of the bytes `s`: `canonKey s` (with
the interned common key, which is the same string). -/
theorem wp_canonicalMIMEHeaderKey (a : GoSlice) (s : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.textproto ∗ a ↦* s }}
      (App (Val (@! canonicalMIMEHeaderKey)) (Val #a))
    {{ (ok : Bool), RET (PairV #(http.canonKey s) #ok); True }} := by
  wp_start as Ha
  ihave HΦ : (∀ (k : GoString) (ok : Bool), ⌜k = http.canonKey s⌝ -∗ Φ (PairV #k #ok)) $$ [HΦ]
  · iintro %k %ok %hk; subst hk; iapply HΦ; itrivial
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Ha
  wp_if_destruct
  · have hs : s = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1, Hif]; rfl)
    iapply HΦ; ipureintro; subst hs; rfl
  try wp_auto
  ihave IH : (∃ (j : w64) (cv : w8),
      "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ cv ∗ "Ha" ∷ a ↦* s ∗
      "noCanon" ∷ noCanon_ptr ↦ decide (W8 32 ∈ s.take (sint.nat j)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ s.length ∧
        ∀ c ∈ s.take (sint.nat j), http.hdrTokenByte c = true ∨ c = W8 32⌝ : IProp GF)
    $$ [i c Ha noCanon]
  · iexists _, _; iframe
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    simp only [List.not_mem_nil, decide_false]
    iframe
    ipureintro; simp
  wp_for IH
  wp_if_destruct
  · have Hjl : sint.nat j < s.length := by word
    list_elem s (sint.nat j) as y
    try wp_auto
    rw [ite_eq_left (by exact ⟨Hj.1, Hif⟩)]
    wp_apply wp_load_slice_index a (sint.Z j) s _ y Hj.1 $$ [Ha] with Ha
    · iframe Ha; ipureintro; exact Hy_lookup
    try wp_auto
    wp_apply wp_validHeaderFieldByte
    have hn : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have hmem : y ∈ s := List.mem_of_getElem? Hy_lookup
    by_cases Htok : http.hdrTokenByte y = false
    · rw [Htok]
      try wp_auto
      wp_if_destruct
      · -- a space: `noCanon = true`, `continue`
        wp_for_post
        iframe
        iexists (j + W64 1), W8 32
        rw [hn, take_succ_of_lt s _ (W8 32) Hy_lookup]
        have hd : decide (W8 32 ∈ s.take (sint.nat j) ++ [W8 32]) = true := by
          simp
        rw [hd]
        iframe
        ipureintro
        refine ⟨by word, by rw [← hn]; word, ?_⟩
        intro c hc
        rcases List.mem_append.1 hc with hc | hc
        · exact Hj.2.2 c hc
        · rw [List.mem_singleton.1 hc]; exact Or.inr rfl
      · -- another byte: `return string(a), false`, the key unchanged
        wp_apply wp_bytes_to_string a s _ $$ Ha as Ha
        try wp_auto
        wp_for_post
        iapply HΦ; ipureintro; exact (canonKey_of_not_token s y hmem Htok).symm
    · -- a token byte: `continue`
      rw [Bool.not_eq_false] at Htok
      rw [Htok]
      have hy32 : y ≠ W8 32 := by rintro rfl; revert Htok; decide
      try wp_auto
      wp_for_post
      iframe
      iexists (j + W64 1), y
      rw [hn, take_succ_of_lt s _ y Hy_lookup]
      have hd : decide (W8 32 ∈ s.take (sint.nat j) ++ [y]) = decide (W8 32 ∈ s.take (sint.nat j)) := by
        rw [decide_eq_decide]
        constructor
        · intro h
          rcases List.mem_append.1 h with h | h
          · exact h
          · exact absurd (List.mem_singleton.1 h).symm hy32
        · intro h; exact List.mem_append_left _ h
      rw [hd]
      iframe
      ipureintro
      refine ⟨by word, by rw [← hn]; word, ?_⟩
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact Hj.2.2 c hc
      · rw [List.mem_singleton.1 hc]; exact Or.inl Htok
  -- the loop done: every byte a token byte or a space
  have hjl : sint.nat j = s.length := by word
  rw [hjl, List.take_length] at Hj
  rw [hjl, List.take_length]
  try wp_auto
  wp_if_destruct
  · -- a space: `return string(a), true`, the key unchanged
    wp_apply wp_bytes_to_string a s _ $$ Ha as Ha
    try wp_auto
    iapply HΦ; ipureintro
    exact (canonKey_of_not_token s (W8 32) Hif (by decide)).symm
  have htok : ∀ c ∈ s, http.hdrTokenByte c = true := by
    intro c hc
    rcases Hj.2.2 c hc with h | h
    · exact h
    · subst h; exact absurd hc Hif
  try wp_auto
  rename_i ip0
  irename: (ip0 ↦ (zero_val w64 : w64)) => i0
  ihave IH : (∃ (j : w64) (cv : w8) (iv : w64),
      "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ cv ∗ "i0" ∷ ip0 ↦ iv ∗
      "Ha" ∷ a ↦* (http.canonLoop true (s.take (sint.nat j)) ++ s.drop (sint.nat j)) ∗
      "upper" ∷ upper_ptr ↦ upAfter true (s.take (sint.nat j)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ s.length⌝ : IProp GF)
    $$ [i c i0 Ha upper]
  · iexists _, _, _; iframe
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    iframe
    ipureintro; simp
  wp_for IH
  wp_if_destruct
  · have Hjl : sint.nat j < s.length := by word
    list_elem s (sint.nat j) as y
    try wp_auto
    rw [ite_eq_left (by exact ⟨Hj.1, Hif⟩)]
    wp_apply wp_load_slice_index a (sint.Z j) _ _ y Hj.1 $$ [Ha] with Ha
    · iframe Ha; ipureintro; exact canon_lookup s _ y Hy_lookup
    try wp_auto
    have Hjb := Hif
    have hn : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have hz : (sint.Z j).toNat = sint.nat j := rfl
    have hlenA : (http.canonLoop true (s.take (sint.nat j)) ++ s.drop (sint.nat j)).length = s.length := by
      rw [List.length_append, canonLoop_length, List.length_take, List.length_drop]; omega
    generalize hu : upAfter true (s.take (sint.nat j)) = u
    cases u
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_if_destruct
        · try wp_auto
          have hcv : canonStep false y = y + W8 32 := by
            exact canonStep_f_up y ‹_› ‹_›
          rw [ite_eq_left (by exact ⟨Hj.1, Hjb⟩)]
          wp_apply wp_store_slice_index a (sint.Z j) _ (y + W8 32) $$ [Ha] with Ha
          · iframe Ha; ipureintro; rw [hlenA]; word
          try wp_auto
          wp_for_post
          iframe
          iexists (j + W64 1), (y + W8 32), j
          have hset : (http.canonLoop true (s.take (sint.nat j)) ++ s.drop (sint.nat j)).set (sint.nat j) (y + W8 32) =
              http.canonLoop true (s.take (sint.nat j + 1)) ++ s.drop (sint.nat j + 1) := by
            rw [← canon_set s _ y Hy_lookup, hu, hcv]
          rw [hn, hset, take_succ_of_lt s _ y Hy_lookup, upAfter_snoc, beq_w8]
          have hdash : decide ((y + W8 32) = W8 45) = decide (y = W8 45) := by
            have h := canonStep_dash false y; rw [hcv] at h; simpa only [beq_w8] using h
          rw [hdash]
          iframe
          ipureintro; constructor <;> word
        · try wp_auto
          have hcv : canonStep false y = y := by
            exact canonStep_f_n2 y ‹_›
          rw [ite_eq_left (by exact ⟨Hj.1, Hjb⟩)]
          wp_apply wp_store_slice_index a (sint.Z j) _ (y) $$ [Ha] with Ha
          · iframe Ha; ipureintro; rw [hlenA]; word
          try wp_auto
          wp_for_post
          iframe
          iexists (j + W64 1), (y), j
          have hset : (http.canonLoop true (s.take (sint.nat j)) ++ s.drop (sint.nat j)).set (sint.nat j) (y) =
              http.canonLoop true (s.take (sint.nat j + 1)) ++ s.drop (sint.nat j + 1) := by
            rw [← canon_set s _ y Hy_lookup, hu, hcv]
          rw [hn, hset, take_succ_of_lt s _ y Hy_lookup, upAfter_snoc, beq_w8]
          iframe
          ipureintro; constructor <;> word
      · try wp_auto
        have hcv : canonStep false y = y := by
          exact canonStep_f_n1 y ‹_›
        rw [ite_eq_left (by exact ⟨Hj.1, Hjb⟩)]
        wp_apply wp_store_slice_index a (sint.Z j) _ (y) $$ [Ha] with Ha
        · iframe Ha; ipureintro; rw [hlenA]; word
        try wp_auto
        wp_for_post
        iframe
        iexists (j + W64 1), (y), j
        have hset : (http.canonLoop true (s.take (sint.nat j)) ++ s.drop (sint.nat j)).set (sint.nat j) (y) =
            http.canonLoop true (s.take (sint.nat j + 1)) ++ s.drop (sint.nat j + 1) := by
          rw [← canon_set s _ y Hy_lookup, hu, hcv]
        rw [hn, hset, take_succ_of_lt s _ y Hy_lookup, upAfter_snoc, beq_w8]
        iframe
        ipureintro; constructor <;> word
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_if_destruct
        · try wp_auto
          have hcv : canonStep true y = y - W8 32 := by
            exact canonStep_t_lo y ‹_› ‹_›
          rw [ite_eq_left (by exact ⟨Hj.1, Hjb⟩)]
          wp_apply wp_store_slice_index a (sint.Z j) _ (y - W8 32) $$ [Ha] with Ha
          · iframe Ha; ipureintro; rw [hlenA]; word
          try wp_auto
          wp_for_post
          iframe
          iexists (j + W64 1), (y - W8 32), j
          have hset : (http.canonLoop true (s.take (sint.nat j)) ++ s.drop (sint.nat j)).set (sint.nat j) (y - W8 32) =
              http.canonLoop true (s.take (sint.nat j + 1)) ++ s.drop (sint.nat j + 1) := by
            rw [← canon_set s _ y Hy_lookup, hu, hcv]
          rw [hn, hset, take_succ_of_lt s _ y Hy_lookup, upAfter_snoc, beq_w8]
          have hdash : decide ((y - W8 32) = W8 45) = decide (y = W8 45) := by
            have h := canonStep_dash true y; rw [hcv] at h; simpa only [beq_w8] using h
          rw [hdash]
          iframe
          ipureintro; constructor <;> word
        · try wp_auto
          have hcv : canonStep true y = y := by
            exact canonStep_t_n2 y ‹_›
          rw [ite_eq_left (by exact ⟨Hj.1, Hjb⟩)]
          wp_apply wp_store_slice_index a (sint.Z j) _ (y) $$ [Ha] with Ha
          · iframe Ha; ipureintro; rw [hlenA]; word
          try wp_auto
          wp_for_post
          iframe
          iexists (j + W64 1), (y), j
          have hset : (http.canonLoop true (s.take (sint.nat j)) ++ s.drop (sint.nat j)).set (sint.nat j) (y) =
              http.canonLoop true (s.take (sint.nat j + 1)) ++ s.drop (sint.nat j + 1) := by
            rw [← canon_set s _ y Hy_lookup, hu, hcv]
          rw [hn, hset, take_succ_of_lt s _ y Hy_lookup, upAfter_snoc, beq_w8]
          iframe
          ipureintro; constructor <;> word
      · try wp_auto
        have hcv : canonStep true y = y := by
          exact canonStep_t_n1 y ‹_›
        rw [ite_eq_left (by exact ⟨Hj.1, Hjb⟩)]
        wp_apply wp_store_slice_index a (sint.Z j) _ (y) $$ [Ha] with Ha
        · iframe Ha; ipureintro; rw [hlenA]; word
        try wp_auto
        wp_for_post
        iframe
        iexists (j + W64 1), (y), j
        have hset : (http.canonLoop true (s.take (sint.nat j)) ++ s.drop (sint.nat j)).set (sint.nat j) (y) =
            http.canonLoop true (s.take (sint.nat j + 1)) ++ s.drop (sint.nat j + 1) := by
          rw [← canon_set s _ y Hy_lookup, hu, hcv]
        rw [hn, hset, take_succ_of_lt s _ y Hy_lookup, upAfter_snoc, beq_w8]
        iframe
        ipureintro; constructor <;> word
  -- the loop done: `a` holds `canonLoop true s`
  have hjl : sint.nat j = s.length := by word
  rw [hjl, List.take_length, List.drop_length, List.append_nil]
  ihave #Hi := isPkgInit_access _ $$ Hpkg
  rw [isPkgInitDef_textproto]
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  try wp_auto
  wp_apply (_root_.Perennial.sync.Once.wp_Do (globalAddr commonHeaderOnce) commonHeaderVar
    commonHeaderOk _) $$ [] as #Hok
  · isplitr
    · unfold textprotoInitLC; iexact Hi
    iintro !> %Ψ HP HΨ
    wp_apply wp_initCommonHeader $$ HP as HQ
    iapply HΨ $$ HQ
  unfold commonHeaderOk
  icases Hok with ⟨%m, %M, #Hv, #Hm, %HM⟩
  have hk : http.canonKey s = http.canonLoop true s := canonKey_of_token s htok
  wp_apply wp_bytes_to_string a _ _ $$ Ha as Ha
  try wp_auto
  wp_apply (wp_map_lookup1 go.string go.string m M (http.canonLoop true s) DFrac.discard) $$ Hm as -
  try wp_auto
  wp_if_destruct
  · -- no interned key
    try wp_auto
    wp_apply wp_bytes_to_string a _ _ $$ Ha as Ha
    try wp_auto
    iapply HΦ; ipureintro; exact hk.symm
  · -- the interned key: `M`'s value at the key is the key
    have hv : (M !! http.canonLoop true s).getD (zero_val GoString) = http.canonLoop true s := by
      cases hM : M !! http.canonLoop true s with
      | none => rw [hM] at Hif; exact absurd rfl Hif
      | some v => exact HM _ _ hM
    rw [hv]
    try wp_auto
    iapply HΦ; ipureintro; exact hk.symm

/-- `CanonicalMIMEHeaderKey(s)` (`reader.go:662`): `canonKey s`. -/
theorem wp_CanonicalMIMEHeaderKey (s : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.textproto }}
      (App (Val (@! CanonicalMIMEHeaderKey)) (Val #s))
    {{ RET #(http.canonKey s); True }} := by
  wp_start
  ihave HΦ : (∀ k : GoString, ⌜k = http.canonKey s⌝ -∗ Φ #k) $$ [HΦ]
  · iintro %k %hk; subst hk; iapply HΦ; itrivial
  try wp_auto
  ihave IH : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "s" ∷ s_ptr ↦ s ∗
      "upper" ∷ upper_ptr ↦ upAfter true (s.take (sint.nat j)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ s.length ∧
        (∀ c ∈ s.take (sint.nat j), http.hdrTokenByte c = true) ∧
        http.canonLoop true (s.take (sint.nat j)) = s.take (sint.nat j)⌝ : IProp GF) $$ [i s upper]
  · iexists _; iframe
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; simp; rfl
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl
  try wp_auto
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z (W64 s.length) := of_decide_eq_true (go.intoVal_inj Hif)
    have Hjl : sint.nat j < s.length := by word
    list_elem s (sint.nat j) as y
    rw [ite_eq_left Hj.1, Hy_lookup]
    try wp_auto
    wp_apply wp_validHeaderFieldByte
    have hn : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have hmem : y ∈ s := List.mem_of_getElem? Hy_lookup
    by_cases Htok : http.hdrTokenByte y = false
    · -- not a token byte: `return s`
      rw [Htok]
      try wp_auto
      wp_for_post
      iapply HΦ; ipureintro; exact (canonKey_of_not_token s y hmem Htok).symm
    rw [Bool.not_eq_false] at Htok
    rw [Htok]
    try wp_auto
    generalize hu : upAfter true (s.take (sint.nat j)) = u
    cases u
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_if_destruct
        · try wp_auto
          wp_apply wp_string_to_bytes s as %sl ⟨Hsl', -⟩
          wp_apply wp_canonicalMIMEHeaderKey sl s $$ [$Hsl'] as %ok -
          try wp_auto
          wp_for_post
          iapply HΦ; ipureintro; rfl
        · try wp_auto
          wp_for_post
          iframe
          iexists (j + W64 1)
          have hcs : canonStep false y = y := canonStep_f_n2 y ‹_›
          rw [hn, take_succ_of_lt s _ y Hy_lookup, upAfter_snoc, beq_w8]
          iframe
          ipureintro
          refine ⟨by word, by omega, ?_, ?_⟩
          · intro c hc
            rcases List.mem_append.1 hc with hc | hc
            · exact Hj.2.2.1 c hc
            · rw [List.mem_singleton.1 hc]; exact Htok
          · rw [canonLoop_snoc, hu, hcs, Hj.2.2.2]
      · try wp_auto
        wp_for_post
        iframe
        iexists (j + W64 1)
        have hcs : canonStep false y = y := canonStep_f_n1 y ‹_›
        rw [hn, take_succ_of_lt s _ y Hy_lookup, upAfter_snoc, beq_w8]
        iframe
        ipureintro
        refine ⟨by word, by omega, ?_, ?_⟩
        · intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact Hj.2.2.1 c hc
          · rw [List.mem_singleton.1 hc]; exact Htok
        · rw [canonLoop_snoc, hu, hcs, Hj.2.2.2]
    · try wp_auto
      wp_if_destruct
      · try wp_auto
        wp_if_destruct
        · try wp_auto
          wp_apply wp_string_to_bytes s as %sl ⟨Hsl', -⟩
          wp_apply wp_canonicalMIMEHeaderKey sl s $$ [$Hsl'] as %ok -
          try wp_auto
          wp_for_post
          iapply HΦ; ipureintro; rfl
        · try wp_auto
          wp_for_post
          iframe
          iexists (j + W64 1)
          have hcs : canonStep true y = y := canonStep_t_n2 y ‹_›
          rw [hn, take_succ_of_lt s _ y Hy_lookup, upAfter_snoc, beq_w8]
          iframe
          ipureintro
          refine ⟨by word, by omega, ?_, ?_⟩
          · intro c hc
            rcases List.mem_append.1 hc with hc | hc
            · exact Hj.2.2.1 c hc
            · rw [List.mem_singleton.1 hc]; exact Htok
          · rw [canonLoop_snoc, hu, hcs, Hj.2.2.2]
      · try wp_auto
        wp_for_post
        iframe
        iexists (j + W64 1)
        have hcs : canonStep true y = y := canonStep_t_n1 y ‹_›
        rw [hn, take_succ_of_lt s _ y Hy_lookup, upAfter_snoc, beq_w8]
        iframe
        ipureintro
        refine ⟨by word, by omega, ?_, ?_⟩
        · intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact Hj.2.2.1 c hc
          · rw [List.mem_singleton.1 hc]; exact Htok
        · rw [canonLoop_snoc, hu, hcs, Hj.2.2.2]
  · have Hge : ¬ sint.Z j < sint.Z (W64 s.length) := fun h => Hif (by rw [decide_eq_true h])
    have hjl : sint.nat j = s.length := by word
    rw [hjl, List.take_length] at Hj
    rw [decide_eq_false Hge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    iapply HΦ; ipureintro
    rw [canonKey_of_token s Hj.2.2.1, Hj.2.2.2]

end proof

end textproto
end EtcdGrove
end Perennial
