/-
`internal/json`'s `AppendKey`, `AppendString` and `appendStringComplex` (dsv-retire-3, 2026-11-26,
mit-pdos/etcd-grove#49 step 3), what `(*Event).Str` calls: each appends to an owned byte slice and
returns the slice it grew (`AppendString`'s first `append` makes what it returns non-empty, which
`AppendKey`'s read of `dst[len(dst)-1]` needs of its argument). Lemmas over the translation (not a
function's `wp_proof`), each taking Perennial's `utf8.DecodeRuneInString` spec, which the linking
module passes.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.internal.json.Base
public import Perennial.Spec.unicode.utf8.DecodeRuneInString
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.rs.zerolog.internal.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.rs.zerolog.internal.json.Assumptions]

attribute [-instance] go.SliceSemantics.composite_literal_slice

/-- The digits of `hex`, as the semantics evaluates the constant (`hex_get`'s statement spells the
list out: the rewrite must find it syntactically in the goal). -/
abbrev hexDigits : List w8 :=
    [48#8, 49#8, 50#8, 51#8, 52#8, 53#8, 54#8, 55#8, 56#8, 57#8, 97#8, 98#8, 99#8, 100#8, 101#8,
      102#8]

/-- `hex[k]`, for `k < 16`: in bounds. -/
theorem hex_get (k : Nat) (h : k < 16) :
    ([48#8, 49#8, 50#8, 51#8, 52#8, 53#8, 54#8, 55#8, 56#8, 57#8, 97#8, 98#8, 99#8, 100#8, 101#8,
      102#8] : List w8)[k]? = some (hexDigits.getD k 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
  rfl

/-- `hex[b>>4]`: in bounds. -/
theorem hex_get_shr (y : w8) :
    ([48#8, 49#8, 50#8, 51#8, 52#8, 53#8, 54#8, 55#8, 56#8, 57#8, 97#8, 98#8, 99#8, 100#8, 101#8,
      102#8] : List w8)[sint.nat (W64 (uint.Z (y >>> W64 4)))]? =
      some (hexDigits.getD (sint.nat (W64 (uint.Z (y >>> W64 4)))) 0) :=
  hex_get _ (by
    have := strconv.lowerhex_idx_shr_w8_hi y
    have := strconv.lowerhex_idx_shr_w8_lo y
    word)

/-- `hex[b&0xF]`: in bounds. -/
theorem hex_get_and (y : w8) :
    ([48#8, 49#8, 50#8, 51#8, 52#8, 53#8, 54#8, 55#8, 56#8, 57#8, 97#8, 98#8, 99#8, 100#8, 101#8,
      102#8] : List w8)[sint.nat (W64 (uint.Z (y &&& W8 15)))]? =
      some (hexDigits.getD (sint.nat (W64 (uint.Z (y &&& W8 15)))) 0) :=
  hex_get _ (by
    have := strconv.lowerhex_idx_and_w8_hi y
    have := strconv.lowerhex_idx_and_w8_lo y
    word)

/-- `appendStringComplex(dst, s, i)`, for `0 ≤ i ≤ len(s)`: appends to `dst`. -/
theorem wp_appendStringComplex
    (wp_DecodeRuneInString : unicode.utf8.DecodeRuneInString.spec (GF := GF) (hG := hG))
    (dst : GoSlice) (bs : List w8) (s : GoString) (i : w64)
    (hi : 0 ≤ sint.Z i ∧ sint.Z i ≤ s.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog.internal.json ∗
        dst ↦* bs ∗ ownSliceCap w8 dst (DFrac.own 1) }}
      (App (App (App (Val (@! appendStringComplex)) (Val #dst)) (Val #s)) (Val #i))
    {{ (dst' : GoSlice), RET #dst';
        ∃ q : List w8, dst' ↦* (bs ++ q) ∗ ownSliceCap w8 dst' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  ihave #Hi := jsonInit_access $$ Hpkg
  unfold jsonInit
  icases Hi with ⟨-, %tbl, #Htbl⟩
  ihave #Hutf8 : isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 $$ []
  · iPkgInit
  wp_auto
  ihave HI : (∃ (iv sv : w64) (d : GoSlice) (q : List w8),
      "i" ∷ i_ptr ↦ iv ∗ "start" ∷ start_ptr ↦ sv ∗ "dst" ∷ dst_ptr ↦ d ∗
      "Hb" ∷ d ↦* (bs ++ q) ∗ "Hcap" ∷ ownSliceCap w8 d (DFrac.own 1) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z sv ∧ sint.Z sv ≤ sint.Z iv ∧ sint.Z iv ≤ s.length⌝ : IProp GF)
      $$ [i start dst Hb Hcap]
  · iexists i, (W64 0), dst, []
    simp only [List.append_nil]
    iframe
    ipureintro
    refine ⟨by word, by word, hi.2⟩
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hslen
  wp_if_destruct
  · have hiv : sint.Z iv < s.length := by
      have := of_decide_eq_true (go.intoVal_inj Hif); word
    obtain ⟨b, hb⟩ : ∃ b, s[sint.nat iv]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    rw [ite_eq_left (show 0 ≤ sint.Z iv by word), hb]
    ihave %Htlen := array_len _ _ _ _ $$ Htbl
    have hbi : (sint.Z (W64 (uint.Z b))).toNat < tbl.arr.length := by
      have : (tbl.arr.length : Int) = 256 := Htlen.symm
      word
    icases array_acc (V := Bool) (globalAddr noEscapeTable) (sint.Z (W64 (uint.Z b))) _ _ _
      (tbl.arr[(sint.Z (W64 (uint.Z b))).toNat]) (by word)
      (List.getElem?_eq_getElem hbi) $$ Htbl with ⟨#Hx, -⟩
    generalize tbl.arr[(sint.Z (W64 (uint.Z b))).toNat] = x
    wp_auto
    wp_if_destruct
    · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      have hlw : sint.Z (W64 (s.length : Int)) = s.length := by word
      rw [ite_eq_left ⟨by word, by word, by word⟩]
      generalize hrest : List.take (sint.nat (W64 (s.length : Int)) - sint.nat iv)
        (List.drop (sint.nat iv) s) = rest
      have hrl : (rest.length : Int) = s.length - sint.Z iv := by
        subst hrest; simp only [List.length_take, List.length_drop]; word
      wp_auto
      wp_apply wp_DecodeRuneInString as %rv %wv %Hw
      have hw : 1 ≤ sint.Z wv ∧ sint.Z wv ≤ rest.length := by
        rcases Hw.1 with ⟨h, -⟩ | ⟨-, h⟩
        · subst h; simp at hrl; word
        · exact h
      clear Hw
      repeat' (first
        | wp_if_destruct
        | wp_auto
        | (rw [ite_eq_left (by word)])
        | (wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
           wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
             as %d' ⟨Hb, Hcap, -⟩)
)
      all_goals (
        wp_for_post
        iframe
        iexists _, _, _, _
        try simp only [List.append_assoc]
        iframe
        ipureintro
        word)
    · rw [ite_eq_left ⟨by word, by word⟩]
      repeat' (first
        | (rw [hex_get_shr])
        | (rw [hex_get_and])
        | wp_if_destruct
        | wp_auto
        | (rw [ite_eq_left (by word)])
        | (wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
           wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
             as %d' ⟨Hb, Hcap, -⟩)
        | (wp_apply wp_slice_literal
           isplitr
           ipureintro
           rfl
           iintro %sl ⟨Hsl, -⟩
           wp_auto
           wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
             as %d' ⟨Hb, Hcap, -⟩))
      all_goals (
        wp_for_post
        iframe
        iexists _, _, _, _
        try simp only [List.append_assoc]
        iframe
        ipureintro
        word)
  · have hc : ¬ sint.Z iv < sint.Z (W64 (s.length : Int)) :=
      fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    repeat' (first
      | wp_if_destruct
      | wp_auto
      | (wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-)
      | (rw [ite_eq_left (by word)])
      | (wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
         wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
           as %d' ⟨Hb, Hcap, -⟩))
    all_goals (
      iapply HΦ
      iexists _
      try simp only [List.append_assoc]
      iframe)

/-- `Encoder.AppendString(dst, s)`: appends a non-empty encoding of `s` to `dst`. -/
theorem wp_AppendString
    (wp_DecodeRuneInString : unicode.utf8.DecodeRuneInString.spec (GF := GF) (hG := hG))
    (e : Encoder) (dst : GoSlice) (bs : List w8) (s : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog.internal.json ∗
        dst ↦* bs ∗ ownSliceCap w8 dst (DFrac.own 1) }}
      (App (App (Val (e @!! Encoder.ty @!! go!"AppendString")) (Val #dst)) (Val #s))
    {{ (dst' : GoSlice), RET #dst';
        ∃ q : List w8, dst' ↦* (bs ++ q) ∗ ownSliceCap w8 dst' (DFrac.own 1) ∗ ⌜q ≠ []⌝ }} := by
  wp_start as ⟨Hb, Hcap⟩
  ihave #Hi := jsonInit_access $$ Hpkg
  unfold jsonInit
  icases Hi with ⟨-, %tbl, #Htbl⟩
  ihave %Htlen := array_len _ _ _ _ $$ Htbl
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
    as %d ⟨Hb, Hcap, -⟩
  ihave HI : (∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ s.length⌝ : IProp GF) $$ [i]
  · iexists (W64 0)
    iframe
    ipureintro
    refine ⟨by word, by word⟩
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hslen
  wp_if_destruct
  · have hiv : sint.Z iv < s.length := by
      have := of_decide_eq_true (go.intoVal_inj Hif); word
    obtain ⟨b, hb⟩ : ∃ b, s[sint.nat iv]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    rw [ite_eq_left (show 0 ≤ sint.Z iv by word), hb]
    have hbi : (sint.Z (W64 (uint.Z b))).toNat < tbl.arr.length := by
      have : (tbl.arr.length : Int) = 256 := Htlen.symm
      word
    icases array_acc (V := Bool) (globalAddr noEscapeTable) (sint.Z (W64 (uint.Z b))) _ _ _
      (tbl.arr[(sint.Z (W64 (uint.Z b))).toNat]) (by word)
      (List.getElem?_eq_getElem hbi) $$ Htbl with ⟨#Hx, -⟩
    generalize tbl.arr[(sint.Z (W64 (uint.Z b))).toNat] = x
    try wp_auto
    rw [ite_eq_left ⟨by word, by word⟩]
    try wp_auto
    cases x <;> simp only [Bool.not_false, Bool.not_true] <;> wp_auto
    · wp_apply (wp_appendStringComplex wp_DecodeRuneInString _ _ _ _ ⟨by word, by word⟩)
        $$ [$Hb $Hcap] as %d' ⟨%q', Hb, Hcap⟩
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl' ⟨Hsl', -⟩
      try wp_auto
      wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl']
        as %d'' ⟨Hb, Hcap, -⟩
      try wp_auto
      wp_for_post
      iapply HΦ
      iexists _
      simp only [List.append_assoc]
      iframe
      ipureintro
      simp
    · wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      word
  · have hc : ¬ sint.Z iv < sint.Z (W64 (s.length : Int)) :=
      fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    wp_apply wp_string_to_bytes as %sl' ⟨Hsl', -⟩
    wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl']
      as %d' ⟨Hb, Hcap, -⟩
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl'' ⟨Hsl'', -⟩
    try wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl'']
      as %d'' ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iexists _
    simp only [List.append_assoc]
    iframe
    ipureintro
    simp

/-- `Encoder.AppendKey(dst, key)`, for a non-empty `dst`: appends to it. -/
theorem wp_AppendKey
    (wp_DecodeRuneInString : unicode.utf8.DecodeRuneInString.spec (GF := GF) (hG := hG))
    (e : Encoder) (dst : GoSlice) (bs : List w8) (s : GoString) (hne : bs ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog.internal.json ∗
        dst ↦* bs ∗ ownSliceCap w8 dst (DFrac.own 1) }}
      (App (App (Val (e @!! Encoder.ty @!! go!"AppendKey")) (Val #dst)) (Val #s))
    {{ (dst' : GoSlice), RET #dst';
        ∃ q : List w8, dst' ↦* (bs ++ q) ∗ ownSliceCap w8 dst' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  ihave %Hblen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  have hpos : 0 < sint.Z dst.len := by
    have := List.length_pos_iff.mpr hne; word
  obtain ⟨c, hc⟩ : ∃ c, bs[(sint.Z (dst.len - W64 1)).toNat]? = some c :=
    ⟨_, List.getElem?_eq_getElem (by word)⟩
  have hset : bs.set (sint.Z (dst.len - W64 1)).toNat c = bs := by
    rw [List.getElem?_eq_some_iff] at hc
    obtain ⟨h, rfl⟩ := hc
    exact List.set_getElem_self h
  rw [ite_eq_left ⟨by word, by word⟩]
  icases ownSlice_elem_acc (V := w8) (sint.Z (dst.len - W64 1)) c dst _ bs (by word) hc $$ Hb
    with ⟨Hc, Hcl⟩
  wp_auto
  ihave Hb := Hcl $$ Hc
  rw [hset]
  wp_if_destruct
  · try wp_auto
    wp_method_call
    try wp_auto
    wp_apply (wp_AppendString wp_DecodeRuneInString) $$ [$Hb $Hcap] as %d'' ⟨%q', Hb, Hcap, -⟩
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl' ⟨Hsl', -⟩
    try wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl']
      as %d''' ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iexists _
    simp only [List.append_assoc]
    iframe
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
      as %d' ⟨Hb, Hcap, -⟩
    try wp_auto
    wp_method_call
    try wp_auto
    wp_apply (wp_AppendString wp_DecodeRuneInString) $$ [$Hb $Hcap] as %d'' ⟨%q', Hb, Hcap, -⟩
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl' ⟨Hsl', -⟩
    try wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl']
      as %d''' ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iexists _
    simp only [List.append_assoc]
    iframe

end proof

end github_com.rs.zerolog.internal.json

end Perennial
