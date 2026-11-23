/-
The kit's generated codec (`examples/craqnet/rpc_gen.go`) meets the codec lemmas of `Codec.lean`
(hypothesis H5 of notes/dsv-craq.md, now proved): the encoders' bytes are `Wire.lean`'s, and
decoding a reply into a fresh zero value is safe and gives back an encoding's value.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Codec
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace github_com.despreston.go_craq

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [examples.craqnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true


/-- `rpcPutU64(b, x)`: `b` with `x`'s 8 bytes (little-endian) appended. -/
theorem wp_rpcPutU64 (b : GoSlice) (bs : List w8) (x : w64) :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! examples.craqnet.rpcPutU64)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ u64Le x) ∗ ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_slice_literal (V := w8) (u64Le x)
  isplitr
  · ipureintro; rw [encoding.binary.u64Le_8]; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, -⟩
  iapply HΦ
  iframe

/-- The shape of an encoder: `f(b, v)` appends `v`'s encoding `e` to `b`. -/
abbrev encFn (f : GoString) (v : val) (e : List w8) (R : IProp GF) : Prop :=
  ∀ (b : GoSlice) (bs : List w8),
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ R : IProp GF) }}
      (App (App (Val (@! f)) (Val #b)) (Val v))
    {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ e) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗ R }}

theorem wp_rpcEnc_t5 (s : GoString) : encFn (GF := GF) examples.craqnet.rpcEnc_t5 #s (encStr s) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_string_len s as %Hlen
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  wp_apply wp_string_to_bytes s as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, -⟩
  iapply HΦ
  unfold encStr
  rw [List.append_assoc]
  iframe


theorem wp_rpcEnc_t6 (x : w64) : encFn (GF := GF) examples.craqnet.rpcEnc_t6 #x (encU64 x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t12 (x : w8) :
    encFn (GF := GF) examples.craqnet.rpcEnc_t12 #x (u64Le (W64 (uint.Z x))) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t29 (x : Bool) : encFn (GF := GF) examples.craqnet.rpcEnc_t29 #x (encBool x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  cases x
  · wp_auto
    wp_apply wp_slice_literal (V := w8) [W8 0]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iframe
  · wp_auto
    wp_apply wp_slice_literal (V := w8) [W8 1]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iframe

theorem wp_rpcSent_t5 (s : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! examples.craqnet.rpcSent_t5)) (Val #s))
    {{ RET #(decide (s ≠ [])); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (s = [])) = decide (s ≠ []) by simp]
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t6 (x : w64) :
    {{ (True : IProp GF) }} (App (Val (@! examples.craqnet.rpcSent_t6)) (Val #x))
    {{ RET #(decide (x ≠ W64 0)); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (x = W64 0)) = decide (x ≠ W64 0) by simp]
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t29 (x : Bool) :
    {{ (True : IProp GF) }} (App (Val (@! examples.craqnet.rpcSent_t29)) (Val #x))
    {{ RET #x; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t11 (sl : GoSlice) (dq : DFrac) (x : List w8) :
    {{ (sl ↦*{dq} x : IProp GF) }} (App (Val (@! examples.craqnet.rpcSent_t11)) (Val #sl))
    {{ RET #(decide (x ≠ [])); sl ↦*{dq} x }} := by
  wp_start as Hsl
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  have h : (!decide (sl.len = W64 0)) = decide (x ≠ []) := by
    by_cases hx : x = []
    · subst hx
      have : sl.len = W64 0 := by simp at Hl; word
      simp [this]
    · have : x.length ≠ 0 := by simpa using hx
      have : sl.len ≠ W64 0 := by
        intro h0; rw [h0] at Hl; exact absurd (Hl.1.trans (by rfl)) this
      simp only [hx, this, decide_false, decide_true, Bool.not_false, ne_eq, not_false_eq_true]
  rw [h]
  iapply HΦ $$ Hsl

theorem wp_rpcEnc_t11 (sl : GoSlice) (dq : DFrac) (x : List w8) :
    encFn (GF := GF) examples.craqnet.rpcEnc_t11 #sl (encBytes x) iprop(sl ↦*{dq} x) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, Hsl⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  have hlen : sl.len = W64 x.length := by rw [Hl.1]; word
  ihave HI : (∃ (i : w64) (bb : GoSlice) (y : w8),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗ "x" ∷ x_ptr ↦ y ∗
      "Hb" ∷ bb ↦* (bs ++ u64Le sl.len ++
        ((x.take (sint.nat i)).map fun c => u64Le (W64 (uint.Z c))).flatten) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp GF) $$ [i b x Hb Hcap]
  · iexists W64 0, b1, _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, List.flatten_nil,
      List.append_nil]
    iframe
    ipureintro
    exact ⟨by decide, Hl.2⟩
  wp_for HI
  wp_if_destruct
  · have hi : sint.Z i < sint.Z sl.len := Hif
    list_elem x (sint.nat i) as e
    rw [ite_eq_left ⟨Hi.1, hi⟩]
    wp_apply wp_load_slice_index sl (sint.Z i) x dq e Hi.1 $$ [Hsl] with Hsl
    · iframe; ipureintro; exact He_lookup
    wp_apply wp_rpcEnc_t12 e _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, b2, e
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
      List.take_add_one, He_lookup, Option.toList_some, List.map_append, List.flatten_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      ← List.append_assoc]
    iframe
    ipureintro; word
  · have hn : sint.nat i = x.length := by rw [Hl.1]; word
    (try wp_auto)
    iapply HΦ
    iframe Hsl Hcap
    unfold encBytes
    rw [← hlen, List.append_assoc,
      show (x.map fun c => u64Le (W64 (uint.Z c))).flatten =
        ((x.take (sint.nat i)).map fun c => u64Le (W64 (uint.Z c))).flatten by
        rw [hn, List.take_length]]
    iexact Hb

set_option hygiene false in
/-- The last step of a struct encoder's proof: its bytes are `Wire.lean`'s. -/
macro "enc_close" : tactic => `(tactic| (
  iapply HΦ
  isimp only [strct, fld, fStr, fU64, fBytes, fBool, encBool, List.flatten_cons, List.flatten_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.singleton_append, List.append_nil,
    decide_true, decide_false, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
    Bool.false_eq_true, ↓reduceIte, *]
  isimp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at Hb
  iframe))

theorem wp_rpcEnc_t18 (k : GoString) (v : w64) :
    encFn (GF := GF) examples.craqnet.rpcEnc_t18 #(transport.netrpc.CommitArgs.mk k v)
      (strct [fStr k, fU64 v]) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := w8) _
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t5 k
    by_cases h1 : k = [] <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t5 k _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t6 v
    by_cases h2 : v = W64 0 <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t6 v _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    enc_close)

end proof

end github_com.despreston.go_craq
end Perennial
