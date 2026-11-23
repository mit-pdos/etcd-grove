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
  (try isimp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at Hb)
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

theorem wp_rpcEnc_t22 :
    encFn (GF := GF) examples.craqnet.rpcEnc_t22 #transport.netrpc.EmptyArgs.mk
      (strct []) iprop(True) := by
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
    enc_close)

theorem wp_rpcEnc_t14 (k : GoString) (sl : GoSlice) (dq : DFrac) (x : List w8) :
    encFn (GF := GF) examples.craqnet.rpcEnc_t14 #(transport.netrpc.ClientWriteArgs.mk k sl)
      (strct [fStr k, fBytes x]) iprop(sl ↦*{dq} x) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, Hsl⟩
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
    wp_apply wp_rpcSent_t11 sl dq x $$ [$Hsl] as Hsl
    by_cases h2 : x = [] <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t11 sl dq x _ _ $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, Hsl⟩))
    )
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t31 (k : GoString) (sl : GoSlice) (dq : DFrac) (x : List w8) (v : w64) :
    encFn (GF := GF) examples.craqnet.rpcEnc_t31 #(transport.netrpc.WriteArgs.mk k sl v)
      (strct [fStr k, fBytes x, fU64 v]) iprop(sl ↦*{dq} x) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, Hsl⟩
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
    wp_apply wp_rpcSent_t11 sl dq x $$ [$Hsl] as Hsl
    by_cases h2 : x = [] <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t11 sl dq x _ _ $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, Hsl⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t6 v
    by_cases h3 : v = W64 0 <;> simp only [h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
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

theorem wp_rpcEnc_t28 (m : MetaV) :
    encFn (GF := GF) examples.craqnet.rpcEnc_t28
      #(transport.NodeMeta.mk m.isHead m.isTail m.prev m.next m.tail)
      (strct [fBool m.isHead, fBool m.isTail, fStr m.prev, fStr m.next, fStr m.tail]) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  rcases m with ⟨hd, tl, p, n, t⟩
  dsimp only
  (try wp_auto)
  wp_apply wp_slice_literal (V := w8) _
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t29 hd
    cases h1 : hd
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t29 _ _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t29 tl
    cases h2 : tl
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t29 _ _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t5 p
    by_cases h3 : p = [] <;> simp only [h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t5 p _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t5 n
    by_cases h4 : n = [] <;> simp only [h4, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t5 n _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t5 t
    by_cases h5 : t = [] <;> simp only [h5, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t5 t _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    enc_close)

/-- `rpcPutTag(tag)`: a new slice, the string `tag`'s encoding. -/
theorem wp_rpcPutTag (tag : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! examples.craqnet.rpcPutTag)) (Val #tag))
    {{ (b : GoSlice), RET #b; b ↦* encStr tag ∗ ownSliceCap w8 b (DFrac.own 1) }} := by
  wp_start
  wp_auto
  wp_apply wp_string_len tag as %Hlen
  ihave Hn := ownSlice_nil (V := w8) (DFrac.own 1)
  ihave Hnc := ownSliceCap_nil (V := w8)
  wp_apply wp_rpcPutU64 $$ [$Hn $Hnc] as %b1 ⟨Hb, Hcap⟩
  wp_apply wp_string_to_bytes tag as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, -⟩
  iapply HΦ
  unfold encStr
  iframe

/-- The entries of a request map, in the order of `keys`. -/
def reqEntries (req : GMap GoString w64) (keys : List GoString) : List (GoString × w64) :=
  keys.map fun k => (k, reqVer req k)

theorem wp_rpcEnc_t4 (mp : Loc) (dq : DFrac) (req : GMap GoString w64) (b : GoSlice) (bs : List w8) :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ ownMap mp dq req : IProp GF) }}
      (App (App (Val (@! examples.craqnet.rpcEnc_t4)) (Val #b)) (Val #mp))
    {{ (b' : GoSlice), RET #b'; ∃ es, ⌜entriesOf req es⌝ ∗
        b' ↦* (bs ++ encU64 (W64 es.length) ++ (es.map fun e => encStr e.1 ++ encU64 e.2).flatten) ∗
        ownSliceCap w8 b' (DFrac.own 1) ∗ ownMap mp dq req }} := by
  wp_start as ⟨Hb, Hcap, Hm⟩
  wp_auto
  wp_apply wp_map_len_lt mp req dq $$ [$Hm] as ⟨Hm, %Hsz⟩
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := w64) (fun keys (i : Int) => iprop(
      ⌜0 ≤ i⌝ ∗ ∃ (bb : GoSlice) (xs : GoString) (ys : w64), b_ptr ↦ bb ∗ x_ptr ↦ xs ∗ y_ptr ↦ ys ∗
        bb ↦* (bs ++ u64Le (W64 (GMap.size req)) ++
          ((reqEntries req (keys.take i.toNat)).map fun e => encStr e.1 ++ encU64 e.2).flatten) ∗
        ownSliceCap w8 bb (DFrac.own 1)))) $$ Hm
  iintro %keys %hkeys
  isplitl [b x y Hb Hcap]
  · isplitr
    · ipureintro; omega
    iexists b1, _, _
    simp only [Int.toNat_zero, List.take_zero, reqEntries, List.map_nil, List.flatten_nil,
      List.append_nil]
    iframe
  isplitl []
  · imodintro
    iintro %i %key %v ⟨%hk1, %hk2⟩ ⟨%hi, %bb, %xs, %ys, Hbp, Hx, Hy, Hb, Hcap⟩
    wp_auto
    wp_apply wp_rpcEnc_t5 key _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩
    wp_apply wp_rpcEnc_t6 v _ _ $$ [$Hb $Hcap] as %b3 ⟨Hb, Hcap, -⟩
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; omega
    iexists b3, key, v
    have hv : reqVer req key = v := by
      unfold reqVer; rw [show req.lookup key = req !! key from rfl, hk2]; rfl
    rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, hk1]
    simp only [reqEntries, Option.toList_some, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, hv,
      ← List.append_assoc]
    unfold encU64
    iframe
  · iintro ⟨%h0, %bb, %xs, %ys, Hbp, Hx, Hy, Hb, Hcap⟩ Hm
    wp_auto
    iapply HΦ
    iexists reqEntries req keys
    rw [← hkeys.2.1, List.take_of_length_le (by omega)]
    simp only [reqEntries, List.length_map]
    unfold encU64
    iframe
    ipureintro
    refine ⟨by rw [List.map_map]; exact (List.map_id' keys ▸ hkeys.2.2 : _), fun k v => ?_⟩
    constructor
    · intro h
      exact List.mem_map.2 ⟨k, (hkeys.1 k).2 (by
        rw [show req !! k = req.lookup k from rfl, h]; rfl), by
          simp [reqVer, h]⟩
    · intro h
      obtain ⟨k', hk', he⟩ := List.mem_map.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := (hkeys.1 k').1 hk'
      unfold reqVer
      rw [show req !! k' = req.lookup k' from rfl] at this
      cases h' : req.lookup k' <;> simp_all

theorem enc_EmptyArgs : enc_EmptyArgs.spec (GF := GF) := by
  intro p dq Ψ
  iintro ⟨Hp, HΨ⟩
  unfold craqCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t22 _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encEmptyArgs, tagged] at HΨ
  iapply HΨ $$ Hp

theorem enc_NodeMeta : enc_NodeMeta.spec (GF := GF) := by
  intro p dq m Ψ
  unfold metaPtr
  iintro ⟨Hp, HΨ⟩
  unfold craqCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t28 m _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encMeta, tagged] at HΨ
  iapply HΨ $$ Hp

theorem enc_CommitArgs : enc_CommitArgs.spec (GF := GF) := by
  intro p dq k v Ψ
  iintro ⟨Hp, HΨ⟩
  unfold craqCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t18 k v _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encCommitArgs, tagged] at HΨ
  iapply HΨ $$ Hp

theorem enc_WriteArgs : enc_WriteArgs.spec (GF := GF) := by
  intro p dq k sl dqs x v Ψ
  iintro ⟨Hp, Hsl, HΨ⟩
  unfold craqCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t31 k sl dqs x v _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, Hsl⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encWriteArgs, tagged] at HΨ
  iapply HΨ $$ Hp Hsl

theorem enc_ClientWriteArgs : enc_ClientWriteArgs.spec (GF := GF) := by
  intro p dq k sl dqs x Ψ
  iintro ⟨Hp, Hsl, HΨ⟩
  unfold craqCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t14 k sl dqs x _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, Hsl⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encClientWriteArgs, tagged] at HΨ
  iapply HΨ $$ Hp Hsl

theorem enc_string : enc_string.spec (GF := GF) := by
  intro s Ψ
  iintro HΨ
  unfold craqCodec
  iintro %Φ HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t5 s _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encString, tagged] at HΨ
  iexact HΨ

theorem enc_PropagateRequest : enc_PropagateRequest.spec (GF := GF) := by
  intro p dq req Ψ
  unfold reqPtr
  iintro ⟨⟨%mp, Hp, Hm⟩, HΨ⟩
  unfold craqCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t4 mp dq req $$ [$Hb $Hcap $Hm] as %b' ⟨%es, %Hes, Hb, Hcap, Hm⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  iapply HΨ $$ [Hp Hm]
  · iexists mp
    iframe
  ipureintro
  refine ⟨es, Hes, ?_⟩
  simp only [encPropReqL, tagged, encU64, List.append_assoc]

/-! ## Decoding -/

/-- A suffix of a slice, with the way back to the whole. -/
theorem ownSlice_suffix (k : w64) (s : GoSlice) (dq : DFrac) (vs : List w8)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.len) :
    (s ↦*{dq} vs : IProp GF) ⊢
      slice.slice s w8 k s.len ↦*{dq} vs.drop (sint.nat k) ∗
      (slice.slice s w8 k s.len ↦*{dq} vs.drop (sint.nat k) -∗ s ↦*{dq} vs) := by
  iintro Hs
  ihave Hs := (ownSlice_trivial_slice s dq vs).1 $$ Hs
  icases (ownSlice_split k s dq vs (W64 0) s.len ⟨by decide, hk.1, hk.2⟩).1 $$ Hs with ⟨Hp, Hs⟩
  have h0 : sint.nat k - sint.nat (W64 0) = sint.nat k := by
    rw [show sint.nat (W64 0) = 0 from rfl]; omega
  rw [h0]
  iframe Hs
  iintro Hs
  iapply (ownSlice_trivial_slice s dq vs).2
  iapply (ownSlice_split k s dq vs (W64 0) s.len ⟨by decide, hk.1, hk.2⟩).2
  rw [h0]
  iframe

theorem wp_rpcGetU64 (b : GoSlice) (bs : List w8) (dq : DFrac) (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (x : w64) (r : GoSlice) (ok : Bool),
        (match getU64 bs with
          | some (x', rest) => ⌜ok = true ∧ x = x'⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV (PairV #x #r) #ok)) -∗
    WP (App (Val (@! examples.craqnet.rpcGetU64)) (Val #b)) {{ Φ }} := by
  iintro Hb HΦ
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_func_call
  wp_call
  wp_auto
  have hlenZ : (bs.length : Int) = sint.Z b.len := by
    rw [Hl.1]; show ((sint.Z b.len).toNat : Int) = _; exact Int.toNat_of_nonneg Hl.2
  by_cases h8 : bs.length < 8
  · rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 8) by
      rw [show sint.Z (W64 8) = 8 from rfl]; omega)]
    wp_auto
    iapply HΦ
    unfold getU64
    rw [ite_eq_right (by omega)]
    dsimp only
    iframe
    ipureintro; rfl
  · have hb8 : 8 ≤ sint.Z b.len := by omega
    rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 8) by
      rw [show sint.Z (W64 8) = 8 from rfl]; omega)]
    rcases bs with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      try (simp at h8; done)
    wp_auto
    iterate 8
      rw [ite_eq_left (show _ ∧ _ by constructor <;> word)]
      wp_apply wp_load_slice_index b _ _ dq _ (by decide) $$ [Hb] with Hb
      · iframe; ipureintro; rfl
      (try wp_auto)
    have hcap : sint.Z b.len ≤ sint.Z b.cap := Hwf.2
    rw [ite_eq_left ⟨by decide, by rw [show sint.Z (W64 8) = 8 from rfl]; omega, hcap⟩]
    wp_auto
    icases ownSlice_suffix (W64 8) b dq _ ⟨by decide, by rw [show sint.Z (W64 8) = 8 from rfl]; omega⟩
      $$ Hb with ⟨Hr, Hback⟩
    iapply HΦ
    simp only [getU64, List.length_cons, show 8 ≤ rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      ite_true, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      encoding.binary.leToU64_8]
    iframe
    ipureintro; simp

end proof

end github_com.despreston.go_craq
end Perennial
