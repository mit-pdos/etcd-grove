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

theorem wp_rpcGetTag (b : GoSlice) (bs : List w8) (dq : DFrac) (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (t : GoString) (r : GoSlice) (ok : Bool),
        (match getTag bs with
          | some (t', rest) => ⌜ok = true ∧ t = t'⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV (PairV #t #r) #ok)) -∗
    WP (App (Val (@! examples.craqnet.rpcGetTag)) (Val #b)) {{ Φ }} := by
  iintro Hb HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold getTag
  rcases hg : getU64 bs with _ | ⟨n, rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hb⟩
    subst Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    ihave %Hl := ownSlice_len _ _ _ $$ Hr
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hr
    wp_auto
    by_cases hn : uint.nat x ≤ rest.length
    · rw [decide_eq_false (show ¬ uint.Z r.len < uint.Z x by word)]
      have hk : 0 ≤ sint.Z x ∧ sint.Z x ≤ sint.Z r.len := by word
      have hxn : sint.nat x = uint.nat x := by word
      wp_auto
      rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z x ∧ sint.Z x ≤ sint.Z r.cap
        from ⟨by decide, hk.1, by omega⟩)]
      icases (ownSlice_split_all x r dq rest hk).1 $$ Hr with ⟨Ht, Hd⟩
      wp_apply wp_bytes_to_string _ _ _ $$ Ht as Ht
      rw [if_pos (show 0 ≤ sint.Z x ∧ sint.Z x ≤ sint.Z r.len ∧ sint.Z r.len ≤ sint.Z r.cap
        from ⟨hk.1, hk.2, by omega⟩)]
      wp_auto
      iapply HΦ
      rw [if_pos hn]
      dsimp only
      rw [hxn] at *
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iintro Hd
      iapply Hback
      iapply (ownSlice_split_all x r dq rest hk).2
      rw [show sint.nat x = uint.nat x by word]
      iframe
    · rw [decide_eq_true (show uint.Z r.len < uint.Z x by word)]
      wp_auto
      iapply HΦ
      rw [if_neg hn]
      dsimp only
      isplitr
      · ipureintro; rfl
      iapply Hback $$ Hr

theorem wp_rpcDec_t5 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (s0 : GoString)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ s0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match getTag bs with
          | some (s, rest) => ⌜ok = true⌝ ∗ p ↦ s ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ s0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t5)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold getTag
  rcases hg : getU64 bs with _ | ⟨n, rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hb⟩
    subst Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    ihave %Hl := ownSlice_len _ _ _ $$ Hr
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hr
    wp_auto
    by_cases hn : uint.nat x ≤ rest.length
    · rw [decide_eq_false (show ¬ uint.Z r.len < uint.Z x by word)]
      have hk : 0 ≤ sint.Z x ∧ sint.Z x ≤ sint.Z r.len := by word
      have hxn : sint.nat x = uint.nat x := by word
      wp_auto
      rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z x ∧ sint.Z x ≤ sint.Z r.cap
        from ⟨by decide, hk.1, by omega⟩)]
      icases (ownSlice_split_all x r dq rest hk).1 $$ Hr with ⟨Ht, Hd⟩
      wp_apply wp_bytes_to_string _ _ _ $$ Ht as Ht
      (try wp_auto)
      rw [if_pos (show 0 ≤ sint.Z x ∧ sint.Z x ≤ sint.Z r.len ∧ sint.Z r.len ≤ sint.Z r.cap
        from ⟨hk.1, hk.2, by omega⟩)]
      wp_auto
      iapply HΦ
      rw [if_pos hn]
      dsimp only
      rw [hxn] at *
      iframe
      isplitr
      · ipureintro; rfl
      iintro Hd
      iapply Hback
      iapply (ownSlice_split_all x r dq rest hk).2
      rw [show sint.nat x = uint.nat x by word]
      iframe
    · rw [decide_eq_true (show uint.Z r.len < uint.Z x by word)]
      wp_auto
      iapply HΦ
      rw [if_neg hn]
      dsimp only
      iframe
      isplitr
      · ipureintro; rfl
      iapply Hback $$ Hr

theorem wp_rpcDec_t6 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : w64)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match getU64 bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t6)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  rcases hg : getU64 bs with _ | ⟨n, rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hb⟩
    subst Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl

/-- The pure `rpcDec_t29`. -/
def decBool (bs : List w8) : Option (Bool × List w8) :=
  match bs with
  | [] => none
  | c :: r => if 1 < uint.Z c then none else some (decide (c = W8 1), r)

theorem wp_rpcDec_t29 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : Bool)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decBool bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t29)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_func_call
  wp_call
  wp_auto
  rcases bs with _ | ⟨c, rest⟩
  · rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 1) by simp at Hl; word)]
    wp_auto
    iapply HΦ
    simp only [decBool]
    iframe
  · have hlen : sint.Z b.len = rest.length + 1 := by
      have := Hl.1; simp only [List.length_cons] at this
      have h2 : ((sint.Z b.len).toNat : Int) = sint.Z b.len := Int.toNat_of_nonneg Hl.2
      rw [show sint.nat b.len = (sint.Z b.len).toNat from rfl] at this; omega
    rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 1) by
      rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
    wp_auto
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len by
      rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
    wp_apply wp_load_slice_index b _ _ dq _ (by decide) $$ [Hb] with Hb
    · iframe; ipureintro; rfl
    by_cases hc : 1 < uint.Z c
    · rw [decide_eq_true (show uint.Z (W8 1) < uint.Z c from hc)]
      wp_auto
      iapply HΦ
      simp only [decBool, if_pos hc]
      iframe
    · rw [decide_eq_false (show ¬ uint.Z (W8 1) < uint.Z c from hc)]
      wp_auto
      rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len by
        rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
      wp_apply wp_load_slice_index b _ _ dq _ (by decide) $$ [Hb] with Hb
      · iframe; ipureintro; rfl
      wp_auto
      rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap by
        rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
      wp_auto
      icases ownSlice_suffix (W64 1) b dq _ ⟨by decide, by rw [show sint.Z (W64 1) = 1 from rfl]; omega⟩
        $$ Hb with ⟨Hr, Hback⟩
      iapply HΦ
      simp only [decBool, if_neg hc, show sint.nat (W64 1) = 1 from rfl, List.drop_succ_cons,
        List.drop_zero]
      iframe

/-- A struct's header byte (`1`). -/
def decHdr (bs : List w8) : Option (List w8) :=
  match bs with
  | [] => none
  | c :: r => if c = W8 1 then some r else none

/-- A struct field: `0` (not sent: the field keeps `v0`) or `1` and the value (`d`). -/
def decFld {α : Type} (d : List w8 → Option (α × List w8)) (v0 : α) (bs : List w8) :
    Option (α × List w8) :=
  match bs with
  | [] => none
  | c :: r => if 1 < uint.Z c then none else if c = W8 1 then d r else some (v0, r)

theorem wp_rpcDec_t16 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decHdr bs with
          | some rest => ⌜ok = true⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t16)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb HΦ
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_func_call
  wp_call
  wp_auto
  rcases bs with _ | ⟨c, rest⟩
  · rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 1) by simp at Hl; word)]
    wp_auto
    iapply HΦ
    simp only [decHdr]
    iframe
  · have hlen : sint.Z b.len = rest.length + 1 := by
      have := Hl.1; simp only [List.length_cons] at this
      have h2 : ((sint.Z b.len).toNat : Int) = sint.Z b.len := Int.toNat_of_nonneg Hl.2
      rw [show sint.nat b.len = (sint.Z b.len).toNat from rfl] at this; omega
    rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 1) by
      rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
    wp_auto
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len by
      rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
    wp_apply wp_load_slice_index b _ _ dq _ (by decide) $$ [Hb] with Hb
    · iframe; ipureintro; rfl
    by_cases hc : c = W8 1
    · simp only [hc, decide_true, Bool.not_true]
      wp_auto
      rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap by
        rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
      wp_auto
      icases ownSlice_suffix (W64 1) b dq _ ⟨by decide, by rw [show sint.Z (W64 1) = 1 from rfl]; omega⟩
        $$ Hb with ⟨Hr, Hback⟩
      iapply HΦ
      simp only [decHdr, hc, ↓reduceIte, show sint.nat (W64 1) = 1 from rfl, List.drop_succ_cons,
        List.drop_zero]
      iframe
    · simp only [hc, decide_false, Bool.not_false]
      wp_auto
      iapply HΦ
      simp only [decHdr, if_neg hc]
      iframe

theorem wp_rpcErrDecode (Φ : val → IProp GF) :
    ▷ (∀ e : GoInterface, net.rpc.decErr e -∗ Φ #e) -∗
    WP (App (Val (@! examples.craqnet.rpcErrDecode)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply net.rpc.wp_errors_New' as %x #HN
  iapply HΦ
  unfold net.rpc.decErr
  iexists x, go!"net/rpc model: malformed value"
  isplitr
  · ipureintro
    exact ⟨rfl, by simp⟩
  iexact HN

theorem decErr_ne_nil (e : GoInterface) : net.rpc.decErr (GF := GF) e ⊢ ⌜e ≠ interface.nil⌝ := by
  unfold net.rpc.decErr
  iintro ⟨%x, %msg, %Hp, -⟩
  ipureintro
  rw [Hp.1]
  nofun

set_option hygiene false in
/-- A decoding failure: `rpcErrDecode()`, with `Hd` (the data back) and `HΨ0 : Ψ false`. -/
macro "dec_fail" : tactic => `(tactic| (
  wp_apply wp_rpcErrDecode
  iintro %e #He
  wp_auto
  ihave %Hne := decErr_ne_nil e $$ He
  iapply HΦ $$ %e %false Hd %(Iff.intro (fun h => absurd h Hne) nofun) HΨ0
  simp only [Bool.false_eq_true, ite_false]
  iexact He))

theorem dec_EmptyReply : dec_EmptyReply.spec (GF := GF) := by
  intro p rep Ψ
  iintro ⟨%Htag, Hp, HΨ⟩
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data rep dq $$ Hd
  iintro %t %r %ok H
  rcases hg : getTag rep with _ | ⟨t', rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hd⟩
    subst Hok
    wp_auto
    ihave HΨ0 := HΨ $$ %false Hp
    dec_fail
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    have ht := Htag _ _ hg
    subst ht
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDec_t16 r rest dq p $$ Hr
    iintro %r2 %ok2 H2
    rcases hd : decHdr rest with _ | rest2
    · simp only [hd]
      icases H2 with ⟨%Hok, Hr⟩
      subst Hok
      wp_auto
      ihave Hd := Hback $$ Hr
      ihave HΨ0 := HΨ $$ %false Hp
      dec_fail
    · simp only [hd]
      icases H2 with ⟨%Hok, Hr2, Hback2⟩
      subst Hok
      ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
      wp_auto
      ihave Hd := Hback $$ [Hback2 Hr2]
      · iapply Hback2 $$ Hr2
      by_cases h0 : rest2 = []
      · subst h0
        rw [show r2.len = W64 0 by simp at Hl2; word]
        wp_auto
        iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
        · iapply HΨ $$ Hp
        simp only [ite_true]
        ipureintro; trivial
      · rw [decide_eq_false (show ¬ r2.len = W64 0 by
          intro h; rw [h] at Hl2; exact h0 (List.eq_nil_of_length_eq_zero (Hl2.1.trans (by rfl))))]
        wp_auto
        ihave HΨ0 := HΨ $$ %false Hp
        dec_fail

/-- A slice's length and capacity, as integers. -/
theorem ownSlice_lenZ (r : GoSlice) (dq : DFrac) (vs : List w8) :
    (r ↦*{dq} vs : IProp GF) ⊢ ⌜sint.Z r.len = vs.length ∧ sint.Z r.len ≤ sint.Z r.cap⌝ := by
  iintro Hr
  ihave %Hl := ownSlice_len _ _ _ $$ Hr
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hr
  ipureintro
  refine ⟨?_, Hwf.2⟩
  have h2 : ((sint.Z r.len).toNat : Int) = sint.Z r.len := Int.toNat_of_nonneg Hl.2
  rw [Hl.1, show sint.nat r.len = (sint.Z r.len).toNat from rfl, h2]

/-- `r[1:]` of a non-empty slice, as a new slice, with the way back. -/
theorem ownSlice_tail (r : GoSlice) (dq : DFrac) (c : w8) (cs : List w8) :
    (r ↦*{dq} (c :: cs) : IProp GF) ⊢ ∃ r' : GoSlice, ⌜slice.slice r w8 (W64 1) r.len = r'⌝ ∗
      ⌜sint.Z r'.len = cs.length ∧ sint.Z r'.len ≤ sint.Z r'.cap⌝ ∗
      r' ↦*{dq} cs ∗ (r' ↦*{dq} cs -∗ r ↦*{dq} (c :: cs)) := by
  iintro Hr
  ihave %Hl := ownSlice_lenZ _ _ _ $$ Hr
  simp only [List.length_cons] at Hl
  icases ownSlice_suffix (W64 1) r dq _ ⟨by decide, by rw [show sint.Z (W64 1) = 1 from rfl]; omega⟩
    $$ Hr with ⟨Hr, Hback⟩
  simp only [show sint.nat (W64 1) = 1 from rfl, List.drop_succ_cons, List.drop_zero]
  ihave %Hl' := ownSlice_lenZ _ _ _ $$ Hr
  iexists _
  iframe
  ipureintro
  exact ⟨rfl, Hl'⟩

theorem wand_trans (P Q R : IProp GF) : (P -∗ Q) ⊢ (Q -∗ R) -∗ (P -∗ R) := by
  iintro H1 H2 H
  iapply H2
  iapply H1 $$ H

set_option hygiene false in
/-- One field of a struct decoder: the state is `Hr : R ↦*{dq} cur`, `Hback` (back to `b`),
`hlR` (`R`'s length); `L` decodes the field into `F` (pure decoder `D`); `ft` closes a failure
(with `Hb : b ↦*{dq} bs`). -/
macro "fld_step " L:term:max D:term:max F:ident " fail " ft:tacticSeq : tactic => `(tactic| (
  rcases cur with _ | ⟨c, cur⟩
  · rw [decide_eq_true (show sint.Z R.len < sint.Z (W64 1) by
      rw [show sint.Z (W64 1) = 1 from rfl]; simp only [List.length_nil] at hlR; omega)]
    wp_auto
    ihave Hb := Hback $$ Hr
    ($ft)
  rw [decide_eq_false (show ¬ sint.Z R.len < sint.Z (W64 1) by
    rw [show sint.Z (W64 1) = 1 from rfl]; simp only [List.length_cons] at hlR; omega)]
  wp_auto
  rw [if_pos]
  case hc => rw [show sint.Z (W64 0) = 0 from rfl]; simp only [List.length_cons] at hlR; omega
  wp_apply wp_load_slice_index R _ _ dq _ (by decide) $$ [Hr] with Hr
  · iframe; ipureintro; rfl
  by_cases h1 : 1 < uint.Z c
  · rw [decide_eq_true (show uint.Z (W8 1) < uint.Z c from h1)]
    wp_auto
    ihave Hb := Hback $$ Hr
    ($ft)
  rw [decide_eq_false (show ¬ uint.Z (W8 1) < uint.Z c from h1)]
  wp_auto
  rw [if_pos]
  case hc => rw [show sint.Z (W64 0) = 0 from rfl]; simp only [List.length_cons] at hlR; omega
  wp_apply wp_load_slice_index R _ _ dq _ (by decide) $$ [Hr] with Hr
  · iframe; ipureintro; rfl
  by_cases h2 : c = W8 1
  subst h2
  simp only [_root_.decide_true]
  wp_auto
  rw [if_pos]
  case hc => rw [show sint.Z (W64 1) = 1 from rfl]; simp only [List.length_cons] at hlR; omega
  icases ownSlice_tail R dq _ _ $$ Hr with ⟨%R1, %HR1, %hlR1, Hr, HbackT⟩
  rw [HR1]
  wp_auto
  wp_apply ($L R1 cur dq _ _) $$ Hr $F:ident
  iintro %R %okd Hd2
  rcases hd : $D cur with _ | ⟨v, cur⟩
  · simp only [hd]
    icases Hd2 with ⟨%Hok, $F:ident, Hr⟩
    subst Hok
    wp_auto
    ihave Hb := Hback $$ [HbackT Hr]
    · iapply HbackT $$ Hr
    ($ft)
  simp only [hd]
  icases Hd2 with ⟨%Hok, $F:ident, Hr, Hback2⟩
  subst Hok
  wp_auto
  ihave %hlR := ownSlice_lenZ _ _ _ $$ Hr
  ihave HbackT := wand_trans _ _ _ $$ Hback2 HbackT
  ihave Hback := wand_trans _ _ _ $$ HbackT Hback
  rotate_left
  simp only [h2, decide_false]
  wp_auto
  rw [if_pos]
  case hc => rw [show sint.Z (W64 1) = 1 from rfl]; simp only [List.length_cons] at hlR; omega
  icases ownSlice_tail R dq _ _ $$ Hr with ⟨%R, %HR1, %hlR, Hr, HbackT⟩
  rw [HR1]
  wp_auto
  ihave Hback := wand_trans _ _ _ $$ HbackT Hback))

set_option hygiene false in
/-- Close a struct decoder's proof: the pure decoder `D` computed, the struct put back together. -/
macro "struct_close " D:ident : tactic => `(tactic| (
  iapply HΦ
  simp only [$D:ident, decHdr, decFld, ↓reduceIte, *]
  iframe
  (try first | iexists _, _, _, _, _ | iexists _, _)
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe))

set_option hygiene false in
/-- A struct decoder's header byte, after `iStructNamed`: leaves `Hr : R ↦*{dq} cur`, `Hback`,
`hlR`. -/
macro "hdr_step " D:ident : tactic => `(tactic| (
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_func_call
  wp_call
  wp_auto
  rcases bs with _ | ⟨c, rest⟩
  · rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 1) by simp at Hl; word)]
    wp_auto
    struct_close $D:ident
  have hlen : sint.Z b.len = rest.length + 1 := by
    have := Hl.1; simp only [List.length_cons] at this
    have h2 : ((sint.Z b.len).toNat : Int) = sint.Z b.len := Int.toNat_of_nonneg Hl.2
    rw [show sint.nat b.len = (sint.Z b.len).toNat from rfl] at this; omega
  rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 1) by
    rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
  wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
  wp_apply wp_load_slice_index b _ _ dq _ (by decide) $$ [Hb] with Hb
  · iframe; ipureintro; rfl
  by_cases hc : c = W8 1
  rotate_left
  · simp only [hc, decide_false, Bool.not_false]
    wp_auto
    struct_close $D:ident
  subst hc
  simp only [_root_.decide_true, Bool.not_true]
  wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap by
    rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
  icases ownSlice_tail b dq _ _ $$ Hb with ⟨%R, %HR, %hlR, Hr, Hback⟩
  rw [HR]
  wp_auto
  generalize hcur : rest = cur at *
  clear hcur))

/-- The pure `rpcDec_t20` (`VersionResponse`), into `{k0, v0}`. -/
def decVR (k0 : GoString) (v0 : w64) (bs : List w8) : Option ((GoString × w64) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld getTag k0 r with
    | none => none
    | some (k, r) =>
      match decFld getU64 v0 r with
      | none => none
      | some (v, r) => some ((k, v), r)

theorem wp_rpcDec_t20 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (k0 : GoString) (v0 : w64)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ transport.netrpc.VersionResponse.mk k0 v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decVR k0 v0 bs with
          | some ((k, v), rest) => ⌜ok = true⌝ ∗ p ↦ transport.netrpc.VersionResponse.mk k v ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ k v, p ↦ transport.netrpc.VersionResponse.mk k v) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t20)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decVR
  all_goals fld_step wp_rpcDec_t5 getTag Key fail struct_close decVR
  all_goals fld_step wp_rpcDec_t6 getU64 Version fail struct_close decVR
  all_goals ((try wp_auto); struct_close decVR)

/-! ### Round trips -/

/-- `getU64_enc` without the codec section's instances. -/
theorem getU64_enc' (x : w64) (rest : List w8) : getU64 (u64Le x ++ rest) = some (x, rest) := by
  unfold getU64
  rw [ite_eq_left (by simp [u64Le_length])]
  have h8 := u64Le_length x
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
    u64Le_to_word]

/-- `getTag_encStr` without the codec section's instances. -/
theorem getTag_encStr' (s : GoString) (rest : List w8) (hs : s.length < 2 ^ 64) :
    getTag (encStr s ++ rest) = some (s, rest) := by
  unfold getTag encStr
  rw [List.append_assoc, getU64_enc']
  have hn : uint.nat (W64 s.length) = s.length := by
    show (BitVec.ofNat 64 s.length).toNat = s.length
    simp only [BitVec.toNat_ofNat]; omega
  simp only [hn, List.length_append, Nat.le_add_right, ite_true, List.take_left', List.drop_left']

theorem decFld_fld {α : Type} (d : List w8 → Option (α × List w8)) (v0 v : α) (sent : Bool)
    (body rest : List w8) (h0 : sent = false → v = v0)
    (h1 : sent = true → d (body ++ rest) = some (v, rest)) :
    decFld d v0 (fld sent body ++ rest) = some (v, rest) := by
  cases sent
  · simp only [fld, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, decFld]
    rw [h0 rfl]
    simp [show uint.Z (W8 0) = 0 from rfl, show (W8 0 = W8 1) = False by decide]
    decide
  · simp only [fld, ↓reduceIte, List.cons_append, decFld]
    simp [show uint.Z (W8 1) = 1 from rfl, h1 rfl]
    decide

theorem decFld_fStr (k rest : List w8) (hk : k.length < 2 ^ 64) :
    decFld getTag go!"" (fStr k ++ rest) = some (k, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact getTag_encStr' k rest hk

theorem decFld_fU64 (v : w64) (rest : List w8) :
    decFld getU64 (W64 0) (fU64 v ++ rest) = some (v, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact getU64_enc' v rest

theorem decVR_enc (k : GoString) (v : w64) (hk : k.length < 2 ^ 64) :
    decVR go!"" (W64 0) (strct [fStr k, fU64 v]) = some ((k, v), []) := by
  have e : strct [fStr k, fU64 v] = W8 1 :: (fStr k ++ (fU64 v ++ [])) := by
    simp [strct]
  rw [e]
  simp only [decVR, decHdr, ↓reduceIte, decFld_fStr k _ hk, decFld_fU64]

theorem dec_VersionResponse : dec_VersionResponse.spec (GF := GF) := by
  intro p rep Ψ
  iintro ⟨%Htag, Hp, HΨ⟩
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data rep dq $$ Hd
  iintro %t %r %ok H
  rcases hg : getTag rep with _ | ⟨t', rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hd⟩
    subst Hok
    wp_auto
    ihave HΨ0 := HΨ $$ %false [Hp]
    · simp only [Bool.false_eq_true, ite_false]; iexists _, _; iexact Hp
    dec_fail
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    have ht := Htag _ _ hg
    subst ht
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDec_t20 r rest dq p _ _ $$ Hr Hp
    iintro %r2 %ok2 H2
    rcases hd : decVR go!"" (W64 0) rest with _ | ⟨⟨k, v⟩, rest2⟩
    · simp only [hd]
      icases H2 with ⟨%Hok, Hp, Hr⟩
      subst Hok
      wp_auto
      ihave Hd := Hback $$ Hr
      ihave HΨ0 := HΨ $$ %false [Hp]
      · simp only [Bool.false_eq_true, ite_false]; iexact Hp
      dec_fail
    · simp only [hd]
      icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
      subst Hok
      ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
      wp_auto
      ihave Hd := Hback $$ [Hback2 Hr2]
      · iapply Hback2 $$ Hr2
      by_cases h0 : rest2 = []
      · subst h0
        rw [show r2.len = W64 0 by simp at Hl2; word]
        wp_auto
        iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
        · iapply HΨ
          simp only [ite_true]
          iexists k, v
          iframe
          ipureintro
          intro k' v' he
          subst he
          have hk : k'.length < 2 ^ 64 := by
            have h1 : k'.length ≤ (fStr k').length := by
              by_cases hk : k' = []
              · simp [hk]
              · simp [fStr, fld, hk, encStr]; omega
            have h2 : (fStr k').length ≤ (encVersionResp k' v').length := by
              simp [encVersionResp, tagged, strct]; omega
            have h3 : sint.Z data.len < 2 ^ 63 := by word
            omega
          rw [encVersionResp, tagged, getTag_encStr' _ _ (by decide)] at hg
          cases hg
          rw [decVR_enc k' v' hk] at hd
          cases hd
          exact ⟨rfl, rfl⟩
        simp only [ite_true]
        ipureintro; trivial
      · rw [decide_eq_false (show ¬ r2.len = W64 0 by
          intro h; rw [h] at Hl2; exact h0 (List.eq_nil_of_length_eq_zero (Hl2.1.trans (by rfl))))]
        wp_auto
        ihave HΨ0 := HΨ $$ %false [Hp]
        · simp only [Bool.false_eq_true, ite_false]; iexists _, _; iexact Hp
        dec_fail

/-- The pure `rpcDec_t28` (`NodeMeta`): what is left after it (the values are not needed). -/
def decMeta (bs : List w8) : Option (List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld decBool false r with
    | none => none
    | some (_, r) =>
      match decFld decBool false r with
      | none => none
      | some (_, r) =>
        match decFld getTag go!"" r with
        | none => none
        | some (_, r) =>
          match decFld getTag go!"" r with
          | none => none
          | some (_, r) =>
            match decFld getTag go!"" r with
            | none => none
            | some (_, r) => some r

set_option maxHeartbeats 4000000 in
theorem wp_rpcDec_t28 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (m : MetaV)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ transport.NodeMeta.mk m.isHead m.isTail m.prev m.next m.tail -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decMeta bs with
          | some rest => ⌜ok = true⌝ ∗ (∃ h t pr nx tl, p ↦ transport.NodeMeta.mk h t pr nx tl) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ h t pr nx tl, p ↦ transport.NodeMeta.mk h t pr nx tl) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t28)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decMeta
  all_goals fld_step wp_rpcDec_t29 decBool IsHead fail struct_close decMeta
  all_goals fld_step wp_rpcDec_t29 decBool IsTail fail struct_close decMeta
  all_goals fld_step wp_rpcDec_t5 getTag Prev fail struct_close decMeta
  all_goals fld_step wp_rpcDec_t5 getTag Next fail struct_close decMeta
  all_goals fld_step wp_rpcDec_t5 getTag Tail fail struct_close decMeta
  all_goals ((try wp_auto); struct_close decMeta)

theorem dec_NodeMeta : dec_NodeMeta.spec (GF := GF) := by
  intro p rep Ψ
  unfold metaPtr
  iintro ⟨%Htag, Hp, HΨ⟩
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data rep dq $$ Hd
  iintro %t %r %ok H
  rcases hg : getTag rep with _ | ⟨t', rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hd⟩
    subst Hok
    wp_auto
    ihave HΨ0 := HΨ $$ %false [Hp]
    · iexists ⟨false, false, go!"", go!"", go!""⟩; iexact Hp
    dec_fail
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    have ht := Htag _ _ hg
    subst ht
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDec_t28 r rest dq p ⟨false, false, go!"", go!"", go!""⟩ $$ Hr Hp
    iintro %r2 %ok2 H2
    rcases hd : decMeta rest with _ | rest2
    · simp only [hd]
      icases H2 with ⟨%Hok, ⟨%h1, %h2, %h3, %h4, %h5, Hp⟩, Hr⟩
      subst Hok
      wp_auto
      ihave Hd := Hback $$ Hr
      ihave HΨ0 := HΨ $$ %false [Hp]
      · iexists ⟨h1, h2, h3, h4, h5⟩; iexact Hp
      dec_fail
    · simp only [hd]
      icases H2 with ⟨%Hok, ⟨%h1, %h2, %h3, %h4, %h5, Hp⟩, Hr2, Hback2⟩
      subst Hok
      ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
      wp_auto
      ihave Hd := Hback $$ [Hback2 Hr2]
      · iapply Hback2 $$ Hr2
      by_cases h0 : rest2 = []
      · subst h0
        ihave HΨ0 := HΨ $$ %true [Hp]
        · iexists ⟨h1, h2, h3, h4, h5⟩; iexact Hp
        rw [show r2.len = W64 0 by simp at Hl2; word]
        wp_auto
        iapply HΦ $$ %interface.nil %true Hd %(by simp) HΨ0
        simp only [ite_true]
        ipureintro; trivial
      · rw [decide_eq_false (show ¬ r2.len = W64 0 by
          intro h; rw [h] at Hl2; exact h0 (List.eq_nil_of_length_eq_zero (Hl2.1.trans (by rfl))))]
        wp_auto
        ihave HΨ0 := HΨ $$ %false [Hp]
        · iexists ⟨h1, h2, h3, h4, h5⟩; iexact Hp
        dec_fail

/-- The pure `rpcDec_t12` (`uint8`). -/
def decU8 (bs : List w8) : Option (w8 × List w8) :=
  match getU64 bs with
  | none => none
  | some (x, r) => if uint.Z x < 256 then some (W8 (uint.Z x), r) else none

theorem wp_rpcDec_t12 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : w8)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decU8 bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t12)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold decU8
  rcases hg : getU64 bs with _ | ⟨n, rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hb⟩
    subst Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    wp_auto
    by_cases hx : uint.Z x < 256
    · rw [decide_eq_true (show W64 (uint.Z (W8 (uint.Z x))) = x by word)]
      wp_auto
      iapply HΦ
      rw [if_pos hx]
      dsimp only
      iframe
      ipureintro; rfl
    · rw [decide_eq_false (show ¬ W64 (uint.Z (W8 (uint.Z x))) = x by
        intro h; apply hx; rw [← h]; word)]
      wp_auto
      iapply HΦ
      rw [if_neg hx]
      dsimp only
      iframe
      isplitr
      · ipureintro; rfl
      iapply Hback $$ Hr

/-- `k` more bytes (each a `uint64`), after `acc`. -/
def decU8sGo : Nat → List w8 → List w8 → Option (List w8 × List w8)
  | 0, acc, r => some (acc, r)
  | k + 1, acc, r =>
    match decU8 r with
    | none => none
    | some (x, r') => decU8sGo k (acc ++ [x]) r'

/-- The pure `rpcDec_t11` (`[]uint8`). -/
def decBytes (bs : List w8) : Option (List w8 × List w8) :=
  match getU64 bs with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then decU8sGo (uint.nat n) [] r else none

theorem wp_rpcDec_t11 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ slice.nil -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decBytes bs with
          | some (x, rest) => ⌜ok = true⌝ ∗ (∃ sl, p ↦ sl ∗ sl ↦* x) ∗ r ↦*{dq} rest ∗
              (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ sl : GoSlice, p ↦ sl) ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t11)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold decBytes
  rcases hg : getU64 bs with _ | ⟨n, rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hb⟩
    subst Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    ihave %Hl := ownSlice_lenZ _ _ _ $$ Hr
    wp_auto
    by_cases hn : uint.nat x ≤ rest.length
    rotate_left
    · rw [decide_eq_true (show uint.Z r.len < uint.Z x by word)]
      wp_auto
      iapply HΦ
      rw [if_neg hn]
      dsimp only
      iframe
      isplitr
      · ipureintro; rfl
      iapply Hback $$ Hr
    rw [decide_eq_false (show ¬ uint.Z r.len < uint.Z x by word)]
    wp_auto
    have hxs : sint.Z x = uint.Z x := by word
    rw [if_pos hn]
    by_cases hx0 : x = W64 0
    rw [decide_eq_false (by rw [hx0]; decide)]
    wp_auto
    rw [if_pos (by rw [hx0]; decide)]
    wp_auto
    ihave Hn := ownSlice_nil (V := w8) (DFrac.own 1)
    ihave Hs : (slice.slice slice.nil w8 (W64 0) x ↦* List.replicate (uint.nat x) (W8 0)) $$ [Hn]
    · subst hx0
      icases (ownSlice_slice (V := w8) (W64 0) (W64 0) slice.nil (DFrac.own 1) []
        ⟨by decide, by decide, by decide⟩).1 $$ Hn with ⟨-, Hs, -⟩
      have e : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) ([] : List w8) =
          List.replicate (uint.nat (W64 0)) (W8 0) := by simp [subslice]
      rw [e]
      iexact Hs
    generalize slice.slice slice.nil w8 (W64 0) x = sl at *
    iclear Hn
    rotate_left
    rw [decide_eq_true (show uint.Z (0 : w64) < uint.Z x by
      have : uint.Z x ≠ 0 := fun h => hx0 (by word)
      have : (0 : Int) ≤ uint.Z x := by word
      show (0 : Int) < uint.Z x
      omega)]
    wp_auto
    wp_apply wp_slice_make2 (V := w8) x
    · ipureintro; word
    iintro %sl ⟨Hs, -⟩
    rw [show sint.nat x = uint.nat x by word, show zero_val w8 = W8 0 from rfl]
    wp_auto
    rotate_left
    all_goals
      ihave %hsl := ownSlice_lenZ _ _ _ $$ Hs
      simp only [List.length_replicate] at hsl
      ihave HI : (∃ (i : w64) (R : GoSlice) (acc cur : List w8),
          "i" ∷ i_ptr ↦ i ∗ "r" ∷ r_ptr ↦ R ∗ "ok" ∷ ok_ptr ↦ true ∗ "Hr" ∷ R ↦*{dq} cur ∗
          "Hback" ∷ (R ↦*{dq} cur -∗ b ↦*{dq} bs) ∗
          "Hs" ∷ sl ↦* (acc ++ List.replicate (uint.nat x - uint.nat i) (W8 0)) ∗
          "%Hi" ∷ ⌜acc.length = uint.nat i ∧ uint.nat i ≤ uint.nat x ∧
            decU8sGo (uint.nat x - uint.nat i) acc cur = decU8sGo (uint.nat x) [] rest⌝ : IProp GF)
          $$ [i r ok Hr Hback Hs]
      · iexists W64 0, r, [], rest
        simp only [show uint.nat (W64 0) = 0 from rfl, Nat.sub_zero, List.nil_append]
        iframe
        ipureintro
        simp
      wp_for HI
      wp_if_destruct
      · have hi : uint.Z i < uint.Z x := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        have hk : uint.nat x - uint.nat i = (uint.nat x - uint.nat i - 1) + 1 := by word
        rw [if_pos (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len by word)]
        have hlk : (acc ++ List.replicate (uint.nat x - uint.nat i) (W8 0))[(sint.Z i).toNat]? =
            some (W8 0) := by
          rw [show (sint.Z i).toNat = acc.length by word, hk]
          simp
        icases ownSlice_elem_acc (sint.Z i) (W8 0) sl _ _ (by word) hlk $$ Hs with ⟨He, Hs⟩
        wp_apply wp_rpcDec_t12 R cur dq _ _ $$ Hr He
        iintro %R2 %ok2 Hd
        rcases hd : decU8 cur with _ | ⟨v, cur2⟩
        · simp only [hd]
          icases Hd with ⟨%Hok, He, Hr⟩
          subst Hok
          ihave Hs := Hs $$ He
          wp_auto
          rw [forPostcondition_unseal]; unfold forPostconditionDef; iright; iright; iright; ileft
          iexists #()
          isplitr
          · ipureintro; rfl
          dsimp only
          wp_auto
          have hres : decU8sGo (uint.nat x) [] rest = none := by
            rw [← Hi.2.2, hk]; simp [decU8sGo, hd]
          iapply HΦ
          rw [hres]
          dsimp only
          ihave Hb := Hback $$ Hr
          iframe
          ipureintro; rfl
        · simp only [hd]
          icases Hd with ⟨%Hok, He, Hr, Hback2⟩
          subst Hok
          ihave Hs := Hs $$ He
          wp_auto
          wp_for_post
          ihave Hback := wand_trans _ _ _ $$ Hback2 Hback
          have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
          have hset : (acc ++ List.replicate (uint.nat x - uint.nat i) (W8 0)).set (sint.Z i).toNat v =
              (acc ++ [v]) ++ List.replicate (uint.nat x - uint.nat (i + W64 1)) (W8 0) := by
            rw [show (sint.Z i).toNat = acc.length by word, hk, hi1,
              show uint.nat x - (uint.nat i + 1) = uint.nat x - uint.nat i - 1 by omega]
            simp [List.replicate_succ]
          rw [hset]
          iframe
          iexists i + W64 1, R2, acc ++ [v], cur2
          iframe
          ipureintro
          refine ⟨by rw [List.length_append, Hi.1, hi1]; rfl, by rw [hi1]; omega, ?_⟩
          rw [← Hi.2.2, hk, hi1, show uint.nat x - (uint.nat i + 1) = uint.nat x - uint.nat i - 1 by omega]
          simp [decU8sGo, hd]
      · (try wp_auto)
        have hix : uint.nat x - uint.nat i = 0 := by
          have : ¬ uint.Z i < uint.Z x := by
            first | exact Hif | exact fun h => Hif (by simp [h])
          word
        have hres : decU8sGo (uint.nat x) [] rest = some (acc, cur) := by
          rw [← Hi.2.2, hix]; rfl
        iapply HΦ
        rw [hres]
        dsimp only
        rw [hix, List.replicate_zero, List.append_nil]
        iframe
        ipureintro; rfl

/-- The pure `rpcDec_t24` (`Item`), into `{k0, nil}`. -/
def decItem (k0 : GoString) (bs : List w8) : Option ((GoString × List w8) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld getTag k0 r with
    | none => none
    | some (k, r) =>
      match decFld decBytes [] r with
      | none => none
      | some (x, r) => some ((k, x), r)

set_option hygiene false in
/-- Close an `Item` decoder's proof (the `Value` field in any of its states). -/
macro "item_close " D:ident : tactic => `(tactic| (
  iapply HΦ
  simp only [$D:ident, decHdr, decFld, ↓reduceIte, *]
  iframe
  first
  | (icases Value with ⟨%sl, Value, Hsl⟩
     iexists sl
     iframe Hsl
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists slice.nil
     ihave Hsl := ownSlice_nil (V := w8) (DFrac.own 1)
     iframe Hsl
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (icases Value with ⟨%sl, Value, -⟩
     iexists _, _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (icases Value with ⟨%sl, Value⟩
     iexists _, _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists _, _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)))

theorem wp_rpcDec_t24 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (k0 : GoString)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ transport.Item.mk k0 slice.nil -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decItem k0 bs with
          | some ((k, x), rest) => ⌜ok = true⌝ ∗ (∃ sl, p ↦ transport.Item.mk k sl ∗ sl ↦* x) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ k sl, p ↦ transport.Item.mk k sl) ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t24)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decItem
  all_goals fld_step wp_rpcDec_t5 getTag Key fail item_close decItem
  all_goals fld_step wp_rpcDec_t11 decBytes Value fail item_close decItem
  all_goals ((try wp_auto); item_close decItem)

theorem decU8_enc (c : w8) (rest : List w8) :
    decU8 (u64Le (W64 (uint.Z c)) ++ rest) = some (c, rest) := by
  unfold decU8
  rw [getU64_enc']
  have h1 : uint.Z (W64 (uint.Z c)) < 256 := by word
  have h2 : W8 (uint.Z (W64 (uint.Z c))) = c := by word
  simp only [h1, ↓reduceIte, h2]

theorem decU8sGo_enc (l acc rest : List w8) :
    decU8sGo l.length acc ((l.map fun c => u64Le (W64 (uint.Z c))).flatten ++ rest) =
      some (acc ++ l, rest) := by
  induction l generalizing acc with
  | nil => simp [decU8sGo]
  | cons c l ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decU8sGo,
      decU8_enc, ih]
    simp

theorem decBytes_enc (x rest : List w8) (hx : x.length < 2 ^ 64) :
    decBytes (encBytes x ++ rest) = some (x, rest) := by
  unfold decBytes encBytes
  rw [List.append_assoc, getU64_enc']
  have hn : uint.nat (W64 x.length) = x.length := by
    show (BitVec.ofNat 64 x.length).toNat = x.length
    simp only [BitVec.toNat_ofNat]; omega
  have hle : x.length ≤ ((x.map fun c => u64Le (W64 (uint.Z c))).flatten ++ rest).length := by
    have : ∀ l : List w8, l.length ≤ (l.map fun c => u64Le (W64 (uint.Z c))).flatten.length := by
      intro l
      induction l with
      | nil => simp
      | cons c l ih =>
        simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
          u64Le_length]; omega
    have := this x
    simp only [List.length_append]; omega
  simp only [hn, hle, ↓reduceIte, decU8sGo_enc, List.nil_append]

theorem decFld_fBytes (x rest : List w8) (hx : x.length < 2 ^ 64) :
    decFld decBytes [] (fBytes x ++ rest) = some (x, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact decBytes_enc x rest hx

theorem decItem_enc (k x : GoString) (hk : k.length < 2 ^ 64) (hx : x.length < 2 ^ 64) :
    decItem go!"" (strct [fStr k, fBytes x]) = some ((k, x), []) := by
  have e : strct [fStr k, fBytes x] = W8 1 :: (fStr k ++ (fBytes x ++ [])) := by
    simp [strct]
  rw [e]
  simp only [decItem, decHdr, ↓reduceIte, decFld_fStr k _ hk, decFld_fBytes x _ hx]

theorem dec_Item : dec_Item.spec (GF := GF) := by
  intro p rep Ψ
  iintro ⟨%Htag, Hp, HΨ⟩
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data rep dq $$ Hd
  iintro %t %r %ok H
  rcases hg : getTag rep with _ | ⟨t', rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hd⟩
    subst Hok
    wp_auto
    ihave HΨ0 := HΨ $$ %false [Hp]
    · simp only [Bool.false_eq_true, ite_false]; iexists _, _; iexact Hp
    dec_fail
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    have ht := Htag _ _ hg
    subst ht
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDec_t24 r rest dq p _ $$ Hr Hp
    iintro %r2 %ok2 H2
    rcases hd : decItem go!"" rest with _ | ⟨⟨k, x⟩, rest2⟩
    · simp only [hd]
      icases H2 with ⟨%Hok, Hp, Hr⟩
      subst Hok
      wp_auto
      ihave Hd := Hback $$ Hr
      ihave HΨ0 := HΨ $$ %false [Hp]
      · simp only [Bool.false_eq_true, ite_false]; iexact Hp
      dec_fail
    · simp only [hd]
      icases H2 with ⟨%Hok, ⟨%sl, Hp, Hsl⟩, Hr2, Hback2⟩
      subst Hok
      ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
      wp_auto
      ihave Hd := Hback $$ [Hback2 Hr2]
      · iapply Hback2 $$ Hr2
      by_cases h0 : rest2 = []
      · subst h0
        rw [show r2.len = W64 0 by simp at Hl2; word]
        wp_auto
        iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp Hsl]
        · iapply HΨ
          simp only [ite_true]
          iexists k, sl, x
          iframe
          ipureintro
          intro k' x' he
          subst he
          have h3 : sint.Z data.len < 2 ^ 63 := by word
          have hk : k'.length < 2 ^ 64 := by
            have h1 : k'.length ≤ (fStr k').length := by
              by_cases hk : k' = []
              · simp [hk]
              · simp [fStr, fld, hk, encStr]; omega
            have h2 : (fStr k').length ≤ (encItem k' x').length := by
              simp [encItem, tagged, strct]; omega
            omega
          have hx : x'.length < 2 ^ 64 := by
            have h1 : x'.length ≤ (fBytes x').length := by
              by_cases hx : x' = []
              · simp [hx]
              · have : ∀ l : List w8, l.length ≤
                    (l.map fun c => u64Le (W64 (uint.Z c))).flatten.length := by
                  intro l
                  induction l with
                  | nil => simp
                  | cons c l ih =>
                    simp only [List.map_cons, List.flatten_cons, List.length_append,
                      List.length_cons, u64Le_length]; omega
                have := this x'
                simp only [fBytes, fld, hx, decide_false, decide_true, ne_eq, not_false_eq_true,
                  ↓reduceIte, encBytes, List.length_cons, List.length_append]
                omega
            have h2 : (fBytes x').length ≤ (encItem k' x').length := by
              simp [encItem, tagged, strct]; omega
            omega
          rw [encItem, tagged, getTag_encStr' _ _ (by decide)] at hg
          cases hg
          rw [decItem_enc k' x' hk hx] at hd
          cases hd
          exact ⟨rfl, rfl⟩
        simp only [ite_true]
        ipureintro; trivial
      · rw [decide_eq_false (show ¬ r2.len = W64 0 by
          intro h; rw [h] at Hl2; exact h0 (List.eq_nil_of_length_eq_zero (Hl2.1.trans (by rfl))))]
        wp_auto
        ihave HΨ0 := HΨ $$ %false [Hp]
        · simp only [Bool.false_eq_true, ite_false]; iexists _, _; iexact Hp
        dec_fail

/-- The pure `rpcDec_t10` (`ValueVersion`), into `{nil, 0}`. -/
def decVV (bs : List w8) : Option ((List w8 × w64) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld decBytes [] r with
    | none => none
    | some (x, r) =>
      match decFld getU64 (W64 0) r with
      | none => none
      | some (v, r) => some ((x, v), r)

theorem wp_rpcDec_t10 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ transport.ValueVersion.mk slice.nil (W64 0) -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decVV bs with
          | some ((x, v), rest) => ⌜ok = true⌝ ∗ (∃ sl, p ↦ transport.ValueVersion.mk sl v ∗ sl ↦* x) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ sl v, p ↦ transport.ValueVersion.mk sl v) ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t10)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decVV
  all_goals fld_step wp_rpcDec_t11 decBytes Value fail item_close decVV
  all_goals fld_step wp_rpcDec_t6 getU64 Version fail item_close decVV
  all_goals ((try wp_auto); item_close decVV)


/-- The zero `ValueVersion`. -/
abbrev zVV : transport.ValueVersion := transport.ValueVersion.mk slice.nil (W64 0)

/-- `k` more `ValueVersion`s, after `acc`. -/
def decVVsGo : Nat → List (GoString × w64) → List w8 → Option (List (GoString × w64) × List w8)
  | 0, acc, r => some (acc, r)
  | k + 1, acc, r =>
    match decVV r with
    | none => none
    | some (e, r') => decVVsGo k (acc ++ [e]) r'

/-- The pure `rpcDec_t9` (`[]ValueVersion`). -/
def decVVs (bs : List w8) : Option (List (GoString × w64) × List w8) :=
  match getU64 bs with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then decVVsGo (uint.nat n) [] r else none

/-- The `i`th element `vv` of a decoded `[]ValueVersion` holds `xs`'s `i`th value. -/
def vvElem (xs : List (GoString × w64)) (i : Nat) (vv : transport.ValueVersion) : IProp GF :=
  iprop(∃ x, ⌜((xs[i]?).map Prod.fst) = some x⌝ ∗ vv.Value' ↦*□ x)

/-- `sl` holds the `[]ValueVersion` `xs` (as `respPtr` wants it). -/
def vvsOwn (sl : GoSlice) (xs : List (GoString × w64)) : IProp GF :=
  iprop(∃ (vvs : List transport.ValueVersion), sl ↦* vvs ∗
    ⌜vvs.map (·.Version') = xs.map Prod.snd⌝ ∗ [∗list] i ↦ vv ∈ vvs, vvElem xs i vv)

theorem vvElem_snoc (vvs : List transport.ValueVersion) (acc : List (GoString × w64)) (vsl : GoSlice)
    (xv : GoString) (v : w64) (h1 : vvs.length = n) (h2 : acc.length = n) :
    ([∗list] j ↦ vv ∈ vvs, vvElem (GF := GF) acc j vv) -∗ vsl ↦*□ xv -∗
      [∗list] j ↦ vv ∈ vvs ++ [transport.ValueVersion.mk vsl v], vvElem (acc ++ [(xv, v)]) j vv := by
  iintro HV #Hx
  iapply BigSepL.bigSepL_snoc.2
  isplitl [HV]
  · iapply (BigSepL.bigSepL_mono (Φ := fun j vv => vvElem (GF := GF) acc j vv) ?_) $$ HV
    intro j vv hj
    have hjl : j < acc.length := by
      have := (List.getElem?_eq_some_iff.1 hj).1; omega
    unfold vvElem
    rw [List.getElem?_append_left hjl]
  · unfold vvElem
    iexists xv
    isplitr
    · ipureintro
      rw [List.getElem?_append_right (by omega), show vvs.length - acc.length = 0 by omega]
      rfl
    iexact Hx

theorem wp_rpcDec_t9 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ slice.nil -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decVVs bs with
          | some (xs, rest) => ⌜ok = true⌝ ∗ (∃ sl, p ↦ sl ∗ vvsOwn sl xs) ∗ r ↦*{dq} rest ∗
              (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ sl : GoSlice, p ↦ sl) ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t9)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold decVVs
  rcases hg : getU64 bs with _ | ⟨n, rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hb⟩
    subst Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    ihave %Hl := ownSlice_lenZ _ _ _ $$ Hr
    wp_auto
    by_cases hn : uint.nat x ≤ rest.length
    rotate_left
    · rw [decide_eq_true (show uint.Z r.len < uint.Z x by word)]
      wp_auto
      iapply HΦ
      rw [if_neg hn]
      dsimp only
      iframe
      isplitr
      · ipureintro; rfl
      iapply Hback $$ Hr
    rw [decide_eq_false (show ¬ uint.Z r.len < uint.Z x by word)]
    wp_auto
    have hxs : sint.Z x = uint.Z x := by word
    rw [if_pos hn]
    by_cases hx0 : x = W64 0
    rw [decide_eq_false (by rw [hx0]; decide)]
    wp_auto
    rw [if_pos (by rw [hx0]; decide)]
    wp_auto
    ihave Hn := ownSlice_nil (V := transport.ValueVersion) (DFrac.own 1)
    ihave Hs : (slice.slice slice.nil transport.ValueVersion (W64 0) x ↦*
        List.replicate (uint.nat x) zVV) $$ [Hn]
    · subst hx0
      icases (ownSlice_slice (V := transport.ValueVersion) (W64 0) (W64 0) slice.nil (DFrac.own 1) []
        ⟨by decide, by decide, by decide⟩).1 $$ Hn with ⟨-, Hs, -⟩
      have e : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) ([] : List transport.ValueVersion) =
          List.replicate (uint.nat (W64 0)) zVV := by simp [subslice]
      rw [e]
      iexact Hs
    generalize slice.slice slice.nil transport.ValueVersion (W64 0) x = sl at *
    iclear Hn
    rotate_left
    rw [decide_eq_true (show uint.Z (0 : w64) < uint.Z x by
      have : uint.Z x ≠ 0 := fun h => hx0 (by word)
      have : (0 : Int) ≤ uint.Z x := by word
      show (0 : Int) < uint.Z x
      omega)]
    wp_auto
    wp_apply wp_slice_make2 (V := transport.ValueVersion) x
    · ipureintro; word
    iintro %sl ⟨Hs, -⟩
    rw [show sint.nat x = uint.nat x by word, show zero_val transport.ValueVersion = zVV from rfl]
    wp_auto
    rotate_left
    all_goals
      ihave %hsl := ownSlice_len _ _ _ $$ Hs
      simp only [List.length_replicate] at hsl
      ihave HI : (∃ (i : w64) (R : GoSlice) (vvs : List transport.ValueVersion)
          (acc : List (GoString × w64)) (cur : List w8),
          "i" ∷ i_ptr ↦ i ∗ "r" ∷ r_ptr ↦ R ∗ "ok" ∷ ok_ptr ↦ true ∗ "Hr" ∷ R ↦*{dq} cur ∗
          "Hback" ∷ (R ↦*{dq} cur -∗ b ↦*{dq} bs) ∗
          "Hs" ∷ sl ↦* (vvs ++ List.replicate (uint.nat x - uint.nat i) zVV) ∗
          "HV" ∷ ([∗list] j ↦ vv ∈ vvs, vvElem acc j vv) ∗
          "%Hi" ∷ ⌜vvs.length = uint.nat i ∧ acc.length = uint.nat i ∧ uint.nat i ≤ uint.nat x ∧
            vvs.map (·.Version') = acc.map Prod.snd ∧
            decVVsGo (uint.nat x - uint.nat i) acc cur = decVVsGo (uint.nat x) [] rest⌝ : IProp GF)
          $$ [i r ok Hr Hback Hs]
      · iexists W64 0, r, [], [], rest
        simp only [show uint.nat (W64 0) = 0 from rfl, Nat.sub_zero, List.nil_append]
        iframe
        isplitl []
        · iapply BigSepL.bigSepL_nil.2; iempintro
        ipureintro
        simp
      wp_for HI
      wp_if_destruct
      · have hi : uint.Z i < uint.Z x := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        have hk : uint.nat x - uint.nat i = (uint.nat x - uint.nat i - 1) + 1 := by word
        rw [if_pos (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len by
          have := hsl.1; have := hsl.2
          have h2 : ((sint.Z sl.len).toNat : Int) = sint.Z sl.len := Int.toNat_of_nonneg hsl.2
          rw [show sint.nat sl.len = (sint.Z sl.len).toNat from rfl] at *
          word)]
        have hlk : (vvs ++ List.replicate (uint.nat x - uint.nat i) zVV)[(sint.Z i).toNat]? =
            some zVV := by
          rw [show (sint.Z i).toNat = vvs.length by word, hk]
          simp
        icases ownSlice_elem_acc (sint.Z i) zVV sl _ _ (by word) hlk $$ Hs with ⟨He, Hs⟩
        wp_apply wp_rpcDec_t10 R cur dq _ _ $$ Hr He
        iintro %R2 %ok2 Hd
        rcases hd : decVV cur with _ | ⟨⟨xv, v⟩, cur2⟩
        · simp only [hd]
          icases Hd with ⟨%Hok, ⟨%vsl, %vv, He⟩, Hr⟩
          subst Hok
          ihave Hs := Hs $$ He
          wp_auto
          rw [forPostcondition_unseal]; unfold forPostconditionDef; iright; iright; iright; ileft
          iexists #()
          isplitr
          · ipureintro; rfl
          dsimp only
          wp_auto
          have hres : decVVsGo (uint.nat x) [] rest = none := by
            rw [← Hi.2.2.2.2, hk]; simp [decVVsGo, hd]
          iapply HΦ
          rw [hres]
          dsimp only
          ihave Hb := Hback $$ Hr
          iframe
          ipureintro; rfl
        · simp only [hd]
          icases Hd with ⟨%Hok, ⟨%vsl, He, Hx⟩, Hr, Hback2⟩
          subst Hok
          imod ownSlice_persist $$ Hx with #Hx
          ihave Hs := Hs $$ He
          wp_auto
          wp_for_post
          ihave Hback := wand_trans _ _ _ $$ Hback2 Hback
          ihave HV := vvElem_snoc vvs acc _ xv v Hi.1 Hi.2.1 $$ HV Hx
          have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
          have hset : (vvs ++ List.replicate (uint.nat x - uint.nat i) zVV).set (sint.Z i).toNat
                (transport.ValueVersion.mk vsl v) =
              (vvs ++ [transport.ValueVersion.mk vsl v]) ++
                List.replicate (uint.nat x - uint.nat (i + W64 1)) zVV := by
            rw [show (sint.Z i).toNat = vvs.length by word, hk, hi1,
              show uint.nat x - (uint.nat i + 1) = uint.nat x - uint.nat i - 1 by omega]
            simp [List.replicate_succ]
          rw [hset]
          iframe
          iexists i + W64 1, R2, vvs ++ [transport.ValueVersion.mk vsl v], acc ++ [(xv, v)], cur2
          iframe
          ipureintro
          refine ⟨by rw [List.length_append, Hi.1, hi1]; rfl, by rw [List.length_append, Hi.2.1, hi1]; rfl,
            by rw [hi1]; omega, by simp [Hi.2.2.2.1], ?_⟩
          rw [← Hi.2.2.2.2, hk, hi1, show uint.nat x - (uint.nat i + 1) = uint.nat x - uint.nat i - 1 by omega]
          simp [decVVsGo, hd]
      · have hc : ¬ uint.Z i < uint.Z x := by
          first | exact Hif | exact fun h => Hif (by simp [h])
        (try (rw [decide_eq_false hc, if_pos (by simp)]))
        (try wp_auto)
        have hix : uint.nat x - uint.nat i = 0 := by
          word
        have hres : decVVsGo (uint.nat x) [] rest = some (acc, cur) := by
          rw [← Hi.2.2.2.2, hix]; rfl
        iapply HΦ
        rw [hres]
        dsimp only
        rw [hix, List.replicate_zero, List.append_nil]
        iframe
        isplitr
        · ipureintro; rfl
        unfold vvsOwn
        iexists vvs
        iframe
        ipureintro; exact Hi.2.2.2.1


/-- `k` more response entries, after `acc`. -/
def decPRGo : Nat → List (GoString × List (GoString × w64)) → List w8 →
    Option (List (GoString × List (GoString × w64)) × List w8)
  | 0, acc, r => some (acc, r)
  | k + 1, acc, r =>
    match getTag r with
    | none => none
    | some (key, r') =>
      match decVVs r' with
      | none => none
      | some (vs, r'') => decPRGo k (acc ++ [(key, vs)]) r''

/-- The pure `rpcDec_t8` (`PropagateResponse`): its entries in order. -/
def decPR (bs : List w8) : Option (List (GoString × List (GoString × w64)) × List w8) :=
  match getU64 bs with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then decPRGo (uint.nat n) [] r else none

/-- The map of a list of entries (later ones win). -/
def respL (es : List (GoString × List (GoString × w64))) : GMap GoString (List (GoString × w64)) :=
  es.foldl (fun m e => <[e.1 := e.2]> m) ∅

/-- The slices of the map `m` hold the response `resp`. -/
def respOwn (m : GMap GoString GoSlice) (resp : GMap GoString (List (GoString × w64))) : IProp GF :=
  iprop(⌜∀ k, (m.lookup k).isSome ↔ (resp.lookup k).isSome⌝ ∗
    [∗map] k ↦ sl ∈ m, vvsOwn sl ((resp.lookup k).getD []))

theorem respOwn_insert (m : GMap GoString GoSlice) (resp : GMap GoString (List (GoString × w64)))
    (key : GoString) (sl : GoSlice) (vs : List (GoString × w64)) :
    respOwn (GF := GF) m resp -∗ vvsOwn sl vs -∗ respOwn (<[key := sl]> m) (<[key := vs]> resp) := by
  unfold respOwn
  iintro ⟨%Hdom, Hm⟩ Hsl
  isplitr
  · ipureintro
    intro k
    show ((<[key := sl]> m) !! k).isSome ↔ ((<[key := vs]> resp) !! k).isSome
    simp only [GMap.lookup_insert_eq_iff]
    split
    · simp
    · exact Hdom k
  ihave Hd : ([∗map] k ↦ s ∈ GMap.delete key m, vvsOwn (GF := GF) s ((resp !! k).getD [])) $$ [Hm]
  · rcases hk : m !! key with _ | s0
    · have e : GMap.delete key m = m := by
        rw [GMap.ext_iff']
        intro k
        by_cases h : k = key
        · subst h; exact (GMap.lookup_delete m k).trans hk.symm
        · exact GMap.lookup_delete_ne m (Ne.symm h)
      rw [e]
      iexact Hm
    · icases (BigSepM.bigSepM_delete (Φ := fun k s => vvsOwn (GF := GF) s ((resp !! k).getD []))
        (m := m) (i := key) (x := s0) hk).1 $$ Hm with ⟨-, Hm⟩
      iexact Hm
  iapply (BigSepM.bigSepM_insert_delete (Φ := fun k s =>
    vvsOwn (GF := GF) s ((<[key := vs]> resp !! k).getD [])) (m := m) (i := key) (x := sl)).2
  isplitl [Hsl]
  · simp only [GMap.lookup_insert, Option.getD_some]
    iexact Hsl
  iapply (BigSepM.bigSepM_mono ?_) $$ Hd
  intro k s hks
  have hne : key ≠ k := by
    intro h; subst h
    have : (GMap.delete key m) !! key = none := GMap.lookup_delete m key
    rw [show (GMap.delete key m) !! key = PartialMap.get? (GMap.delete key m) key from rfl] at this
    rw [this] at hks; cases hks
  simp only [GMap.lookup_insert_ne _ _ hne]
  exact .rfl

theorem wp_rpcDec_t8 (b : GoSlice) (bs : List w8) (dq : DFrac) (p mp : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ mp -∗ ownMap mp (DFrac.own 1) (∅ : GMap GoString GoSlice) -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decPR bs with
          | some (es, rest) => ⌜ok = true⌝ ∗
              (∃ (mp' : Loc) (m : GMap GoString GoSlice), p ↦ mp' ∗ ownMap mp' (DFrac.own 1) m ∗
                respOwn m (respL es)) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ mp' : Loc, p ↦ mp') ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t8)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp Hm HΦ
  ihave %Hmn := ownMap_not_nil _ _ _ $$ Hm
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold decPR
  rcases hg : getU64 bs with _ | ⟨n, rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hb⟩
    subst Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    ihave %Hl := ownSlice_lenZ _ _ _ $$ Hr
    wp_auto
    by_cases hn : uint.nat x ≤ rest.length
    rotate_left
    · rw [decide_eq_true (show uint.Z r.len < uint.Z x by word)]
      wp_auto
      iapply HΦ
      rw [if_neg hn]
      dsimp only
      iframe
      isplitr
      · ipureintro; rfl
      iapply Hback $$ Hr
    rw [decide_eq_false (show ¬ uint.Z r.len < uint.Z x by word)]
    rw [if_pos hn]
    wp_auto
    rw [decide_eq_false Hmn]
    wp_auto
    ihave HR0 : respOwn (GF := GF) (∅ : GMap GoString GoSlice) (respL []) $$ []
    · unfold respOwn respL
      isplitr
      · ipureintro; intro k; simp [show ∀ m : GMap GoString GoSlice, m.lookup k = m !! k from fun _ => rfl,
          show ∀ m : GMap GoString (List (GoString × w64)), m.lookup k = m !! k from fun _ => rfl]
      iapply BigSepM.bigSepM_empty.2; iempintro
    ihave HI : (∃ (i : w64) (R : GoSlice) (acc : List (GoString × List (GoString × w64)))
        (cur : List w8) (m : GMap GoString GoSlice),
        "i" ∷ i_ptr ↦ i ∗ "r" ∷ r_ptr ↦ R ∗ "ok" ∷ ok_ptr ↦ true ∗ "Hr" ∷ R ↦*{dq} cur ∗
        "Hback" ∷ (R ↦*{dq} cur -∗ b ↦*{dq} bs) ∗
        "Hm" ∷ ownMap mp (DFrac.own 1) m ∗ "HR" ∷ respOwn m (respL acc) ∗
        "%Hi" ∷ ⌜acc.length = uint.nat i ∧ uint.nat i ≤ uint.nat x ∧
          decPRGo (uint.nat x - uint.nat i) acc cur = decPRGo (uint.nat x) [] rest⌝ : IProp GF)
        $$ [i r ok Hr Hback Hm HR0]
    · iexists W64 0, r, [], rest, ∅
      simp only [show uint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
      iframe
      ipureintro
      simp
    wp_for HI
    wp_if_destruct
    · have hi : uint.Z i < uint.Z x := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      have hk : uint.nat x - uint.nat i = (uint.nat x - uint.nat i - 1) + 1 := by word
      wp_apply wp_rpcDec_t5 R cur dq x_ptr _ _ $$ Hr x
      iintro %R1 %ok1 Hd1
      rcases hd1 : getTag cur with _ | ⟨key, cur1⟩
      · simp only [hd1]
        icases Hd1 with ⟨%Hok, Hx, Hr⟩
        subst Hok
        wp_auto
        have hres : decPRGo (uint.nat x) [] rest = none := by
          rw [← Hi.2.2, hk]; simp [decPRGo, hd1]
        ihave Hb := Hback $$ Hr
        rw [forPostcondition_unseal]; unfold forPostconditionDef; iright; iright; iright; ileft
        iexists #()
        isplitr
        · ipureintro; rfl
        dsimp only
        wp_auto
        iapply HΦ
        rw [hres]
        dsimp only
        iframe
        ipureintro; rfl
      simp only [hd1]
      icases Hd1 with ⟨%Hok, Hx, Hr1, Hback1⟩
      subst Hok
      wp_auto
      wp_apply wp_rpcDec_t9 R1 cur1 dq y_ptr _ $$ Hr1 y
      iintro %R2 %ok2 Hd2
      rcases hd2 : decVVs cur1 with _ | ⟨vs, cur2⟩
      · simp only [hd2]
        icases Hd2 with ⟨%Hok, Hy, Hr1⟩
        subst Hok
        wp_auto
        have hres : decPRGo (uint.nat x) [] rest = none := by
          rw [← Hi.2.2, hk]; simp [decPRGo, hd1, hd2]
        ihave Hb := Hback $$ [Hback1 Hr1]
        · iapply Hback1 $$ Hr1
        rw [forPostcondition_unseal]; unfold forPostconditionDef; iright; iright; iright; ileft
        iexists #()
        isplitr
        · ipureintro; rfl
        dsimp only
        wp_auto
        iapply HΦ
        rw [hres]
        dsimp only
        iframe
        ipureintro; rfl
      simp only [hd2]
      icases Hd2 with ⟨%Hok, ⟨%sl, Hy, Hvv⟩, Hr2, Hback2⟩
      subst Hok
      wp_auto
      wp_apply wp_mapInsert go.string mp m key sl $$ Hm as Hm
      (try wp_auto)
      wp_for_post
      ihave HR := respOwn_insert m (respL acc) key sl vs $$ HR Hvv
      ihave Hback2 := wand_trans _ _ _ $$ Hback2 Hback1
      ihave Hback := wand_trans _ _ _ $$ Hback2 Hback
      have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
      have hrl : respL (acc ++ [(key, vs)]) = <[key := vs]> (respL acc) := by
        simp [respL, List.foldl_append]
      iframe
      iexists i + W64 1, R2, acc ++ [(key, vs)], cur2, <[key := sl]> m
      rw [hrl]
      iframe
      ipureintro
      refine ⟨by rw [List.length_append, Hi.1, hi1]; rfl, by rw [hi1]; omega, ?_⟩
      rw [← Hi.2.2, hk, hi1, show uint.nat x - (uint.nat i + 1) = uint.nat x - uint.nat i - 1 by omega]
      simp [decPRGo, hd1, hd2]
    · have hc : ¬ uint.Z i < uint.Z x := by
        first | exact Hif | exact fun h => Hif (by simp [h])
      (try (rw [decide_eq_false hc, if_pos (by simp)]))
      (try wp_auto)
      have hix : uint.nat x - uint.nat i = 0 := by
        word
      have hres : decPRGo (uint.nat x) [] rest = some (acc, cur) := by
        rw [← Hi.2.2, hix]; rfl
      iapply HΦ
      rw [hres]
      dsimp only
      iframe
      ipureintro; rfl

/-! ### `PropagateResponse` round trip -/

theorem len_le_flatten (L : List (List w8)) (l : List w8) (h : l ∈ L) :
    l.length ≤ L.flatten.length := by
  induction L with
  | nil => cases h
  | cons a L ih =>
    simp only [List.flatten_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem count_le_flatten (L : List (List w8)) (h : ∀ l ∈ L, l ≠ []) : L.length ≤ L.flatten.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    have ha : a ≠ [] := h a (List.mem_cons_self ..)
    have : 0 < a.length := List.length_pos_iff.2 ha
    have := ih (fun l hl => h l (List.mem_cons_of_mem _ hl)); omega

theorem len_fBytes (x : List w8) : x.length ≤ (fBytes x).length := by
  by_cases hx : x = []
  · simp [hx]
  · have h2 : x.length ≤ (x.map fun c => u64Le (W64 (uint.Z c))).flatten.length := by
      have := count_le_flatten (x.map fun c => u64Le (W64 (uint.Z c)))
        (fun l hl => by
          obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl
          intro h; have := congrArg List.length h; simp [u64Le_length] at this)
      simpa using this
    simp only [fBytes, fld, hx, decide_false, decide_true, ne_eq, not_false_eq_true, ↓reduceIte, encBytes,
      List.length_cons, List.length_append]
    omega

theorem decVV_enc (x : List w8) (v : w64) (rest : List w8) (hx : x.length < 2 ^ 64) :
    decVV (strct [fBytes x, fU64 v] ++ rest) = some ((x, v), rest) := by
  have e : strct [fBytes x, fU64 v] ++ rest = W8 1 :: (fBytes x ++ (fU64 v ++ rest)) := by
    simp [strct]
  rw [e]
  simp only [decVV, decHdr, ↓reduceIte, decFld_fBytes x _ hx, decFld_fU64]

theorem decVVsGo_enc (vs acc : List (GoString × w64)) (rest : List w8)
    (h : ∀ e ∈ vs, e.1.length < 2 ^ 64) :
    decVVsGo vs.length acc ((vs.map fun e => strct [fBytes e.1, fU64 e.2]).flatten ++ rest) =
      some (acc ++ vs, rest) := by
  induction vs generalizing acc with
  | nil => simp [decVVsGo]
  | cons e vs ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decVVsGo,
      decVV_enc e.1 e.2 _ (h e (List.mem_cons_self ..)),
      ih (acc ++ [e]) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    simp

theorem decVVs_enc (vs : List (GoString × w64)) (rest : List w8) (hl : vs.length < 2 ^ 64)
    (h : ∀ e ∈ vs, e.1.length < 2 ^ 64) :
    decVVs (encVVs vs ++ rest) = some (vs, rest) := by
  unfold decVVs encVVs encU64
  rw [List.append_assoc, getU64_enc']
  have hn : uint.nat (W64 vs.length) = vs.length := by
    show (BitVec.ofNat 64 vs.length).toNat = vs.length
    simp only [BitVec.toNat_ofNat]; omega
  have hle : vs.length ≤ ((vs.map fun e => strct [fBytes e.1, fU64 e.2]).flatten ++ rest).length := by
    have := count_le_flatten (vs.map fun e => strct [fBytes e.1, fU64 e.2])
      (fun l hl => by obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl; simp [strct])
    simp only [List.length_append, List.length_map] at this ⊢; omega
  simp only [hn, hle, ↓reduceIte, decVVsGo_enc vs [] rest h, List.nil_append]

theorem decPRGo_enc (es acc : List (GoString × List (GoString × w64))) (rest : List w8)
    (h : ∀ e ∈ es, e.1.length < 2 ^ 64 ∧ e.2.length < 2 ^ 64 ∧ ∀ x ∈ e.2, x.1.length < 2 ^ 64) :
    decPRGo es.length acc ((es.map fun e => encStr e.1 ++ encVVs e.2).flatten ++ rest) =
      some (acc ++ es, rest) := by
  induction es generalizing acc with
  | nil => simp [decPRGo]
  | cons e es ih =>
    have he := h e (List.mem_cons_self ..)
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decPRGo,
      getTag_encStr' e.1 _ he.1, decVVs_enc e.2 _ he.2.1 he.2.2,
      ih (acc ++ [e]) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    simp

theorem respL_spec (es : List (GoString × List (GoString × w64))) (hnd : (es.map Prod.fst).Nodup)
    (m0 : GMap GoString (List (GoString × w64))) (k : GoString) (v : List (GoString × w64)) :
    (es.foldl (fun m e => <[e.1 := e.2]> m) m0) !! k = some v ↔
      ((k, v) ∈ es ∨ (k ∉ es.map Prod.fst ∧ m0 !! k = some v)) := by
  induction es generalizing m0 with
  | nil => simp
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rw [ih hnd.2]
    by_cases hk : k' = k
    · subst hk
      have : ∀ w, (k', w) ∉ es := fun w hw => hnd.1 (List.mem_map.2 ⟨_, hw, rfl⟩)
      simp [this, hnd.1, GMap.lookup_insert_eq_iff, eq_comm]
    · have hk' : k ≠ k' := fun h => hk h.symm
      simp [hk, hk', GMap.lookup_insert_eq_iff]

theorem respL_eq (r : GMap GoString (List (GoString × w64))) (es : List (GoString × List (GoString × w64)))
    (h : entriesOf r es) : respL es = r := by
  rw [GMap.ext_iff']
  intro k
  have hs := respL_spec es h.1 ∅ k
  show (respL es) !! k = r !! k
  rcases hr : r !! k with _ | v
  · rcases hl : (respL es) !! k with _ | v
    · rfl
    · rcases (hs v).1 hl with h' | ⟨-, h'⟩
      · have := (h.2 k v).2 h'
        rw [show r.lookup k = r !! k from rfl, hr] at this; cases this
      · simp at h'
  · exact (hs v).2 (Or.inl ((h.2 k v).1 (by rw [show r.lookup k = r !! k from rfl, hr])))

theorem decPR_enc (es : List (GoString × List (GoString × w64)))
    (hb : (encPropRespL es).length < 2 ^ 63) (t : GoString) (rest : List w8)
    (hg : getTag (encPropRespL es) = some (t, rest)) : decPR rest = some (es, []) := by
  unfold encPropRespL tagged at hg hb
  rw [getTag_encStr' _ _ (by decide)] at hg
  cases hg
  have hfl : (es.map fun e => encStr e.1 ++ encVVs e.2).flatten.length < 2 ^ 63 := by
    simp only [List.length_append] at hb; omega
  have helem : ∀ e ∈ es, (encStr e.1 ++ encVVs e.2).length < 2 ^ 63 := fun e he =>
    Nat.lt_of_le_of_lt (len_le_flatten _ _ (List.mem_map_of_mem (f := fun e => encStr e.1 ++ encVVs e.2) he)) hfl
  have hcnt : es.length ≤ (es.map fun e => encStr e.1 ++ encVVs e.2).flatten.length := by
    have := count_le_flatten (es.map fun e => encStr e.1 ++ encVVs e.2)
      (fun l hl => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hl
        intro h; have := congrArg List.length h; simp [encStr, u64Le_length] at this)
    simpa using this
  have h : ∀ e ∈ es, e.1.length < 2 ^ 64 ∧ e.2.length < 2 ^ 64 ∧ ∀ x ∈ e.2, x.1.length < 2 ^ 64 := by
    intro e he
    have h1 := helem e he
    have hv : (encVVs e.2).length < 2 ^ 63 := by simp only [List.length_append] at h1; omega
    refine ⟨by simp only [encStr, List.length_append] at h1; omega, ?_, ?_⟩
    · have := count_le_flatten (e.2.map fun x => strct [fBytes x.1, fU64 x.2])
        (fun l hl => by obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl; simp [strct])
      simp only [encVVs, List.length_append, List.length_map] at hv this; omega
    · intro x hx
      have h2 := len_le_flatten _ _ (List.mem_map_of_mem (f := fun x : GoString × w64 => strct [fBytes x.1, fU64 x.2]) hx)
      have h3 := len_fBytes x.1
      have h4 : (fBytes x.1).length ≤ (strct [fBytes x.1, fU64 x.2]).length := by
        simp [strct]; omega
      simp only [encVVs, List.length_append] at hv; omega
  unfold decPR encU64
  rw [getU64_enc']
  have hn : uint.nat (W64 es.length) = es.length := by
    show (BitVec.ofNat 64 es.length).toNat = es.length
    simp only [BitVec.toNat_ofNat]; omega
  simp only [hn, hcnt, ↓reduceIte]
  have := decPRGo_enc es [] [] h
  simpa using this

theorem dec_PropagateResponse : dec_PropagateResponse.spec (GF := GF) := by
  intro p mp rep Ψ
  iintro ⟨%Htag, Hp, Hm, HΨ⟩
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data rep dq $$ Hd
  iintro %t %r %ok H
  rcases hg : getTag rep with _ | ⟨t', rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hd⟩
    subst Hok
    wp_auto
    ihave HΨ0 := HΨ $$ %false [Hp]
    · simp only [Bool.false_eq_true, ite_false]; iexists _; iexact Hp
    dec_fail
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    have ht := Htag _ _ hg
    subst ht
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDec_t8 r rest dq p mp $$ Hr Hp Hm
    iintro %r2 %ok2 H2
    rcases hd : decPR rest with _ | ⟨es, rest2⟩
    · simp only [hd]
      icases H2 with ⟨%Hok, Hp, Hr⟩
      subst Hok
      wp_auto
      ihave Hd := Hback $$ Hr
      ihave HΨ0 := HΨ $$ %false [Hp]
      · simp only [Bool.false_eq_true, ite_false]; iexact Hp
      dec_fail
    · simp only [hd]
      icases H2 with ⟨%Hok, ⟨%mp', %m, Hp, Hm, HR⟩, Hr2, Hback2⟩
      subst Hok
      ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
      wp_auto
      ihave Hd := Hback $$ [Hback2 Hr2]
      · iapply Hback2 $$ Hr2
      by_cases h0 : rest2 = []
      · subst h0
        rw [show r2.len = W64 0 by simp at Hl2; word]
        wp_auto
        iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp Hm HR]
        · iapply HΨ
          simp only [ite_true]
          iexists respL es
          isplitl [Hp Hm HR]
          · unfold respPtr
            unfold respOwn vvsOwn vvElem
            iexists mp', m
            iframe
          ipureintro
          intro r' ⟨es', hes', he⟩
          subst he
          have h3 : sint.Z data.len < 2 ^ 63 := by word
          have := decPR_enc es' (by omega) _ _ hg
          rw [this] at hd
          cases hd
          exact respL_eq r' es hes'
        simp only [ite_true]
        ipureintro; trivial
      · rw [decide_eq_false (show ¬ r2.len = W64 0 by
          intro h; rw [h] at Hl2; exact h0 (List.eq_nil_of_length_eq_zero (Hl2.1.trans (by rfl))))]
        wp_auto
        ihave HΨ0 := HΨ $$ %false [Hp]
        · simp only [Bool.false_eq_true, ite_false]; iexists _; iexact Hp
        dec_fail

/-- The codec lemmas (hypothesis H5), proved. -/
theorem craqCodecLaws : CodecLaws (GF := GF) where
  enc_string := enc_string
  enc_EmptyArgs := enc_EmptyArgs
  enc_NodeMeta := enc_NodeMeta
  enc_CommitArgs := enc_CommitArgs
  enc_WriteArgs := enc_WriteArgs
  enc_ClientWriteArgs := enc_ClientWriteArgs
  enc_PropagateRequest := enc_PropagateRequest
  dec_EmptyReply := dec_EmptyReply
  dec_VersionResponse := dec_VersionResponse
  dec_Item := dec_Item
  dec_NodeMeta := dec_NodeMeta
  dec_PropagateResponse := dec_PropagateResponse

end proof

end github_com.despreston.go_craq
end Perennial
