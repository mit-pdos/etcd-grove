/-
The kit's generated codec (`examples/gryffnet/rpc_gen.go`) meets the codec lemmas of `Codec.lean`
(dsv-craq's `CodecProof.lean`/`CodecSrvProof.lean`, adapted to gryff's types): the encoders' bytes
are `Rpc/Defs.lean`'s, and decoding an encoding into the target's starting value gives back the
encoded value.
-/
module

public import Dsverify.Proof.gryff.Rpc.Codec
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [examples.gryffnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true


/-- `rpcPutU64(b, x)`: `b` with `x`'s 8 bytes (little-endian) appended. -/
theorem wp_rpcPutU64 (b : GoSlice) (bs : List w8) (x : w64) :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! examples.gryffnet.rpcPutU64)) (Val #b)) (Val #x))
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

theorem wp_rpcEnc_t12 (s : GoString) : encFn (GF := GF) examples.gryffnet.rpcEnc_t12 #s (encStr s) iprop(True) := by
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


theorem wp_rpcEnc_t2 (x : w64) : encFn (GF := GF) examples.gryffnet.rpcEnc_t2 #x (encU64 x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t64 (x : w8) :
    encFn (GF := GF) examples.gryffnet.rpcEnc_t64 #x (u64Le (W64 (uint.Z x))) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t13 (x : Bool) : encFn (GF := GF) examples.gryffnet.rpcEnc_t13 #x (encBool x) iprop(True) := by
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

theorem wp_rpcSent_t12 (s : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! examples.gryffnet.rpcSent_t12)) (Val #s))
    {{ RET #(decide (s ≠ [])); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (s = [])) = decide (s ≠ []) by simp]
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t2 (x : w64) :
    {{ (True : IProp GF) }} (App (Val (@! examples.gryffnet.rpcSent_t2)) (Val #x))
    {{ RET #(decide (x ≠ W64 0)); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (x = W64 0)) = decide (x ≠ W64 0) by simp]
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t13 (x : Bool) :
    {{ (True : IProp GF) }} (App (Val (@! examples.gryffnet.rpcSent_t13)) (Val #x))
    {{ RET #x; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t64 (x : w8) :
    {{ (True : IProp GF) }} (App (Val (@! examples.gryffnet.rpcSent_t64)) (Val #x))
    {{ RET #(decide (x ≠ W8 0)); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (x = W8 0)) = decide (x ≠ W8 0) by simp]
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t11 (sl : GoSlice) (dq : DFrac) (x : List GoString) :
    {{ (sl ↦*{dq} x : IProp GF) }} (App (Val (@! examples.gryffnet.rpcSent_t11)) (Val #sl))
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

theorem wp_rpcEnc_t11 (sl : GoSlice) (dq : DFrac) (x : List GoString) :
    encFn (GF := GF) examples.gryffnet.rpcEnc_t11 #sl (encStrs x) iprop(sl ↦*{dq} x) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, Hsl⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  have hlen : sl.len = W64 x.length := by rw [Hl.1]; word
  ihave HI : (∃ (i : w64) (bb : GoSlice) (y : GoString),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗ "x" ∷ x_ptr ↦ y ∗
      "Hb" ∷ bb ↦* (bs ++ u64Le sl.len ++
        ((x.take (sint.nat i)).map encStr).flatten) ∗
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
    unfold encStrs
    rw [← hlen, List.append_assoc,
      show (x.map encStr).flatten =
        ((x.take (sint.nat i)).map encStr).flatten by
        rw [hn, List.take_length]]
    iexact Hb


set_option hygiene false in
/-- The last step of a struct encoder's proof: its bytes are `Wire.lean`'s. -/
macro "enc_close" : tactic => `(tactic| (
  iapply HΦ
  isimp only [strct, fld, fStr, fU64, fU8, fStrs, fBool, encBool, List.flatten_cons, List.flatten_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.singleton_append, List.append_nil,
    _root_.decide_true, _root_.decide_false, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
    Bool.false_eq_true, ↓reduceIte, *]
  (try isimp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at Hb)
  iframe))

theorem wp_rpcEnc_t15 (addr : GoString) (port : w64) :
    encFn (GF := GF) examples.gryffnet.rpcEnc_t15 #(src.masterproto.RegisterArgs.mk addr port)
      (strct [fStr addr, fU64 port]) iprop(True) := by
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
    wp_apply wp_rpcSent_t12 addr
    by_cases haddr : addr = [] <;> simp only [haddr, ne_eq, not_true_eq_false, not_false_eq_true, _root_.decide_false, _root_.decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t12 addr _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t2 port
    by_cases hport : port = W64 0 <;> simp only [hport, ne_eq, not_true_eq_false, not_false_eq_true, _root_.decide_false, _root_.decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t2 port _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t17 (id : w64) (nl : GoSlice) (dqs : DFrac) (nodes : List GoString) (ready : Bool) :
    encFn (GF := GF) examples.gryffnet.rpcEnc_t17 #(src.masterproto.RegisterReply.mk id nl ready)
      (strct [fU64 id, fStrs nodes, fBool ready]) iprop(nl ↦*{dqs} nodes) := by
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
    wp_apply wp_rpcSent_t2 id
    by_cases hid : id = W64 0 <;> simp only [hid, ne_eq, not_true_eq_false, not_false_eq_true, _root_.decide_false, _root_.decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t2 id _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t11 nl dqs nodes $$ [$Hsl] as Hsl
    by_cases hnodes : nodes = [] <;> simp only [hnodes, ne_eq, not_true_eq_false, not_false_eq_true, _root_.decide_false, _root_.decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t11 nl dqs nodes _ _ $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, Hsl⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t13 ready
    cases hready : ready
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t13 _ _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t63 (a : w8) :
    encFn (GF := GF) examples.gryffnet.rpcEnc_t63 #(src.genericsmrproto.PingArgs.mk a)
      (strct [fU8 a]) iprop(True) := by
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
    wp_apply wp_rpcSent_t64 a
    by_cases ha : a = W8 0 <;> simp only [ha, ne_eq, not_true_eq_false, not_false_eq_true, _root_.decide_false, _root_.decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t64 a _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t59 :
    encFn (GF := GF) examples.gryffnet.rpcEnc_t59 #(src.genericsmrproto.BeTheLeaderArgs.mk)
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

theorem wp_rpcEnc_t61 :
    encFn (GF := GF) examples.gryffnet.rpcEnc_t61 #(src.genericsmrproto.BeTheLeaderReply.mk)
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

theorem wp_rpcEnc_t66 :
    encFn (GF := GF) examples.gryffnet.rpcEnc_t66 #(src.genericsmrproto.PingReply.mk)
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

/-- `rpcPutTag(tag)`: a new slice, the string `tag`'s encoding. -/
theorem wp_rpcPutTag (tag : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! examples.gryffnet.rpcPutTag)) (Val #tag))
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

theorem enc_RegisterArgs : enc_RegisterArgs.spec (GF := GF) := by
  intro p dq addr port Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t15 addr port _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encRegArgs, tagged] at HΨ
  iapply HΨ $$ Hp

theorem enc_PingArgs : enc_PingArgs.spec (GF := GF) := by
  intro p dq a Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t63 a _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encPingArgs, tagged] at HΨ
  iapply HΨ $$ Hp

theorem enc_BTLArgs : enc_BTLArgs.spec (GF := GF) := by
  intro p dq Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t59  _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encBTLArgs, tagged] at HΨ
  iapply HΨ $$ Hp

theorem enc_RegisterReply : enc_RegisterReply.spec (GF := GF) := by
  intro p dq id nl dqs nodes ready Ψ
  iintro ⟨Hp, Hsl, HΨ⟩
  unfold gryffCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t17 id nl dqs nodes ready _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, Hsl⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encRegReply, tagged] at HΨ
  iapply HΨ $$ Hp Hsl

theorem enc_PingReply : enc_PingReply.spec (GF := GF) := by
  intro p dq Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t66  _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encPingReply, tagged] at HΨ
  iapply HΨ $$ Hp

theorem enc_BTLReply : enc_BTLReply.spec (GF := GF) := by
  intro p dq Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t61  _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encBTLReply, tagged] at HΨ
  iapply HΨ $$ Hp


/-- The pure `rpcGetU64`. -/
def getU64 (bs : List w8) : Option (w64 × List w8) :=
  if 8 ≤ bs.length then some (leToU64 (bs.take 8), bs.drop 8) else none

/-- The pure `rpcGetTag` (and `rpcDec_t12`): a length, then that many bytes. -/
def getTag (bs : List w8) : Option (GoString × List w8) :=
  match getU64 bs with
  | some (n, r) => if uint.nat n ≤ r.length then some (r.take (uint.nat n), r.drop (uint.nat n)) else none
  | none => none

/-- `rep`'s type tag, if it parses, is `t`. -/
def tagOk (t : GoString) (rep : List w8) : Prop :=
  ∀ t' rest, getTag rep = some (t', rest) → t' = t

theorem getU64_enc (x : w64) (rest : List w8) : getU64 (u64Le x ++ rest) = some (x, rest) := by
  unfold getU64
  rw [ite_eq_left (by simp [u64Le_length])]
  have h8 := u64Le_length x
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
    u64Le_to_word]

theorem getTag_encStr (s : GoString) (rest : List w8) (hs : s.length < 2 ^ 64) :
    getTag (encStr s ++ rest) = some (s, rest) := by
  unfold getTag encStr
  rw [List.append_assoc, getU64_enc]
  have hn : uint.nat (W64 s.length) = s.length := by
    show (BitVec.ofNat 64 s.length).toNat = s.length
    simp only [BitVec.toNat_ofNat]; omega
  simp only [hn, List.length_append, Nat.le_add_right, ite_true, List.take_left', List.drop_left']

theorem tagOk_tagged (t : GoString) (body : List w8) (ht : t.length < 2 ^ 64) :
    tagOk t (tagged t body) := by
  intro t' rest h
  unfold tagged at h
  rw [getTag_encStr t body ht] at h
  cases h; rfl


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
    WP (App (Val (@! examples.gryffnet.rpcGetU64)) (Val #b)) {{ Φ }} := by
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
    WP (App (Val (@! examples.gryffnet.rpcGetTag)) (Val #b)) {{ Φ }} := by
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

theorem wp_rpcDec_t12 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (s0 : GoString)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ s0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match getTag bs with
          | some (s, rest) => ⌜ok = true⌝ ∗ p ↦ s ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ s0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t12)) (Val #b)) (Val #p)) {{ Φ }} := by
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

/-- The pure `rpcDec_t13`. -/
def decBool (bs : List w8) : Option (Bool × List w8) :=
  match bs with
  | [] => none
  | c :: r => if 1 < uint.Z c then none else some (decide (c = W8 1), r)

theorem wp_rpcDec_t13 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : Bool)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decBool bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t13)) (Val #b)) (Val #p)) {{ Φ }} := by
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

theorem wp_rpcDec_t59 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decHdr bs with
          | some rest => ⌜ok = true⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t59)) (Val #b)) (Val #p)) {{ Φ }} := by
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

theorem wp_rpcDec_t61 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decHdr bs with
          | some rest => ⌜ok = true⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t61)) (Val #b)) (Val #p)) {{ Φ }} := by
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

theorem wp_rpcDec_t66 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decHdr bs with
          | some rest => ⌜ok = true⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t66)) (Val #b)) (Val #p)) {{ Φ }} := by
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
    WP (App (Val (@! examples.gryffnet.rpcErrDecode)) (Val #())) {{ Φ }} := by
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

theorem getTag_tagged (t body : List w8) (ht : t.length < 2 ^ 64) :
    getTag (tagged t body) = some (t, body) := by
  unfold tagged; exact getTag_encStr t body ht

theorem dec_PingReply : dec_PingReply.spec (GF := GF) := by
  intro p Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  have hg := getTag_tagged go!"gryff/src/genericsmrproto.PingReply" (strct []) (by decide)
  simp only [encPingReply, hg]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t66 r _ dq p $$ Hr
  iintro %r2 %ok2 H2
  have hd : decHdr (strct []) = some [] := rfl
  simp only [hd]
  icases H2 with ⟨%Hok, Hr2, Hback2⟩
  subst Hok
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
  wp_auto
  ihave Hd := Hback $$ [Hback2 Hr2]
  · iapply Hback2 $$ Hr2
  rw [show r2.len = W64 0 by simp at Hl2; word]
  wp_auto
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ $$ Hp
  simp only [ite_true]
  ipureintro; trivial

theorem dec_BTLReply : dec_BTLReply.spec (GF := GF) := by
  intro p Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  have hg := getTag_tagged go!"gryff/src/genericsmrproto.BeTheLeaderReply" (strct []) (by decide)
  simp only [encBTLReply, hg]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t61 r _ dq p $$ Hr
  iintro %r2 %ok2 H2
  have hd : decHdr (strct []) = some [] := rfl
  simp only [hd]
  icases H2 with ⟨%Hok, Hr2, Hback2⟩
  subst Hok
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
  wp_auto
  ihave Hd := Hback $$ [Hback2 Hr2]
  · iapply Hback2 $$ Hr2
  rw [show r2.len = W64 0 by simp at Hl2; word]
  wp_auto
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ $$ Hp
  simp only [ite_true]
  ipureintro; trivial

theorem decA_BTLArgs : decA_BTLArgs.spec (GF := GF) := by
  intro p Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  have hg := getTag_tagged go!"gryff/src/genericsmrproto.BeTheLeaderArgs" (strct []) (by decide)
  simp only [encBTLArgs, hg]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t59 r _ dq p $$ Hr
  iintro %r2 %ok2 H2
  have hd : decHdr (strct []) = some [] := rfl
  simp only [hd]
  icases H2 with ⟨%Hok, Hr2, Hback2⟩
  subst Hok
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
  wp_auto
  ihave Hd := Hback $$ [Hback2 Hr2]
  · iapply Hback2 $$ Hr2
  rw [show r2.len = W64 0 by simp at Hl2; word]
  wp_auto
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ $$ Hp
  simp only [ite_true]
  ipureintro; trivial


theorem wp_rpcDec_t2 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : w64)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match getU64 bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t2)) (Val #b)) (Val #p)) {{ Φ }} := by
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

theorem ownSlice_lenZS (r : GoSlice) (dq : DFrac) (vs : List GoString) :
    (r ↦*{dq} vs : IProp GF) ⊢ ⌜sint.Z r.len = vs.length ∧ sint.Z r.len ≤ sint.Z r.cap⌝ := by
  iintro Hr
  ihave %Hl := ownSlice_len _ _ _ $$ Hr
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hr
  ipureintro
  refine ⟨?_, Hwf.2⟩
  have h2 : ((sint.Z r.len).toNat : Int) = sint.Z r.len := Int.toNat_of_nonneg Hl.2
  rw [Hl.1, show sint.nat r.len = (sint.Z r.len).toNat from rfl, h2]

def decU8 (bs : List w8) : Option (w8 × List w8) :=
  match getU64 bs with
  | none => none
  | some (x, r) => if uint.Z x < 256 then some (W8 (uint.Z x), r) else none

theorem wp_rpcDec_t64 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : w8)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decU8 bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t64)) (Val #b)) (Val #p)) {{ Φ }} := by
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


def decStrsGo : Nat → List GoString → List w8 → Option (List GoString × List w8)
  | 0, acc, r => some (acc, r)
  | k + 1, acc, r =>
    match getTag r with
    | none => none
    | some (x, r') => decStrsGo k (acc ++ [x]) r'

/-- The pure `rpcDec_t11` (`[]string`). -/
def decStrs (bs : List w8) : Option (List GoString × List w8) :=
  match getU64 bs with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then decStrsGo (uint.nat n) [] r else none

theorem wp_rpcDec_t11 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ slice.nil -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decStrs bs with
          | some (x, rest) => ⌜ok = true⌝ ∗ (∃ sl, p ↦ sl ∗ sl ↦* x) ∗ r ↦*{dq} rest ∗
              (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ sl : GoSlice, p ↦ sl) ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t11)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold decStrs
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
    ihave Hn := ownSlice_nil (V := GoString) (DFrac.own 1)
    ihave Hs : (slice.slice slice.nil GoString (W64 0) x ↦* List.replicate (uint.nat x) (go!"" : GoString)) $$ [Hn]
    · subst hx0
      icases (ownSlice_slice (V := GoString) (W64 0) (W64 0) slice.nil (DFrac.own 1) []
        ⟨by decide, by decide, by decide⟩).1 $$ Hn with ⟨-, Hs, -⟩
      have e : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) ([] : List GoString) =
          List.replicate (uint.nat (W64 0)) (go!"" : GoString) := by simp [subslice]
      rw [e]
      iexact Hs
    generalize slice.slice slice.nil GoString (W64 0) x = sl at *
    iclear Hn
    rotate_left
    rw [decide_eq_true (show uint.Z (0 : w64) < uint.Z x by
      have : uint.Z x ≠ 0 := fun h => hx0 (by word)
      have : (0 : Int) ≤ uint.Z x := by word
      show (0 : Int) < uint.Z x
      omega)]
    wp_auto
    wp_apply wp_slice_make2 (V := GoString) x
    · ipureintro; word
    iintro %sl ⟨Hs, -⟩
    rw [show sint.nat x = uint.nat x by word, show zero_val GoString = (go!"" : GoString) from rfl]
    wp_auto
    rotate_left
    all_goals
      ihave %hsl := ownSlice_lenZS _ _ _ $$ Hs
      simp only [List.length_replicate] at hsl
      ihave HI : (∃ (i : w64) (R : GoSlice) (acc : List GoString) (cur : List w8),
          "i" ∷ i_ptr ↦ i ∗ "r" ∷ r_ptr ↦ R ∗ "ok" ∷ ok_ptr ↦ true ∗ "Hr" ∷ R ↦*{dq} cur ∗
          "Hback" ∷ (R ↦*{dq} cur -∗ b ↦*{dq} bs) ∗
          "Hs" ∷ sl ↦* (acc ++ List.replicate (uint.nat x - uint.nat i) (go!"" : GoString)) ∗
          "%Hi" ∷ ⌜acc.length = uint.nat i ∧ uint.nat i ≤ uint.nat x ∧
            decStrsGo (uint.nat x - uint.nat i) acc cur = decStrsGo (uint.nat x) [] rest⌝ : IProp GF)
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
        have hlk : (acc ++ List.replicate (uint.nat x - uint.nat i) (go!"" : GoString))[(sint.Z i).toNat]? =
            some (go!"" : GoString) := by
          rw [show (sint.Z i).toNat = acc.length by word, hk]
          simp
        icases ownSlice_elem_acc (sint.Z i) (go!"" : GoString) sl _ _ (by word) hlk $$ Hs with ⟨He, Hs⟩
        wp_apply wp_rpcDec_t12 R cur dq _ _ $$ Hr He
        iintro %R2 %ok2 Hd
        rcases hd : getTag cur with _ | ⟨v, cur2⟩
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
          have hres : decStrsGo (uint.nat x) [] rest = none := by
            rw [← Hi.2.2, hk]; simp [decStrsGo, hd]
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
          have hset : (acc ++ List.replicate (uint.nat x - uint.nat i) (go!"" : GoString)).set (sint.Z i).toNat v =
              (acc ++ [v]) ++ List.replicate (uint.nat x - uint.nat (i + W64 1)) (go!"" : GoString) := by
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
          simp [decStrsGo, hd]
      · (try wp_auto)
        have hix : uint.nat x - uint.nat i = 0 := by
          have : ¬ uint.Z i < uint.Z x := by
            first | exact Hif | exact fun h => Hif (by simp [h])
          word
        have hres : decStrsGo (uint.nat x) [] rest = some (acc, cur) := by
          rw [← Hi.2.2, hix]; rfl
        iapply HΦ
        rw [hres]
        dsimp only
        rw [hix, List.replicate_zero, List.append_nil]
        iframe
        ipureintro; rfl


/-- A struct field whose decoder's result is kept apart: not sent (`none`) or sent and decoded. -/
def decFldO {α : Type} (d : List w8 → Option (α × List w8)) (bs : List w8) :
    Option (Option α × List w8) :=
  match bs with
  | [] => none
  | c :: r => if 1 < uint.Z c then none else if c = W8 1 then (d r).map (fun x => (some x.1, x.2))
    else some (none, r)

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
  simp only [$D:ident, decHdr, decFld, decFldO, Option.map, ↓reduceIte, *]
  iframe
  (try first | iexists _, _, _, _, _ | iexists _, _, _ | iexists _, _ | iexists _)
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


/-- The pure `rpcDec_t15` (`RegisterArgs`), into `{a0, p0}`. -/
def decRA (a0 : GoString) (p0 : w64) (bs : List w8) : Option ((GoString × w64) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld getTag a0 r with
    | none => none
    | some (a, r) =>
      match decFld getU64 p0 r with
      | none => none
      | some (v, r) => some ((a, v), r)

theorem wp_rpcDec_t15 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (a0 : GoString) (p0 : w64)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ src.masterproto.RegisterArgs.mk a0 p0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decRA a0 p0 bs with
          | some ((a, v), rest) => ⌜ok = true⌝ ∗ p ↦ src.masterproto.RegisterArgs.mk a v ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ a v, p ↦ src.masterproto.RegisterArgs.mk a v) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t15)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decRA
  all_goals fld_step wp_rpcDec_t12 getTag Addr fail struct_close decRA
  all_goals fld_step wp_rpcDec_t2 getU64 Port fail struct_close decRA
  all_goals ((try wp_auto); struct_close decRA)

/-- The pure `rpcDec_t63` (`PingArgs`), into `{a0}`. -/
def decPA (a0 : w8) (bs : List w8) : Option (w8 × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld decU8 a0 r with
    | none => none
    | some (a, r) => some (a, r)

set_option hygiene false in
macro "pa_close" : tactic => `(tactic| (
  iapply HΦ
  simp only [decPA, decHdr, decFld, ↓reduceIte, *]
  iframe
  first
  | (iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
))

theorem wp_rpcDec_t63 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (a0 : w8)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ src.genericsmrproto.PingArgs.mk a0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decPA a0 bs with
          | some (a, rest) => ⌜ok = true⌝ ∗ p ↦ src.genericsmrproto.PingArgs.mk a ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ a, p ↦ src.genericsmrproto.PingArgs.mk a) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t63)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decPA
  all_goals fld_step wp_rpcDec_t64 decU8 ActAsLeader fail pa_close
  all_goals ((try wp_auto); pa_close)

/-- The pure `rpcDec_t17` (`RegisterReply`), into `{id0, nil, rd0}` (`NodeList` kept apart: not
sent, it stays `nil`). -/
def decRR (id0 : w64) (rd0 : Bool) (bs : List w8) :
    Option ((w64 × Option (List GoString) × Bool) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld getU64 id0 r with
    | none => none
    | some (i, r) =>
      match decFldO decStrs r with
      | none => none
      | some (nl, r) =>
        match decFld decBool rd0 r with
        | none => none
        | some (rd, r) => some ((i, nl, rd), r)

set_option hygiene false in
macro "rr_close" : tactic => `(tactic| (
  iapply HΦ
  simp only [decRR, decHdr, decFld, decFldO, Option.map, ↓reduceIte, *]
  iframe
  first
  | (icases NodeList with ⟨%sl, NodeList, Hsl⟩
     iexists sl
     iframe Hsl
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (icases NodeList with ⟨%sl, NodeList, -⟩
     iexists _, _, _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (icases NodeList with ⟨%sl, NodeList⟩
     iexists _, _, _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists _, _, _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)))

theorem wp_rpcDec_t17 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (id0 : w64) (rd0 : Bool)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ src.masterproto.RegisterReply.mk id0 slice.nil rd0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decRR id0 rd0 bs with
          | some ((i, none, rd), rest) => ⌜ok = true⌝ ∗
              p ↦ src.masterproto.RegisterReply.mk i slice.nil rd ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | some ((i, some x, rd), rest) => ⌜ok = true⌝ ∗
              (∃ sl, p ↦ src.masterproto.RegisterReply.mk i sl rd ∗ sl ↦* x) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ i sl rd, p ↦ src.masterproto.RegisterReply.mk i sl rd) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.gryffnet.rpcDec_t17)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decRR
  all_goals fld_step wp_rpcDec_t2 getU64 ReplicaId fail rr_close
  all_goals fld_step wp_rpcDec_t11 decStrs NodeList fail rr_close
  all_goals fld_step wp_rpcDec_t13 decBool Ready fail rr_close
  all_goals ((try wp_auto); rr_close)



/-! ### Round trips -/

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
  · intro _; exact getTag_encStr k rest hk

theorem decFld_fU64 (v : w64) (rest : List w8) :
    decFld getU64 (W64 0) (fU64 v ++ rest) = some (v, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact getU64_enc v rest

theorem decU8_enc (c : w8) (rest : List w8) :
    decU8 (u64Le (W64 (uint.Z c)) ++ rest) = some (c, rest) := by
  unfold decU8
  rw [getU64_enc]
  have h1 : uint.Z (W64 (uint.Z c)) < 256 := by word
  have h2 : W8 (uint.Z (W64 (uint.Z c))) = c := by word
  simp only [h1, ↓reduceIte, h2]

theorem decFld_fU8 (a : w8) (rest : List w8) :
    decFld decU8 (W8 0) (fU8 a ++ rest) = some (a, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact decU8_enc a rest

theorem decBool_enc (x : Bool) (rest : List w8) : decBool (encBool x ++ rest) = some (x, rest) := by
  cases x <;> simp [decBool, encBool, show uint.Z (W8 1) = 1 from rfl,
    show uint.Z (W8 0) = 0 from rfl] <;> decide

theorem decFld_fBool (x : Bool) (rest : List w8) :
    decFld decBool false (fBool x ++ rest) = some (x, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact decBool_enc x rest

theorem decStrsGo_enc (l : List GoString) (acc : List GoString) (rest : List w8)
    (hl : ∀ s ∈ l, s.length < 2 ^ 64) :
    decStrsGo l.length acc ((l.map encStr).flatten ++ rest) = some (acc ++ l, rest) := by
  induction l generalizing acc with
  | nil => simp [decStrsGo]
  | cons s l ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decStrsGo,
      getTag_encStr s _ (hl s (by simp)), ih (acc ++ [s]) (fun t ht => hl t (by simp [ht]))]
    simp

theorem len_le_flatten_encStr (l : List GoString) :
    l.length ≤ (l.map encStr).flatten.length ∧ ∀ s ∈ l, s.length ≤ (l.map encStr).flatten.length := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons, encStr,
      u64Le_length, List.mem_cons]
    refine ⟨by omega, ?_⟩
    rintro t (rfl | ht)
    · omega
    · have := ih.2 t ht; omega

theorem decStrs_enc (l : List GoString) (rest : List w8) (hl : l.length < 2 ^ 64)
    (hs : ∀ s ∈ l, s.length < 2 ^ 64) : decStrs (encStrs l ++ rest) = some (l, rest) := by
  unfold decStrs encStrs
  rw [List.append_assoc, getU64_enc]
  have hn : uint.nat (W64 l.length) = l.length := by
    show (BitVec.ofNat 64 l.length).toNat = l.length
    simp only [BitVec.toNat_ofNat]; omega
  have hle : l.length ≤ ((l.map encStr).flatten ++ rest).length := by
    have := (len_le_flatten_encStr l).1
    simp only [List.length_append]; omega
  simp only [hn, hle, ↓reduceIte, decStrsGo_enc l [] rest hs, List.nil_append]

theorem decFldO_fStrs (l : List GoString) (rest : List w8) (hl : l.length < 2 ^ 64)
    (hs : ∀ s ∈ l, s.length < 2 ^ 64) :
    decFldO decStrs (fStrs l ++ rest) = some (if l = [] then none else some l, rest) := by
  by_cases h : l = []
  · subst h
    simp [fStrs, fld, decFldO, show uint.Z (W8 0) = 0 from rfl]
    decide
  · simp only [fStrs, fld, ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte, List.cons_append,
      decFldO]
    simp [show uint.Z (W8 1) = 1 from rfl, decStrs_enc l rest hl hs, h]
    decide

theorem decRA_enc (a : GoString) (v : w64) (ha : a.length < 2 ^ 64) :
    decRA go!"" (W64 0) (strct [fStr a, fU64 v]) = some ((a, v), []) := by
  have e : strct [fStr a, fU64 v] = W8 1 :: (fStr a ++ (fU64 v ++ [])) := by simp [strct]
  rw [e]
  simp only [decRA, decHdr, ↓reduceIte, decFld_fStr a _ ha, decFld_fU64]

theorem decPA_enc (a : w8) : decPA (W8 0) (strct [fU8 a]) = some (a, []) := by
  have e : strct [fU8 a] = W8 1 :: (fU8 a ++ []) := by simp [strct]
  rw [e]
  simp only [decPA, decHdr, ↓reduceIte, decFld_fU8]

theorem decRR_enc (i : w64) (l : List GoString) (rd : Bool) (hl : l.length < 2 ^ 64)
    (hs : ∀ s ∈ l, s.length < 2 ^ 64) :
    decRR (W64 0) false (strct [fU64 i, fStrs l, fBool rd]) =
      some ((i, if l = [] then none else some l, rd), []) := by
  have e : strct [fU64 i, fStrs l, fBool rd] = W8 1 :: (fU64 i ++ (fStrs l ++ (fBool rd ++ []))) := by
    simp [strct]
  rw [e]
  simp only [decRR, decHdr, ↓reduceIte, decFld_fU64, decFldO_fStrs l _ hl hs, decFld_fBool]

theorem len_fStr (k : GoString) : k.length ≤ (fStr k).length := by
  by_cases hk : k = []
  · simp [hk]
  · simp [fStr, fld, hk, encStr]; omega

theorem len_fStrs (l : List GoString) :
    l.length ≤ (fStrs l).length ∧ ∀ s ∈ l, s.length ≤ (fStrs l).length := by
  by_cases hl : l = []
  · subst hl; simp
  · have := len_le_flatten_encStr l
    simp only [fStrs, fld, ne_eq, hl, not_false_eq_true, decide_true, ↓reduceIte, List.length_cons,
      encStrs, List.length_append, u64Le_length]
    exact ⟨by omega, fun s hs => by have := this.2 s hs; omega⟩

set_option hygiene false in
/-- The end of a top-level decoding: the data back, nothing left, `nil`. -/
macro "dec_done" : tactic => `(tactic| (
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
  wp_auto
  ihave Hd := Hback $$ [Hback2 Hr2]
  · iapply Hback2 $$ Hr2
  rw [show r2.len = W64 0 by simp at Hl2; word]
  wp_auto))

theorem decA_RegisterArgs : decA_RegisterArgs.spec (GF := GF) := by
  intro p addr port Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have ha : addr.length < 2 ^ 64 := by
    have h3 : sint.Z data.len < 2 ^ 63 := by word
    have h1 := len_fStr addr
    have h2 : (fStr addr).length ≤ (encRegArgs addr port).length := by
      simp [encRegArgs, tagged, strct]; omega
    omega
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  have hg := getTag_tagged go!"gryff/src/masterproto.RegisterArgs" (strct [fStr addr, fU64 port])
    (by decide)
  simp only [encRegArgs, hg]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t15 r _ dq p _ _ $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [decRA_enc addr port ha]
  icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
  subst Hok
  dec_done
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ $$ Hp
  simp only [ite_true]
  ipureintro; trivial

theorem decA_PingArgs : decA_PingArgs.spec (GF := GF) := by
  intro p a Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  have hg := getTag_tagged go!"gryff/src/genericsmrproto.PingArgs" (strct [fU8 a]) (by decide)
  simp only [encPingArgs, hg]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t63 r _ dq p _ $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [decPA_enc a]
  icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
  subst Hok
  dec_done
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ $$ Hp
  simp only [ite_true]
  ipureintro; trivial

theorem dec_RegisterReply : dec_RegisterReply.spec (GF := GF) := by
  intro p id nodes ready Ψ
  iintro ⟨Hp, HΨ⟩
  unfold gryffCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have hb : nodes.length < 2 ^ 64 ∧ ∀ s ∈ nodes, s.length < 2 ^ 64 := by
    have h3 : sint.Z data.len < 2 ^ 63 := by word
    have h1 := len_fStrs nodes
    have h2 : (fStrs nodes).length ≤ (encRegReply id nodes ready).length := by
      simp [encRegReply, tagged, strct]; omega
    exact ⟨by omega, fun s hs => by have := h1.2 s hs; omega⟩
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  have hg := getTag_tagged go!"gryff/src/masterproto.RegisterReply"
    (strct [fU64 id, fStrs nodes, fBool ready]) (by decide)
  simp only [encRegReply, hg]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t17 r _ dq p _ _ $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [decRR_enc id nodes ready hb.1 hb.2]
  by_cases hn : nodes = []
  · simp only [hn, ↓reduceIte]
    icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
    subst Hok
    dec_done
    iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
    · iapply HΨ $$ Hp
      simp only [↓reduceIte]
      ipureintro; trivial
    simp only [ite_true]
    ipureintro; trivial
  · simp only [hn, ↓reduceIte]
    icases H2 with ⟨%Hok, ⟨%sl, Hp, Hsl⟩, Hr2, Hback2⟩
    subst Hok
    dec_done
    iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp Hsl]
    · iapply HΨ $$ Hp
      (try simp only [hn, ↓reduceIte])
      iexact Hsl
    simp only [ite_true]
    ipureintro; trivial

theorem gryffCodecLaws : CodecLaws (GF := GF) where
  enc_RegisterArgs := enc_RegisterArgs
  enc_PingArgs := enc_PingArgs
  enc_BTLArgs := enc_BTLArgs
  dec_RegisterReply := dec_RegisterReply
  dec_PingReply := dec_PingReply
  dec_BTLReply := dec_BTLReply
  decA_RegisterArgs := decA_RegisterArgs
  decA_PingArgs := decA_PingArgs
  decA_BTLArgs := decA_BTLArgs
  enc_RegisterReply := enc_RegisterReply
  enc_PingReply := enc_PingReply
  enc_BTLReply := enc_BTLReply

end proof

/-! ## The receivers -/

section rcvproof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [net.rpc.Assumptions] [π : NetProtoGS]
variable [examples.gryffnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

theorem gryffCodec_rcv_eq (rcvr : GoInterface) (Ψ : Loc → IProp GF) :
    (gryffCodec (hG := hG)).rcv rcvr Ψ = iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
      WP (App (Val #(functions examples.gryffnet.rpcReceiver [])) (Val #rcvr)) {{ Φ }}) := rfl

theorem newArg_GetLeader : newArg_GetLeader.spec (GF := GF) := by
  intro rcvr Sm hS
  iintro #Hcs
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mGetLeader, mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  have hne : ptrIface src.masterproto.GetLeaderArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  iapply HΨ $$ %_ %iprop(True) %(fun _ _ => iprop(True)) %hne [] []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro - %args %Φ HS
    iexfalso
    iapply (hS args Φ) $$ HS
  · itrivial
  iintro %args %Φ HS -
  iexfalso
  iapply (hS args Φ) $$ HS

theorem newArg_GetReplicaList : newArg_GetReplicaList.spec (GF := GF) := by
  intro rcvr Sm hS
  iintro #Hcs
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mGetReplicaList, mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  have hne : ptrIface src.masterproto.GetReplicaListArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  iapply HΨ $$ %_ %iprop(True) %(fun _ _ => iprop(True)) %hne [] []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro - %args %Φ HS
    iexfalso
    iapply (hS args Φ) $$ HS
  · itrivial
  iintro %args %Φ HS -
  iexfalso
  iapply (hS args Φ) $$ HS

theorem rcv_Master : rcv_Master.spec (GF := GF) := by
  intro mp S Hnn
  iintro ⟨#N0, #N1, #N2⟩
  rw [gryffCodec_rcv_eq]
  iintro %Φ HΦ
  iapply wp_fupd
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) _ _) as %mpp Hm
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m0 as H0
  ipersist H0
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m1 as H1
  ipersist H1
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m2 as H2
  ipersist H2
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  ipersist «$r0»
  imod ownMap_persist $$ Hm with #Hm
  iapply HΦ
  unfold net.rpc.rcvrIs
  iexists _, _
  iframe «$r0» Hm
  isplitr
  · ipureintro
    refine ⟨rfl, ?_, ?_⟩
    · simp [Hnn]
    · exact GMap.map_size_ne_0_lookup_2 _ (GMap.lookup_insert _ _ _)
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk gryffCodec
    (ptrIface src.masterlib.Master.ty mp) (S m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H2
    iexact N2
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk gryffCodec
    (ptrIface src.masterlib.Master.ty mp) (S m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H1
    iexact N1
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk gryffCodec
    (ptrIface src.masterlib.Master.ty mp) (S m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H0
    iexact N0
  iapply BI.BigSepM.bigSepM_empty.2
  itrivial

theorem rcv_Replica : rcv_Replica.spec (GF := GF) := by
  intro mp S Hnn
  iintro ⟨#N0, #N1⟩
  rw [gryffCodec_rcv_eq]
  iintro %Φ HΦ
  iapply wp_fupd
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) _ _) as %mpp Hm
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m0 as H0
  ipersist H0
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  wp_alloc m1 as H1
  ipersist H1
  repeat (first | (wp_apply wp_mapInsert $$ Hm as Hm) | wp_auto)
  ipersist «$r0»
  imod ownMap_persist $$ Hm with #Hm
  iapply HΦ
  unfold net.rpc.rcvrIs
  iexists _, _
  iframe «$r0» Hm
  isplitr
  · ipureintro
    refine ⟨rfl, ?_, ?_⟩
    · simp [Hnn]
    · exact GMap.map_size_ne_0_lookup_2 _ (GMap.lookup_insert _ _ _)
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk gryffCodec
    (ptrIface src.gryff.Replica.ty mp) (S m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H1
    iexact N1
  iapply (BI.BigSepM.bigSepM_insert (Φ := fun m mm => net.rpc.methodOk gryffCodec
    (ptrIface src.gryff.Replica.ty mp) (S m) mm) ?_).2
  · first | rfl | decide | simp
  isplitr
  · iapply methodOk_of
    iframe H0
    iexact N0
  iapply BI.BigSepM.bigSepM_empty.2
  itrivial

theorem gryffRcvLaws : RcvLaws (GF := GF) where
  rcv_Master := rcv_Master
  rcv_Replica := rcv_Replica
  newArg_GetLeader := newArg_GetLeader
  newArg_GetReplicaList := newArg_GetReplicaList


end rcvproof


end Perennial.gryff
