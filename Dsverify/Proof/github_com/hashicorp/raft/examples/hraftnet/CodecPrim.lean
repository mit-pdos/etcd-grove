/-
The hraft kit's generated codec (`examples/hraftnet/rpc_gen.go`): the helpers and the encoders and
decoders of its basic types (`uint64`, `int64`, `uint8`, `bool`, `string`, `[]byte`, raft's
`ProtocolVersion`, `SnapshotVersion`, `LogType`), as craq's (`Craq/CodecProof.lean`, the same
generated code): an encoder appends the encoding of `CodecDefs.lean`'s, a decoder computes its pure
decoder.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecDefs
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

namespace github_com.hashicorp.raft.examples.hraftnet

open rpctransport

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

/-! ## Encoding -/

/-- `rpcPutU64(b, x)`: `b` with `x`'s 8 bytes (little-endian) appended. -/
theorem wp_rpcPutU64 (b : GoSlice) (bs : List w8) (x : w64) :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! rpcPutU64)) (Val #b)) (Val #x))
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

theorem wp_rpcEnc_t8 (x : w64) : encFn (GF := GF) rpcEnc_t8 #x (encU64 x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t5 (x : w64) : encFn (GF := GF) rpcEnc_t5 #x (encU64 x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t18 (x : w64) : encFn (GF := GF) rpcEnc_t18 #x (encU64 x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t19 (x : w64) : encFn (GF := GF) rpcEnc_t19 #x (encU64 x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t7 (x : w8) :
    encFn (GF := GF) rpcEnc_t7 #x (encU64 (W64 (uint.Z x))) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t11 (x : w8) :
    encFn (GF := GF) rpcEnc_t11 #x (encU64 (W64 (uint.Z x))) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t14 (x : Bool) : encFn (GF := GF) rpcEnc_t14 #x (encBool x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  cases x
  · wp_auto
    wp_apply wp_slice_literal (V := w8) [W8 0]
    isplitr
    · ipureintro; first | rfl | trivial
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iframe
  · wp_auto
    wp_apply wp_slice_literal (V := w8) [W8 1]
    isplitr
    · ipureintro; first | rfl | trivial
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iframe

theorem wp_rpcEnc_t15 (s : GoString) :
    encFn (GF := GF) rpcEnc_t15 #s (rpctransport.encStr s) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_string_len s as %Hlen
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  wp_apply wp_string_to_bytes s as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, -⟩
  iapply HΦ
  unfold rpctransport.encStr
  rw [List.append_assoc]
  iframe

set_option hygiene false in
/-- `rpcSent` of a `uint64`-like type. -/
macro "sent_u64_proof" : tactic => `(tactic| (
  wp_start
  wp_auto
  rw [show (!decide (x = W64 0)) = decide (x ≠ W64 0) by simp]
  iapply HΦ
  ipureintro; trivial))

theorem wp_rpcSent_t8 (x : w64) :
    {{ (True : IProp GF) }} (App (Val (@! rpcSent_t8)) (Val #x))
    {{ RET #(decide (x ≠ W64 0)); True }} := by
  sent_u64_proof

theorem wp_rpcSent_t5 (x : w64) :
    {{ (True : IProp GF) }} (App (Val (@! rpcSent_t5)) (Val #x))
    {{ RET #(decide (x ≠ W64 0)); True }} := by
  sent_u64_proof

theorem wp_rpcSent_t18 (x : w64) :
    {{ (True : IProp GF) }} (App (Val (@! rpcSent_t18)) (Val #x))
    {{ RET #(decide (x ≠ W64 0)); True }} := by
  sent_u64_proof

theorem wp_rpcSent_t19 (x : w64) :
    {{ (True : IProp GF) }} (App (Val (@! rpcSent_t19)) (Val #x))
    {{ RET #(decide (x ≠ W64 0)); True }} := by
  sent_u64_proof

theorem wp_rpcSent_t11 (x : w8) :
    {{ (True : IProp GF) }} (App (Val (@! rpcSent_t11)) (Val #x))
    {{ RET #(decide (x ≠ W8 0)); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (x = W8 0)) = decide (x ≠ W8 0) by simp]
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t14 (x : Bool) :
    {{ (True : IProp GF) }} (App (Val (@! rpcSent_t14)) (Val #x))
    {{ RET #x; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t15 (s : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! rpcSent_t15)) (Val #s))
    {{ RET #(decide (s ≠ [])); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (s = [])) = decide (s ≠ []) by simp]
  iapply HΦ
  ipureintro; trivial

/-- `rpcSent` of a slice: its length is not `0`. -/
theorem sent_len {V : Type} (sl : GoSlice) (x : List V) (Hl : x.length = sint.nat sl.len ∧ 0 ≤ sint.Z sl.len) :
    (!decide (sl.len = W64 0)) = decide (x ≠ []) := by
  by_cases hx : x = []
  · subst hx
    have : sl.len = W64 0 := by simp at Hl; word
    simp [this]
  · have : x.length ≠ 0 := by simpa using hx
    have : sl.len ≠ W64 0 := by
      intro h0; rw [h0] at Hl; exact absurd (Hl.1.trans (by rfl)) this
    simp only [hx, this, decide_false, decide_true, Bool.not_false, ne_eq, not_false_eq_true]

theorem wp_rpcSent_t6 (sl : GoSlice) (dq : DFrac) (x : List w8) :
    {{ (sl ↦*{dq} x : IProp GF) }} (App (Val (@! rpcSent_t6)) (Val #sl))
    {{ RET #(decide (x ≠ [])); sl ↦*{dq} x }} := by
  wp_start as Hsl
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  rw [sent_len sl x Hl]
  iapply HΦ $$ Hsl

theorem wp_rpcSent_t9 (sl : GoSlice) (dq : DFrac) (x : List Entry) :
    {{ (sl ↦*{dq} x : IProp GF) }} (App (Val (@! rpcSent_t9)) (Val #sl))
    {{ RET #(decide (x ≠ [])); sl ↦*{dq} x }} := by
  wp_start as Hsl
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  rw [sent_len sl x Hl]
  iapply HΦ $$ Hsl

theorem wp_rpcEnc_t6 (sl : GoSlice) (dq : DFrac) (x : List w8) :
    encFn (GF := GF) rpcEnc_t6 #sl (encBytes x) iprop(sl ↦*{dq} x) := by
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
    wp_apply wp_rpcEnc_t7 e _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, b2, e
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
      List.take_add_one, He_lookup, Option.toList_some, List.map_append, List.flatten_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      ← List.append_assoc, encU64]
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

/-- `rpcPutTag(tag)`: a new slice, the string `tag`'s encoding. -/
theorem wp_rpcPutTag (tag : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! rpcPutTag)) (Val #tag))
    {{ (b : GoSlice), RET #b; b ↦* rpctransport.encStr tag ∗ ownSliceCap w8 b (DFrac.own 1) }} := by
  wp_start
  wp_auto
  wp_apply wp_string_len tag as %Hlen
  ihave Hn := ownSlice_nil (V := w8) (DFrac.own 1)
  ihave Hnc := ownSliceCap_nil (V := w8)
  wp_apply wp_rpcPutU64 $$ [$Hn $Hnc] as %b1 ⟨Hb, Hcap⟩
  wp_apply wp_string_to_bytes tag as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, -⟩
  iapply HΦ
  unfold rpctransport.encStr
  iframe

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

theorem wp_rpcGetU64 (b : GoSlice) (bs : List w8) (dq : DFrac) (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (x : w64) (r : GoSlice) (ok : Bool),
        (match getU64 bs with
          | some (x', rest) => ⌜ok = true ∧ x = x'⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV (PairV #x #r) #ok)) -∗
    WP (App (Val (@! rpcGetU64)) (Val #b)) {{ Φ }} := by
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
    ipureintro; first | rfl | trivial
  · have hb8 : 8 ≤ sint.Z b.len := by omega
    rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 8) by
      rw [show sint.Z (W64 8) = 8 from rfl]; omega)]
    rcases bs with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      try (simp at h8; done)
    wp_auto
    iterate 8
      rw [ite_eq_left (show _ ∧ _ by constructor <;> word)]
      wp_apply wp_load_slice_index b _ _ dq _ (by decide) $$ [Hb] with Hb
      · iframe; ipureintro; first | rfl | trivial
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

set_option hygiene false in
/-- The tail of a `getTag`-like proof (`rpcGetTag`, the `string` decoder), after `rpcGetU64`. -/
macro "tag_tail" : tactic => `(tactic| (
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
    · ipureintro; first | exact ⟨rfl, rfl⟩ | rfl
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
    · ipureintro; first | rfl | trivial
    iapply Hback $$ Hr))

theorem wp_rpcGetTag (b : GoSlice) (bs : List w8) (dq : DFrac) (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (t : GoString) (r : GoSlice) (ok : Bool),
        (match getTag bs with
          | some (t', rest) => ⌜ok = true ∧ t = t'⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV (PairV #t #r) #ok)) -∗
    WP (App (Val (@! rpcGetTag)) (Val #b)) {{ Φ }} := by
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
    ipureintro; first | rfl | trivial
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    tag_tail

/-- The shape of a decoder's spec: `f(b, p)` decodes `b`'s bytes with the pure decoder `D` into
`p` (from `p ↦ v0`): on success, `O p v` of the value `v`, and the rest of the bytes. -/
abbrev decFn {T α : Type} [TypedPointsto (GF := GF) T] (f : GoString) (D : List w8 → Option (α × List w8))
    (v0 : T) (O : Loc → α → IProp GF) : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (Φ : val → IProp GF),
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match D bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ O p v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! f)) (Val #b)) (Val #p)) {{ Φ }}

theorem wp_rpcDec_t15 : decFn (GF := GF) rpcDec_t15 getTag ([] : GoString) (fun p s => p ↦ s) := by
  intro b bs dq p Φ
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
    ipureintro; first | rfl | trivial
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
      · ipureintro; first | rfl | trivial
      iintro Hd
      iapply Hback
      iapply (ownSlice_split_all x r dq rest hk).2
      rw [show sint.nat x = uint.nat x by word]
      iframe
    · rw [decide_eq_true (show uint.Z r.len < uint.Z x by word)]
      wp_auto
      iapply HΦ
      rw [if_neg hn]
      ipureintro; first | rfl | trivial

set_option hygiene false in
/-- A decoder of a `uint64`-like type: `rpcGetU64` and a range check that holds. -/
macro "dec_u64_proof" : tactic => `(tactic| (
  intro b bs dq p Φ
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
    ipureintro; first | rfl | trivial
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; first | rfl | trivial))

theorem wp_rpcDec_t8 : decFn (GF := GF) rpcDec_t8 getU64 (W64 0) (fun p x => p ↦ x) := by
  dec_u64_proof

theorem wp_rpcDec_t5 : decFn (GF := GF) rpcDec_t5 getU64 (W64 0) (fun p x => p ↦ x) := by
  dec_u64_proof

theorem wp_rpcDec_t18 : decFn (GF := GF) rpcDec_t18 getU64 (W64 0) (fun p x => p ↦ x) := by
  dec_u64_proof

theorem wp_rpcDec_t19 : decFn (GF := GF) rpcDec_t19 getU64 (W64 0) (fun p x => p ↦ x) := by
  dec_u64_proof

set_option hygiene false in
/-- A decoder of a `uint8`-like type. -/
macro "dec_u8_proof" : tactic => `(tactic| (
  intro b bs dq p Φ
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
    ipureintro; first | rfl | trivial
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
      ipureintro; first | rfl | trivial
    · rw [decide_eq_false (show ¬ W64 (uint.Z (W8 (uint.Z x))) = x by
        intro h; apply hx; rw [← h]; word)]
      wp_auto
      iapply HΦ
      rw [if_neg hx]
      ipureintro; first | rfl | trivial))

theorem wp_rpcDec_t7 : decFn (GF := GF) rpcDec_t7 decU8 (W8 0) (fun p x => p ↦ x) := by
  dec_u8_proof

theorem wp_rpcDec_t11 : decFn (GF := GF) rpcDec_t11 decU8 (W8 0) (fun p x => p ↦ x) := by
  dec_u8_proof

theorem wp_rpcDec_t14 : decFn (GF := GF) rpcDec_t14 decBool false (fun p x => p ↦ x) := by
  intro b bs dq p Φ
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
    ipureintro; first | rfl | trivial
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
    · iframe; ipureintro; first | rfl | trivial
    by_cases hc : 1 < uint.Z c
    · rw [decide_eq_true (show uint.Z (W8 1) < uint.Z c from hc)]
      wp_auto
      iapply HΦ
      simp only [decBool, if_pos hc]
      ipureintro; first | rfl | trivial
    · rw [decide_eq_false (show ¬ uint.Z (W8 1) < uint.Z c from hc)]
      wp_auto
      rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len by
        rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
      wp_apply wp_load_slice_index b _ _ dq _ (by decide) $$ [Hb] with Hb
      · iframe; ipureintro; first | rfl | trivial
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

/-- `rpcErrDecode()`: a decoding error. -/
theorem wp_rpcErrDecode (Φ : val → IProp GF) :
    ▷ (∀ e : GoInterface, net.rpc.decErr e -∗ Φ #e) -∗
    WP (App (Val (@! rpcErrDecode)) (Val #())) {{ Φ }} := by
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

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
