/-
The kit's generated codec (`examples/epaxosnet/rpc_gen.go`) meets the clients' codec lemmas of
`NetRpc/Codec.lean` (`epCodecLaws`): the encoders' bytes are `Wire.lean`'s, and decoding a reply
is safe and, on success, gives back an encoding's value. As dsv-craq's `Craq/CodecProof.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Codec
public import Net.Proof.net.rpc.Errs
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
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [examples.epaxosnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

/-! ## Encoding -/

/-- `rpcPutU64(b, x)`: `b` with `x`'s 8 bytes (little-endian) appended. -/
theorem wp_rpcPutU64 (b : GoSlice) (bs : List w8) (x : w64) :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! examples.epaxosnet.rpcPutU64)) (Val #b)) (Val #x))
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

theorem wp_rpcEnc_t14 (s : GoString) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t14 #s (encStr s) iprop(True) := by
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

theorem wp_rpcEnc_t4 (x : w64) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t4 #x (encU64 x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t66 (x : w8) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t66 #x (encU8 x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcSent_t14 (s : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! examples.epaxosnet.rpcSent_t14)) (Val #s))
    {{ RET #(decide (s ≠ [])); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (s = [])) = decide (s ≠ []) by simp]
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t4 (x : w64) :
    {{ (True : IProp GF) }} (App (Val (@! examples.epaxosnet.rpcSent_t4)) (Val #x))
    {{ RET #(decide (x ≠ W64 0)); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (x = W64 0)) = decide (x ≠ W64 0) by simp]
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t66 (x : w8) :
    {{ (True : IProp GF) }} (App (Val (@! examples.epaxosnet.rpcSent_t66)) (Val #x))
    {{ RET #(decide (x ≠ W8 0)); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (x = W8 0)) = decide (x ≠ W8 0) by simp]
  iapply HΦ
  ipureintro; trivial

set_option hygiene false in
/-- The last step of a struct encoder's proof: its bytes are `Wire.lean`'s. -/
macro "enc_close" : tactic => `(tactic| (
  iapply HΦ
  isimp only [strct, fld, fStr, fInt, fBool, fI32, fU8, fStrs, fBools, encBool, List.flatten_cons,
    List.flatten_nil, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    List.append_nil, decide_true, decide_false, ne_eq, not_true_eq_false, not_false_eq_true,
    ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, *]
  (try isimp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at Hb)
  iframe))

theorem wp_rpcEnc_t18 (a : GoString) (port : w64) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t18 #(replica.defs.RegisterArgs.mk a port)
      (strct [fStr a, fInt port]) iprop(True) := by
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
    wp_apply wp_rpcSent_t14 a
    by_cases h1 : a = [] <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t14 a _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t4 port
    by_cases h2 : port = W64 0 <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t4 port _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t84 :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t84 #replica.defs.BeTheLeaderArgs.mk
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

theorem wp_rpcEnc_t88 (a : w8) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t88 #(replica.defs.PingArgs.mk a)
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
    wp_apply wp_rpcSent_t66 a
    by_cases h1 : a = W8 0 <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t66 a _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    enc_close)

/-- `rpcPutTag(tag)`: a new slice, the string `tag`'s encoding. -/
theorem wp_rpcPutTag (tag : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! examples.epaxosnet.rpcPutTag)) (Val #tag))
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
  intro p dq a port Ψ
  iintro ⟨Hp, HΨ⟩
  unfold epCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t18 a port _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encRegisterArgs, tagged, tRegisterArgs] at HΨ
  iapply HΨ $$ Hp

theorem enc_BtlArgs : enc_BtlArgs.spec (GF := GF) := by
  intro p dq Ψ
  iintro ⟨Hp, HΨ⟩
  unfold epCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t84 _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encBtlArgs, tagged, tBeTheLeaderArgs] at HΨ
  iapply HΨ $$ Hp

theorem enc_PingArgs : enc_PingArgs.spec (GF := GF) := by
  intro p dq a Ψ
  iintro ⟨Hp, HΨ⟩
  unfold epCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t88 a _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encPingArgs, tagged, tPingArgs] at HΨ
  iapply HΨ $$ Hp

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
    WP (App (Val (@! examples.epaxosnet.rpcGetU64)) (Val #b)) {{ Φ }} := by
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
    WP (App (Val (@! examples.epaxosnet.rpcGetTag)) (Val #b)) {{ Φ }} := by
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

theorem wp_rpcDec_t14 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (s0 : GoString)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ s0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match getTag bs with
          | some (s, rest) => ⌜ok = true⌝ ∗ p ↦ s ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ s0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t14)) (Val #b)) (Val #p)) {{ Φ }} := by
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

theorem wp_rpcDec_t4 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : w64)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match getU64 bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t4)) (Val #b)) (Val #p)) {{ Φ }} := by
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

/-- The pure `rpcDec_t16` (`bool`). -/
def decBool (bs : List w8) : Option (Bool × List w8) :=
  match bs with
  | [] => none
  | c :: r => if 1 < uint.Z c then none else some (decide (c = W8 1), r)

theorem wp_rpcDec_t16 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : Bool)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decBool bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t16)) (Val #b)) (Val #p)) {{ Φ }} := by
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

theorem wp_rpcDec_t90 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decHdr bs with
          | some rest => ⌜ok = true⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t90)) (Val #b)) (Val #p)) {{ Φ }} := by
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
    WP (App (Val (@! examples.epaxosnet.rpcErrDecode)) (Val #())) {{ Φ }} := by
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

theorem dec_PingReply : dec_PingReply.spec (GF := GF) := by
  intro p rep Ψ
  iintro ⟨%Htag, Hp, HΨ⟩
  unfold epCodec
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
    wp_apply wp_rpcDec_t90 r rest dq p $$ Hr
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

/-- The pure `rpcDec_t26` (`int32`, sign-extended on the wire). -/
def decI32 (bs : List w8) : Option (w32 × List w8) :=
  match getU64 bs with
  | none => none
  | some (x, r) => if W64 (sint.Z (W32 (sint.Z x))) = x then some (W32 (sint.Z x), r) else none

theorem wp_rpcDec_t26 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : w32)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decI32 bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t26)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold decI32
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
    by_cases hx : W64 (sint.Z (W32 (sint.Z x))) = x
    · rw [decide_eq_true hx]
      wp_auto
      iapply HΦ
      rw [if_pos hx]
      dsimp only
      iframe
      ipureintro; rfl
    · rw [decide_eq_false hx]
      wp_auto
      iapply HΦ
      rw [if_neg hx]
      dsimp only
      iframe
      isplitr
      · ipureintro; rfl
      iapply Hback $$ Hr

/-- The pure `rpcDec_t86` (`BeTheLeaderReply`), into `{l0, nl0}`. -/
def decBR (l0 nl0 : w32) (bs : List w8) : Option ((w32 × w32) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld decI32 l0 r with
    | none => none
    | some (l, r) =>
      match decFld decI32 nl0 r with
      | none => none
      | some (nl, r) => some ((l, nl), r)

theorem wp_rpcDec_t86 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (l0 nl0 : w32)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ replica.defs.BeTheLeaderReply.mk l0 nl0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decBR l0 nl0 bs with
          | some ((l, nl), rest) => ⌜ok = true⌝ ∗ p ↦ replica.defs.BeTheLeaderReply.mk l nl ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ l nl, p ↦ replica.defs.BeTheLeaderReply.mk l nl) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t86)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decBR
  all_goals fld_step wp_rpcDec_t26 decI32 Leader fail struct_close decBR
  all_goals fld_step wp_rpcDec_t26 decI32 NextLeader fail struct_close decBR
  all_goals ((try wp_auto); struct_close decBR)

end proof

/-! ### Round trips -/

theorem getU64_enc' (x : w64) (rest : List w8) : getU64 (u64Le x ++ rest) = some (x, rest) := by
  unfold getU64
  rw [ite_eq_left (by simp [u64Le_length])]
  have h8 := u64Le_length x
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
    u64Le_to_word]

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

theorem decI32_enc (x : w32) (rest : List w8) : decI32 (encI32 x ++ rest) = some (x, rest) := by
  unfold decI32 encI32
  rw [getU64_enc']
  have h1 : sint.Z (W64 (sint.Z x)) = sint.Z x := by word
  have h2 : W32 (sint.Z x) = x := by word
  simp only [h1, h2, ↓reduceIte]

theorem decFld_fI32 (v0 x : w32) (rest : List w8) :
    decFld decI32 v0 (fI32 x ++ rest) = some (mergeI32 v0 x, rest) := by
  apply decFld_fld
  · intro h
    have hx : x = W32 0 := by simpa using h
    simp [mergeI32, hx]
  · intro h
    have hx : x ≠ W32 0 := by simpa using h
    rw [decI32_enc]
    simp only [mergeI32, if_neg hx]

theorem decBR_enc (l0 nl0 l nl : w32) :
    decBR l0 nl0 (strct [fI32 l, fI32 nl]) = some ((mergeI32 l0 l, mergeI32 nl0 nl), []) := by
  have e : strct [fI32 l, fI32 nl] = W8 1 :: (fI32 l ++ (fI32 nl ++ [])) := by
    simp [strct]
  rw [e]
  simp only [decBR, decHdr, ↓reduceIte, decFld_fI32]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [examples.epaxosnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

theorem dec_BtlReply : dec_BtlReply.spec (GF := GF) := by
  intro p l0 nl0 rep Ψ
  iintro ⟨%Htag, Hp, HΨ⟩
  unfold epCodec
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
    · simp only [Bool.false_eq_true, ite_false]
      iexists _; iframe Hp; ipureintro
      intro l' nl' he; subst he
      rw [encBtlReply, tagged, getTag_encStr' _ _ (by decide)] at hg
      first | (cases hg; done) | (cases hg; rw [decBR_enc] at hd; first | (cases hd; done) | (cases hd; exact h0 rfl))
    dec_fail
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    have ht := Htag _ _ hg
    subst ht
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDec_t86 r rest dq p _ _ $$ Hr Hp
    iintro %r2 %ok2 H2
    rcases hd : decBR l0 nl0 rest with _ | ⟨⟨l, nl⟩, rest2⟩
    · simp only [hd]
      icases H2 with ⟨%Hok, ⟨%l1, %nl1, Hp⟩, Hr⟩
      subst Hok
      wp_auto
      ihave Hd := Hback $$ Hr
      ihave HΨ0 := HΨ $$ %false [Hp]
      · simp only [Bool.false_eq_true, ite_false]
        iexists _; iframe Hp; ipureintro
        intro l' nl' he; subst he
        rw [encBtlReply, tagged, getTag_encStr' _ _ (by decide)] at hg
        first | (cases hg; done) | (cases hg; rw [decBR_enc] at hd; first | (cases hd; done) | (cases hd; exact h0 rfl))
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
          iexists l, nl
          iframe
          ipureintro
          intro l' nl' he
          subst he
          rw [encBtlReply, tagged, getTag_encStr' _ _ (by decide)] at hg
          cases hg
          rw [decBR_enc] at hd
          cases hd
          exact ⟨rfl, rfl⟩
        simp only [ite_true]
        ipureintro; trivial
      · rw [decide_eq_false (show ¬ r2.len = W64 0 by
          intro h; rw [h] at Hl2; exact h0 (List.eq_nil_of_length_eq_zero (Hl2.1.trans (by rfl))))]
        wp_auto
        ihave HΨ0 := HΨ $$ %false [Hp]
        · simp only [Bool.false_eq_true, ite_false]
          iexists _; iframe Hp; ipureintro
          intro l' nl' he; subst he
          rw [encBtlReply, tagged, getTag_encStr' _ _ (by decide)] at hg
          first | (cases hg; done) | (cases hg; rw [decBR_enc] at hd; first | (cases hd; done) | (cases hd; exact h0 rfl))
        dec_fail

/-- `k` more strings, after `acc`. -/
def decStrsGo : Nat → List GoString → List w8 → Option (List GoString × List w8)
  | 0, acc, r => some (acc, r)
  | k + 1, acc, r =>
    match getTag r with
    | none => none
    | some (x, r') => decStrsGo k (acc ++ [x]) r'

/-- The pure `rpcDec_t13` (`[]string`). -/
def decStrs (bs : List w8) : Option (List GoString × List w8) :=
  match getU64 bs with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then decStrsGo (uint.nat n) [] r else none

theorem wp_rpcDec_t13 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ slice.nil -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decStrs bs with
          | some (x, rest) => ⌜ok = true⌝ ∗ (∃ sl : GoSlice, p ↦ sl ∗ sl ↦* x) ∗ r ↦*{dq} rest ∗
              (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ sl : GoSlice, p ↦ sl) ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t13)) (Val #b)) (Val #p)) {{ Φ }} := by
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
      ihave %hsl := ownSlice_len _ _ _ $$ Hs
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
        rw [if_pos (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len by
          have := hsl.1; have := hsl.2
          have h2 : ((sint.Z sl.len).toNat : Int) = sint.Z sl.len := Int.toNat_of_nonneg hsl.2
          rw [show sint.nat sl.len = (sint.Z sl.len).toNat from rfl] at *
          word)]
        have hlk : (acc ++ List.replicate (uint.nat x - uint.nat i) (go!"" : GoString))[(sint.Z i).toNat]? =
            some (go!"" : GoString) := by
          rw [show (sint.Z i).toNat = acc.length by word, hk]
          simp
        icases ownSlice_elem_acc (sint.Z i) (go!"" : GoString) sl _ _ (by word) hlk $$ Hs with ⟨He, Hs⟩
        wp_apply wp_rpcDec_t14 R cur dq _ _ $$ Hr He
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


set_option hygiene false in
/-- `hdr_step`, with the closing tactic `cl` for the header's failures. -/
macro "hdr_step_with " _D:ident " (" cl:tacticSeq ")" : tactic => `(tactic| (
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_func_call
  wp_call
  wp_auto
  rcases bs with _ | ⟨c, rest⟩
  · rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 1) by simp at Hl; word)]
    wp_auto
    ($cl)
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
    ($cl)
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

/-- The pure `rpcDec_t20` (`RegisterReply`), into the zero value. -/
def decRR (bs : List w8) : Option ((w64 × List GoString × Bool × Bool) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld getU64 (W64 0) r with
    | none => none
    | some (id, r) =>
      match decFld decStrs [] r with
      | none => none
      | some (nl, r) =>
        match decFld decBool false r with
        | none => none
        | some (rd, r) =>
          match decFld decBool false r with
          | none => none
          | some (il, r) => some ((id, nl, rd, il), r)

set_option hygiene false in
/-- Close a `RegisterReply` decoder's proof (the `NodeList` field in any of its states). -/
macro "rr_close " D:ident : tactic => `(tactic| (
  iapply HΦ
  simp only [$D:ident, decHdr, decFld, ↓reduceIte, *]
  iframe
  first
  | (icases NodeList with ⟨%sl, NodeList, Hsl⟩
     iexists sl
     iframe Hsl
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists slice.nil
     ihave Hsl := ownSlice_nil (V := GoString) (DFrac.own 1)
     iframe Hsl
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (icases NodeList with ⟨%sl, NodeList, -⟩
     iexists _; iexists _; iexists _; iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (icases NodeList with ⟨%sl, NodeList⟩
     iexists _; iexists _; iexists _; iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists _; iexists _; iexists _; iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)))

set_option maxHeartbeats 4000000 in
theorem wp_rpcDec_t20 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ replica.defs.RegisterReply.mk (W64 0) slice.nil false false -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decRR bs with
          | some ((id, nl, rd, il), rest) => ⌜ok = true⌝ ∗
              (∃ sl : GoSlice, p ↦ replica.defs.RegisterReply.mk id sl rd il ∗ sl ↦* nl) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ id sl rd il, p ↦ replica.defs.RegisterReply.mk id sl rd il) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t20)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step_with decRR (rr_close decRR)
  all_goals fld_step wp_rpcDec_t4 getU64 ReplicaId fail rr_close decRR
  all_goals fld_step wp_rpcDec_t13 decStrs NodeList fail rr_close decRR
  all_goals fld_step wp_rpcDec_t16 decBool Ready fail rr_close decRR
  all_goals fld_step wp_rpcDec_t16 decBool IsLeader fail rr_close decRR
  all_goals ((try wp_auto); rr_close decRR)

end proof

/-! ### `RegisterReply` round trip -/

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

theorem decFld_fInt (v : w64) (rest : List w8) :
    decFld getU64 (W64 0) (fInt v ++ rest) = some (v, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact getU64_enc' v rest

theorem decFld_fBool (x : Bool) (rest : List w8) :
    decFld decBool false (fBool x ++ rest) = some (x, rest) := by
  apply decFld_fld
  · intro h; exact h
  · intro h; subst h
    simp only [encBool, ↓reduceIte, List.cons_append, List.nil_append, decBool]
    simp [show uint.Z (W8 1) = 1 from rfl]
    decide

theorem decStrsGo_enc (ss acc : List GoString) (rest : List w8) (h : ∀ s ∈ ss, s.length < 2 ^ 64) :
    decStrsGo ss.length acc ((ss.map encStr).flatten ++ rest) = some (acc ++ ss, rest) := by
  induction ss generalizing acc with
  | nil => simp [decStrsGo]
  | cons s ss ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decStrsGo,
      getTag_encStr' s _ (h s (List.mem_cons_self ..)),
      ih (acc ++ [s]) (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))]
    simp

/-- The bounds a `[]string` round trip needs, from its encoding's length. -/
theorem encStrs_bounds (ss : List GoString) (hb : (encStrs ss).length < 2 ^ 63) :
    ss.length < 2 ^ 64 ∧ ∀ s ∈ ss, s.length < 2 ^ 64 := by
  have hfl : (ss.map encStr).flatten.length < 2 ^ 63 := by
    simp only [encStrs, List.length_append] at hb; omega
  refine ⟨?_, fun s hs => ?_⟩
  · have := count_le_flatten (ss.map encStr)
      (fun l hl => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl
        intro h; have := congrArg List.length h; simp [encStr, u64Le_length] at this)
    simp only [List.length_map] at this; omega
  · have := len_le_flatten _ _ (List.mem_map_of_mem (f := encStr) hs)
    simp only [encStr, List.length_append] at this; omega

theorem decStrs_enc (ss : List GoString) (rest : List w8) (hb : (encStrs ss).length < 2 ^ 63) :
    decStrs (encStrs ss ++ rest) = some (ss, rest) := by
  obtain ⟨hl, h⟩ := encStrs_bounds ss hb
  unfold decStrs encStrs
  rw [List.append_assoc, getU64_enc']
  have hn : uint.nat (W64 ss.length) = ss.length := by
    show (BitVec.ofNat 64 ss.length).toNat = ss.length
    simp only [BitVec.toNat_ofNat]; omega
  have hle : ss.length ≤ ((ss.map encStr).flatten ++ rest).length := by
    have := count_le_flatten (ss.map encStr)
      (fun l hl => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl
        intro h; have := congrArg List.length h; simp [encStr, u64Le_length] at this)
    simp only [List.length_append, List.length_map] at this ⊢; omega
  simp only [hn, hle, ↓reduceIte, decStrsGo_enc ss [] rest h, List.nil_append]

theorem decFld_fStrs (ss : List GoString) (rest : List w8) (hb : (encStrs ss).length < 2 ^ 63) :
    decFld decStrs [] (fStrs ss ++ rest) = some (ss, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact decStrs_enc ss rest hb

theorem decRR_enc (id : w64) (nl : List GoString) (r il : Bool)
    (hb : (encRegisterReply id nl r il).length < 2 ^ 63) :
    decRR (strct [fInt id, fStrs nl, fBool r, fBool il]) = some ((id, nl, r, il), []) := by
  have hs : (encStrs nl).length < 2 ^ 63 := by
    by_cases h : nl = []
    · subst h; simp [encStrs, u64Le_length]
    · have : (fStrs nl).length = (encStrs nl).length + 1 := by
        simp [fStrs, fld, h]
      simp only [encRegisterReply, tagged, strct, List.flatten_cons, List.flatten_nil,
        List.length_append, List.length_cons, List.length_nil] at hb
      omega
  have e : strct [fInt id, fStrs nl, fBool r, fBool il] =
      W8 1 :: (fInt id ++ (fStrs nl ++ (fBool r ++ (fBool il ++ [])))) := by
    simp [strct]
  rw [e]
  simp only [decRR, decHdr, ↓reduceIte, decFld_fInt, decFld_fStrs nl _ hs, decFld_fBool]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [examples.epaxosnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

theorem dec_RegisterReply : dec_RegisterReply.spec (GF := GF) := by
  intro p rep Ψ
  iintro ⟨%Htag, Hp, HΨ⟩
  unfold epCodec
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
    wp_apply wp_rpcDec_t20 r rest dq p $$ Hr Hp
    iintro %r2 %ok2 H2
    rcases hd : decRR rest with _ | ⟨⟨id, nl, rd, il⟩, rest2⟩
    · simp only [hd]
      icases H2 with ⟨%Hok, ⟨%id1, %sl1, %rd1, %il1, Hp⟩, Hr⟩
      subst Hok
      wp_auto
      ihave Hd := Hback $$ Hr
      ihave HΨ0 := HΨ $$ %false [Hp]
      · simp only [Bool.false_eq_true, ite_false]; iexists _; iexact Hp
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
          iexists id, sl, nl, rd, il
          iframe
          ipureintro
          intro id' nl' r' il' he
          subst he
          have h3 : sint.Z data.len < 2 ^ 63 := by word
          have hb : (encRegisterReply id' nl' r' il').length < 2 ^ 63 := by omega
          rw [encRegisterReply, tagged, getTag_encStr' _ _ (by decide)] at hg
          cases hg
          rw [decRR_enc id' nl' r' il' hb] at hd
          cases hd
          exact ⟨rfl, rfl, rfl, rfl⟩
        simp only [ite_true]
        ipureintro; trivial
      · rw [decide_eq_false (show ¬ r2.len = W64 0 by
          intro h; rw [h] at Hl2; exact h0 (List.eq_nil_of_length_eq_zero (Hl2.1.trans (by rfl))))]
        wp_auto
        ihave HΨ0 := HΨ $$ %false [Hp]
        · simp only [Bool.false_eq_true, ite_false]; iexists _; iexact Hp
        dec_fail

/-- The clients' codec lemmas, proved. -/
theorem epCodecLaws : CodecLaws (GF := GF) where
  enc_RegisterArgs := enc_RegisterArgs
  enc_BtlArgs := enc_BtlArgs
  enc_PingArgs := enc_PingArgs
  dec_RegisterReply := dec_RegisterReply
  dec_BtlReply := dec_BtlReply
  dec_PingReply := dec_PingReply

end proof

end github_com.imdea_software.swiftpaxos_epaxos

end Perennial
