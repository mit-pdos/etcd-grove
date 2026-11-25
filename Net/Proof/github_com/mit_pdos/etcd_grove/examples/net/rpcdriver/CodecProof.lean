/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: its codec's laws, proved

The generated codec (`examples/net/rpcdriver/rpc_gen.go`) meets `Codec.lean`'s laws
(`drvCodecLaws`): the encoders' bytes are `Wire.lean`'s, and decoding an encoding of a request
(into `NewArg()`'s zero `service.Args`) or of a reply (into the client's zero `service.Reply`)
succeeds and gives back the encoded values. As swiftnet's `NetRpc/CodecProof.lean`,
`CodecSrvProof.lean` and `CodecCliProof.lean` (whose lemmas are about swiftnet's functions: copied
and adapted here, the `[]bool` loops as the `[]byte` ones).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Codec
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
open github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.wire

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

/-! ## Pure decoders -/

/-- A `uint8` (`rpcEnc_t6`). -/
def encU8 (x : w8) : List w8 := u64Le (W64 (uint.Z x))

theorem encBytes_eq (ds : List w8) :
    encBytes ds = u64Le (W64 ds.length) ++ (ds.map encU8).flatten := rfl

/-- The pure `rpcGetU64`. -/
def getU64 (bs : List w8) : Option (w64 × List w8) :=
  if 8 ≤ bs.length then some (leToU64 (bs.take 8), bs.drop 8) else none

/-- The pure `rpcGetTag` (and `rpcDec_t7`, a `string`): a length, then that many bytes. -/
def getTag (bs : List w8) : Option (GoString × List w8) :=
  match getU64 bs with
  | some (n, r) =>
    if uint.nat n ≤ r.length then some (r.take (uint.nat n), r.drop (uint.nat n)) else none
  | none => none

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

/-- The pure `rpcDec_t6` (`uint8`). -/
def decU8 (bs : List w8) : Option (w8 × List w8) :=
  match getU64 bs with
  | none => none
  | some (x, r) => if uint.Z x < 256 then some (W8 (uint.Z x), r) else none

/-- `k` more bytes, after `acc`. -/
def decBytesGo : Nat → List w8 → List w8 → Option (List w8 × List w8)
  | 0, acc, r => some (acc, r)
  | k + 1, acc, r =>
    match decU8 r with
    | none => none
    | some (x, r') => decBytesGo k (acc ++ [x]) r'

/-- The pure `rpcDec_t5` (`[]byte`). -/
def decBytes (bs : List w8) : Option (List w8 × List w8) :=
  match getU64 bs with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then decBytesGo (uint.nat n) [] r else none

/-- The pure `rpcDec_t3` (`service.Args`), into the zero value. -/
def decArgs (bs : List w8) : Option ((w64 × List w8 × GoString) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld getU64 (W64 0) r with
    | none => none
    | some (id, r) =>
      match decFld decBytes [] r with
      | none => none
      | some (d, r) =>
        match decFld getTag go!"" r with
        | none => none
        | some (f, r) => some ((id, d, f), r)

/-- The pure `rpcDec_t9` (`service.Reply`), into the zero value. -/
def decReply (bs : List w8) : Option ((w64 × List w8 × w64) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld getU64 (W64 0) r with
    | none => none
    | some (id, r) =>
      match decFld decBytes [] r with
      | none => none
      | some (d, r) =>
        match decFld getU64 (W64 0) r with
        | none => none
        | some (n, r) => some ((id, d, n), r)

/-! ## Round trips -/

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

theorem getTag_tagged (t body : List w8) (ht : t.length < 2 ^ 64) :
    getTag (tagged t body) = some (t, body) := by
  unfold tagged; exact getTag_encStr' _ _ ht

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

theorem decFld_fU64 (v : w64) (rest : List w8) :
    decFld getU64 (W64 0) (fU64 v ++ rest) = some (v, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact getU64_enc' v rest

theorem len_fStr (k : GoString) : k.length ≤ (fStr k).length := by
  by_cases hk : k = []
  · simp [hk]
  · simp [fStr, fld, hk, encStr]; omega

theorem decFld_fStr (k rest : List w8) (hk : k.length < 2 ^ 64) :
    decFld getTag go!"" (fStr k ++ rest) = some (k, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact getTag_encStr' k rest hk

theorem decU8_enc (c : w8) (rest : List w8) : decU8 (encU8 c ++ rest) = some (c, rest) := by
  unfold decU8 encU8
  rw [getU64_enc']
  have h1 : uint.Z (W64 (uint.Z c)) < 256 := by word
  have h2 : W8 (uint.Z (W64 (uint.Z c))) = c := by word
  simp only [h1, ↓reduceIte, h2]

theorem len_flatten_encU8 (ds : List w8) : ((ds.map encU8).flatten).length = 8 * ds.length := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih, encU8, u64Le_length,
      List.length_cons]
    omega

theorem decBytesGo_enc (ds acc rest : List w8) :
    decBytesGo ds.length acc ((ds.map encU8).flatten ++ rest) = some (acc ++ ds, rest) := by
  induction ds generalizing acc with
  | nil => simp [decBytesGo]
  | cons d ds ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decBytesGo,
      decU8_enc d _, ih (acc ++ [d])]
    simp

theorem decBytes_enc (ds rest : List w8) (h : ds.length < 2 ^ 64) :
    decBytes (encBytes ds ++ rest) = some (ds, rest) := by
  unfold decBytes
  rw [encBytes_eq, List.append_assoc, getU64_enc']
  have hn : uint.nat (W64 ds.length) = ds.length := by
    show (BitVec.ofNat 64 ds.length).toNat = ds.length
    simp only [BitVec.toNat_ofNat]; omega
  have hle : ds.length ≤ ((ds.map encU8).flatten ++ rest).length := by
    simp only [List.length_append, len_flatten_encU8]; omega
  simp only [hn, hle, ↓reduceIte, decBytesGo_enc ds [] rest, List.nil_append]

theorem len_fBytes (ds : List w8) : ds.length ≤ (fBytes ds).length := by
  by_cases h : ds = []
  · simp [h]
  · have : (fBytes ds).length = 1 + (8 + 8 * ds.length) := by
      simp only [fBytes, fld, ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte,
        List.length_cons, encBytes_eq, List.length_append, u64Le_length, len_flatten_encU8]
      omega
    omega

theorem decFld_fBytes (ds rest : List w8) (h : ds.length < 2 ^ 64) :
    decFld decBytes [] (fBytes ds ++ rest) = some (ds, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact decBytes_enc ds rest h

theorem decArgs_enc (id : w64) (data : List w8) (fl : GoString) (hd : data.length < 2 ^ 64)
    (hf : fl.length < 2 ^ 64) :
    decArgs (strct [fU64 id, fBytes data, fStr fl]) = some ((id, data, fl), []) := by
  have e : strct [fU64 id, fBytes data, fStr fl] =
      W8 1 :: (fU64 id ++ (fBytes data ++ (fStr fl ++ []))) := by
    simp [strct]
  rw [e]
  simp only [decArgs, decHdr, ↓reduceIte, decFld_fU64, decFld_fBytes data _ hd,
    decFld_fStr fl _ hf]

theorem decReply_enc (id : w64) (data : List w8) (runs : w64) (hd : data.length < 2 ^ 64) :
    decReply (strct [fU64 id, fBytes data, fU64 runs]) = some ((id, data, runs), []) := by
  have e : strct [fU64 id, fBytes data, fU64 runs] =
      W8 1 :: (fU64 id ++ (fBytes data ++ (fU64 runs ++ []))) := by
    simp [strct]
  rw [e]
  simp only [decReply, decHdr, ↓reduceIte, decFld_fU64, decFld_fBytes data _ hd]

/-- The bounds a request's round trip needs, from its encoding's length. -/
theorem encArgs_bounds (id : w64) (data : List w8) (fl : GoString)
    (h : (encArgs id data fl).length < 2 ^ 63) : data.length < 2 ^ 64 ∧ fl.length < 2 ^ 64 := by
  have h1 := len_fBytes data
  have h2 := len_fStr fl
  simp only [encArgs, tagged, strct, List.flatten_cons, List.flatten_nil, List.length_append,
    List.length_cons, List.append_nil] at h
  omega

/-- The bound a reply's round trip needs, from its encoding's length. -/
theorem encReply_bounds (id : w64) (data : List w8) (runs : w64)
    (h : (encReply id data runs).length < 2 ^ 63) : data.length < 2 ^ 64 := by
  have h1 := len_fBytes data
  simp only [encReply, tagged, strct, List.flatten_cons, List.flatten_nil, List.length_append,
    List.length_cons, List.append_nil] at h
  omega

theorem tagged_inj {t b b' : List w8} (h : tagged t b = tagged t b') : b = b' :=
  List.append_cancel_left h

/-- The request encoding is injective (under the bound a decoding gives). -/
theorem encArgs_inj (id id' : w64) (data data' : List w8) (fl fl' : GoString)
    (hl : (encArgs id data fl).length < 2 ^ 63)
    (h : encArgs id data fl = encArgs id' data' fl') :
    id = id' ∧ data = data' ∧ fl = fl' := by
  have hl' : (encArgs id' data' fl').length < 2 ^ 63 := h ▸ hl
  obtain ⟨hd, hf⟩ := encArgs_bounds id data fl hl
  obtain ⟨hd', hf'⟩ := encArgs_bounds id' data' fl' hl'
  have e1 := decArgs_enc id data fl hd hf
  rw [tagged_inj h, decArgs_enc id' data' fl' hd' hf'] at e1
  cases e1; exact ⟨rfl, rfl, rfl⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [rpcdriver.Assumptions]
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

theorem wp_rpcEnc_t7 (s : GoString) :
    encFn (GF := GF) rpcEnc_t7 #s (encStr s) iprop(True) := by
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
    encFn (GF := GF) rpcEnc_t4 #x (u64Le x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcEnc_t6 (x : w8) :
    encFn (GF := GF) rpcEnc_t6 #x (encU8 x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcSent_t7 (s : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! rpcSent_t7)) (Val #s))
    {{ RET #(decide (s ≠ [])); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (s = [])) = decide (s ≠ []) by simp]
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t4 (x : w64) :
    {{ (True : IProp GF) }} (App (Val (@! rpcSent_t4)) (Val #x))
    {{ RET #(decide (x ≠ W64 0)); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (x = W64 0)) = decide (x ≠ W64 0) by simp]
  iapply HΦ
  ipureintro; trivial

set_option hygiene false in
/-- The last step of a struct encoder's proof: its bytes are `Wire.lean`'s. -/
local macro "enc_close" : tactic => `(tactic| (
  iapply HΦ
  isimp only [strct, fld, fStr, fU64, fBytes, List.flatten_cons,
    List.flatten_nil, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    List.append_nil, decide_true, decide_false, ne_eq, not_true_eq_false, not_false_eq_true,
    ite_true, ite_false, Bool.false_eq_true, ↓reduceIte, *]
  (try isimp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at Hb)
  iframe))

/-- `rpcPutTag(tag)`: a new slice, the string `tag`'s encoding. -/
theorem wp_rpcPutTag (tag : GoString) :
    {{ (True : IProp GF) }} (App (Val (@! rpcPutTag)) (Val #tag))
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

theorem wp_rpcSent_t5 (sl : GoSlice) (dq : DFrac) (x : List w8) :
    {{ (sl ↦*{dq} x : IProp GF) }} (App (Val (@! rpcSent_t5)) (Val #sl))
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

theorem wp_rpcEnc_t5 (sl : GoSlice) (dq : DFrac) (x : List w8) :
    encFn (GF := GF) rpcEnc_t5 #sl (encBytes x) iprop(sl ↦*{dq} x) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, Hsl⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  have hlen : sl.len = W64 x.length := by rw [Hl.1]; word
  ihave HI : (∃ (i : w64) (bb : GoSlice) (y : w8),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗ "x" ∷ x_ptr ↦ y ∗
      "Hb" ∷ bb ↦* (bs ++ u64Le sl.len ++
        ((x.take (sint.nat i)).map encU8).flatten) ∗
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
    wp_apply wp_rpcEnc_t6 e _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩
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
    rw [encBytes_eq, ← hlen, List.append_assoc,
      show (x.map encU8).flatten =
        ((x.take (sint.nat i)).map encU8).flatten by
        rw [hn, List.take_length]]
    iexact Hb

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

theorem wp_rpcDec_t7 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (s0 : GoString)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ s0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match getTag bs with
          | some (s, rest) => ⌜ok = true⌝ ∗ p ↦ s ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ s0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! rpcDec_t7)) (Val #b)) (Val #p)) {{ Φ }} := by
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
    WP (App (App (Val (@! rpcDec_t4)) (Val #b)) (Val #p)) {{ Φ }} := by
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


theorem wp_rpcDec_t6 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : w8)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decU8 bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! rpcDec_t6)) (Val #b)) (Val #p)) {{ Φ }} := by
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
local macro "fld_step " L:term:max D:term:max F:ident " fail " ft:tacticSeq : tactic => `(tactic| (
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
/-- `hdr_step`, with the closing tactic `cl` for the header's failures. -/
local macro "hdr_step_with " _D:ident " (" cl:tacticSeq ")" : tactic => `(tactic| (
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


set_option hygiene false in
/-- A decoding's success tail: `Hr2`, `Hback2` (the inner decoder's rest, empty), `Hback`; ends
with `Hd` back and the length check done, before `HΦ`. -/
local macro "dec_ok" : tactic => `(tactic| (
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
  wp_auto
  ihave Hd := Hback $$ [Hback2 Hr2]
  · iapply Hback2 $$ Hr2
  rw [show r2.len = W64 0 by simp at Hl2; word]
  wp_auto))


theorem wp_rpcDec_t5 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ slice.nil -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decBytes bs with
          | some (x, rest) => ⌜ok = true⌝ ∗ (∃ sl : GoSlice, p ↦ sl ∗ sl ↦* x) ∗ r ↦*{dq} rest ∗
              (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ sl : GoSlice, p ↦ sl) ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! rpcDec_t5)) (Val #b)) (Val #p)) {{ Φ }} := by
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
      ihave %hsl := ownSlice_len _ _ _ $$ Hs
      simp only [List.length_replicate] at hsl
      ihave HI : (∃ (i : w64) (R : GoSlice) (acc : List w8) (cur : List w8),
          "i" ∷ i_ptr ↦ i ∗ "r" ∷ r_ptr ↦ R ∗ "ok" ∷ ok_ptr ↦ true ∗ "Hr" ∷ R ↦*{dq} cur ∗
          "Hback" ∷ (R ↦*{dq} cur -∗ b ↦*{dq} bs) ∗
          "Hs" ∷ sl ↦* (acc ++ List.replicate (uint.nat x - uint.nat i) (W8 0)) ∗
          "%Hi" ∷ ⌜acc.length = uint.nat i ∧ uint.nat i ≤ uint.nat x ∧
            decBytesGo (uint.nat x - uint.nat i) acc cur = decBytesGo (uint.nat x) [] rest⌝ : IProp GF)
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
        have hlk : (acc ++ List.replicate (uint.nat x - uint.nat i) (W8 0))[(sint.Z i).toNat]? =
            some (W8 0) := by
          rw [show (sint.Z i).toNat = acc.length by word, hk]
          simp
        icases ownSlice_elem_acc (sint.Z i) (W8 0) sl _ _ (by word) hlk $$ Hs with ⟨He, Hs⟩
        wp_apply wp_rpcDec_t6 R cur dq _ _ $$ Hr He
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
          have hres : decBytesGo (uint.nat x) [] rest = none := by
            rw [← Hi.2.2, hk]; simp [decBytesGo, hd]
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
          simp [decBytesGo, hd]
      · (try wp_auto)
        have hix : uint.nat x - uint.nat i = 0 := by
          have : ¬ uint.Z i < uint.Z x := by
            first | exact Hif | exact fun h => Hif (by simp [h])
          word
        have hres : decBytesGo (uint.nat x) [] rest = some (acc, cur) := by
          rw [← Hi.2.2, hix]; rfl
        iapply HΦ
        rw [hres]
        dsimp only
        rw [hix, List.replicate_zero, List.append_nil]
        iframe
        ipureintro; rfl


theorem wp_rpcEnc_t3 (id : w64) (dsl : GoSlice) (dqs : DFrac) (data : List w8) (fl : GoString) :
    encFn (GF := GF) rpcEnc_t3 #(service.Args.mk id dsl fl)
      (strct [fU64 id, fBytes data, fStr fl]) iprop(dsl ↦*{dqs} data) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, HR⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
  )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t4 id
    by_cases h1 : id = W64 0 <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t4 id _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t5 dsl dqs data $$ [$HR] as HR
    by_cases h2 : data = [] <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t5 dsl dqs data _ _ $$ [$Hb $Hcap $HR] as %b2 ⟨Hb, Hcap, HR⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t7 fl
    by_cases h3 : fl = [] <;> simp only [h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t7 fl _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t9 (id : w64) (dsl : GoSlice) (dqs : DFrac) (data : List w8) (runs : w64) :
    encFn (GF := GF) rpcEnc_t9 #(service.Reply.mk id dsl runs)
      (strct [fU64 id, fBytes data, fU64 runs]) iprop(dsl ↦*{dqs} data) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, HR⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
  )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t4 id
    by_cases h1 : id = W64 0 <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t4 id _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t5 dsl dqs data $$ [$HR] as HR
    by_cases h2 : data = [] <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t5 dsl dqs data _ _ $$ [$Hb $Hcap $HR] as %b2 ⟨Hb, Hcap, HR⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t4 runs
    by_cases h3 : runs = W64 0 <;> simp only [h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t4 runs _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    enc_close)

theorem enc_Args : enc_Args.spec (GF := GF) := by
  intro p dq id dsl fl dqs data Ψ
  iintro ⟨Hp, Hsl, HΨ⟩
  unfold drvCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t3 id dsl dqs data fl _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, Hsl⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encArgs, tagged, tArgs] at HΨ
  iapply HΨ $$ Hp Hsl

theorem enc_Reply : enc_Reply.spec (GF := GF) := by
  intro p dq id dsl runs dqs data Ψ
  iintro ⟨Hp, Hsl, HΨ⟩
  unfold drvCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t9 id dsl dqs data runs _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, Hsl⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encReply, tagged, tReply] at HΨ
  iapply HΨ $$ Hp Hsl

/-! ## Decoding the structs -/

set_option hygiene false in
/-- Close an `Args`/`Reply` decoder's proof: the pure decoder `D` computed, the struct put back
together (its `Data` field in any of its states). -/
local macro "sd_close " D:ident : tactic => `(tactic| (
  iapply HΦ
  simp only [$D:ident, decHdr, decFld, ↓reduceIte, *]
  iframe
  first
  | (icases Data with ⟨%sl, Data, Hsl⟩
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
  | (icases Data with ⟨%sl, Data, -⟩
     iexists _; iexists _; iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (icases Data with ⟨%sl, Data⟩
     iexists _; iexists _; iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists _; iexists _; iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)))

set_option maxHeartbeats 4000000 in
theorem wp_rpcDec_t3 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ service.Args.mk (W64 0) slice.nil go!"" -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decArgs bs with
          | some ((id, d, f), rest) => ⌜ok = true⌝ ∗
              (∃ sl : GoSlice, p ↦ service.Args.mk id sl f ∗ sl ↦* d) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ id sl f, p ↦ service.Args.mk id sl f) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! rpcDec_t3)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step_with decArgs (sd_close decArgs)
  all_goals fld_step wp_rpcDec_t4 getU64 ID fail sd_close decArgs
  all_goals fld_step wp_rpcDec_t5 decBytes Data fail sd_close decArgs
  all_goals fld_step wp_rpcDec_t7 getTag Fail fail sd_close decArgs
  all_goals ((try wp_auto); sd_close decArgs)

set_option maxHeartbeats 4000000 in
theorem wp_rpcDec_t9 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ service.Reply.mk (W64 0) slice.nil (W64 0) -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decReply bs with
          | some ((id, d, n), rest) => ⌜ok = true⌝ ∗
              (∃ sl : GoSlice, p ↦ service.Reply.mk id sl n ∗ sl ↦* d) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ id sl n, p ↦ service.Reply.mk id sl n) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! rpcDec_t9)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step_with decReply (sd_close decReply)
  all_goals fld_step wp_rpcDec_t4 getU64 ID fail sd_close decReply
  all_goals fld_step wp_rpcDec_t5 decBytes Data fail sd_close decReply
  all_goals fld_step wp_rpcDec_t4 getU64 Runs fail sd_close decReply
  all_goals ((try wp_auto); sd_close decReply)

/-! ## The decoding laws -/

theorem decA_Args : decA_Args.spec (GF := GF) := by
  intro p id data fl Ψ
  iintro ⟨Hp, HΨ⟩
  unfold drvCodec
  iintro %bsl %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have hb : (encArgs id data fl).length < 2 ^ 63 := by
    have h3 : sint.Z bsl.len < 2 ^ 63 := by word
    omega
  obtain ⟨hdl, hfl⟩ := encArgs_bounds id data fl hb
  have hd := decArgs_enc id data fl hdl hfl
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag bsl _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encArgs, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t3 r _ dq p $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [hd]
  icases H2 with ⟨%Hok, ⟨%sl, Hp, Hsl⟩, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp Hsl]
  · iapply HΨ $$ %sl %hb Hp Hsl
  simp only [ite_true]
  ipureintro; trivial

theorem dec_Reply : dec_Reply.spec (GF := GF) := by
  intro p id data runs Ψ
  iintro ⟨Hp, HΨ⟩
  unfold drvCodec
  iintro %bsl %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have hb : (encReply id data runs).length < 2 ^ 63 := by
    have h3 : sint.Z bsl.len < 2 ^ 63 := by word
    omega
  have hd := decReply_enc id data runs (encReply_bounds id data runs hb)
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag bsl _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encReply, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t9 r _ dq p $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [hd]
  icases H2 with ⟨%Hok, ⟨%sl, Hp, Hsl⟩, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp Hsl]
  · iapply HΨ $$ Hp Hsl
  simp only [ite_true]
  ipureintro; trivial

/-- The codec's laws, proved. -/
theorem drvCodecLaws : CodecLaws (GF := GF) where
  enc_Args := enc_Args
  dec_Reply := dec_Reply
  decA_Args := decA_Args
  enc_Reply := enc_Reply

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

end Perennial
