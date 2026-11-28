/-
The hraft kit's generated net/rpc codec (`examples/hraftnet/rpc_gen.go`, by `models/net/rpc/rpcgen.py`)
as the specs see it (notes/dsv-hraft.md, S4), as craq's (`Craq/Codec.lean`):

* **The `CodecSpec`** `hraftCodec`: each predicate transformer is the weakest precondition of the
  generated function it describes (`rpcEncode`, `rpcDecode`, `rpcReceiver`), so the codec meets it
  by definition (`hraftCodec_encOk`, `hraftCodec_decOk`, `hraftCodec_rcvOk`).
* **The pure decoders** of the wire types (`getU64`, `getTag`, `decBytes`, `decHeaderV`, ...,
  one per generated `rpcDec_tN`, on any bytes), and their round trips on the encodings of
  `rpctransport/WireEnc.lean` (`dec*_enc`), under the bound a slice's bytes have (`< 2 ^ 64`).

The codec laws (`rpctransport/CodecLaws.lean`'s `CodecLaws hraftCodec`) and the receiver's methods
(`methodOk`) are proved in `CodecLawsProof.lean` and `CodecRcv.lean`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.CodecLaws

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open rpctransport

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The codec's predicate transformers: the generated functions' weakest preconditions. -/
def hraftCodec : net.rpc.CodecSpec GF where
  enc v Ψ := iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sl : GoSlice) (bs : List w8), sl ↦* bs -∗ ownSliceCap w8 sl (DFrac.own 1) -∗ Ψ bs -∗
        Φ #sl) -∗
    WP (App (Val #(functions rpcEncode [])) (Val #v)) {{ Φ }})
  dec bs ptr Ψ := iprop(∀ (data : GoSlice) (dq : DFrac) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else net.rpc.decErr err) -∗ Φ #err) -∗
    WP (App (App (Val #(functions rpcDecode [])) (Val #data)) (Val #ptr)) {{ Φ }})
  rcv rcvr Ψ := iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
    WP (App (Val #(functions rpcReceiver [])) (Val #rcvr)) {{ Φ }})

/-- `hraftCodec`'s encoder is monotone in its continuation (`CodecLaws.enc_mono`). -/
theorem hraftCodec_enc_mono (v : GoInterface) (Ψ Ψ' : List w8 → IProp GF) :
    (hraftCodec (GF := GF) (hG := hG)).enc v Ψ ∗ (∀ bs, Ψ bs -∗ Ψ' bs) ⊢
      (hraftCodec (GF := GF) (hG := hG)).enc v Ψ' := by
  iintro ⟨Henc, Hw⟩
  unfold hraftCodec
  iintro %Φ HΦ
  iapply Henc
  inext
  iintro %sl %bs Hs Hc HΨ
  iapply HΦ $$ Hs Hc
  iapply Hw $$ HΨ

variable [package_sem' : net.rpc.Assumptions]

theorem hraftCodec_encOk : ⊢ net.rpc.encOk (hG := hG) hraftCodec (functions rpcEncode []) := by
  unfold net.rpc.encOk
  iintro !> %v %Ψ %Φ Henc HΦ
  unfold hraftCodec
  iapply Henc
  iexact HΦ

theorem hraftCodec_rcvOk : ⊢ net.rpc.rcvOk (hG := hG) hraftCodec (functions rpcReceiver []) := by
  unfold net.rpc.rcvOk
  iintro !> %rcvr %Ψ %Φ Hr HΦ
  unfold hraftCodec
  iapply Hr
  iexact HΦ

theorem hraftCodec_decOk : ⊢ net.rpc.decOk (hG := hG) hraftCodec (functions rpcDecode []) := by
  unfold net.rpc.decOk
  iintro !> %data %dq %bs %ptr %Ψ %Φ Hd Hdec HΦ
  unfold hraftCodec
  iapply Hdec $$ Hd
  iexact HΦ

end codec

/-! ## The pure decoders -/

/-- The pure `rpcGetU64` (and the decoders of `uint64`, `int64`, `raft.ProtocolVersion`,
`raft.SnapshotVersion`, whose range checks always hold). -/
def getU64 (bs : List w8) : Option (w64 × List w8) :=
  if 8 ≤ bs.length then some (leToU64 (bs.take 8), bs.drop 8) else none

/-- The pure `rpcGetTag` (and the `string` decoder): a length, then that many bytes. -/
def getTag (bs : List w8) : Option (GoString × List w8) :=
  match getU64 bs with
  | some (n, r) => if uint.nat n ≤ r.length then some (r.take (uint.nat n), r.drop (uint.nat n)) else none
  | none => none

/-- The pure `bool` decoder. -/
def decBool (bs : List w8) : Option (Bool × List w8) :=
  match bs with
  | [] => none
  | c :: r => if 1 < uint.Z c then none else some (decide (c = W8 1), r)

/-- The pure `uint8` (and `raft.LogType`) decoder. -/
def decU8 (bs : List w8) : Option (w8 × List w8) :=
  match getU64 bs with
  | none => none
  | some (x, r) => if uint.Z x < 256 then some (W8 (uint.Z x), r) else none

/-- `k` more bytes (each a `uint64`), after `acc`. -/
def decU8sGo : Nat → List w8 → List w8 → Option (List w8 × List w8)
  | 0, acc, r => some (acc, r)
  | k + 1, acc, r =>
    match decU8 r with
    | none => none
    | some (x, r') => decU8sGo k (acc ++ [x]) r'

/-- The pure `[]uint8` decoder. -/
def decBytes (bs : List w8) : Option (List w8 × List w8) :=
  match getU64 bs with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then decU8sGo (uint.nat n) [] r else none

/-- A struct's header byte (`1`). -/
def decStructHdr (bs : List w8) : Option (List w8) :=
  match bs with
  | [] => none
  | c :: r => if c = W8 1 then some r else none

/-- A struct field: `0` (not sent: the field keeps `v0`) or `1` and the value (`d`). -/
def decFld {α : Type} (d : List w8 → Option (α × List w8)) (v0 : α) (bs : List w8) :
    Option (α × List w8) :=
  match bs with
  | [] => none
  | c :: r => if 1 < uint.Z c then none else if c = W8 1 then d r else some (v0, r)

/-- The zero `Header`'s value. -/
abbrev hdr0 : HdrV := ⟨W64 0, [], []⟩

/-- The pure `Header` decoder. -/
def decHeaderV (bs : List w8) : Option (HdrV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld getU64 (W64 0) r with
    | none => none
    | some (pv, r) =>
      match decFld decBytes [] r with
      | none => none
      | some (id, r) =>
        match decFld decBytes [] r with
        | none => none
        | some (ad, r) => some (⟨pv, id, ad⟩, r)

/-- The pure `Entry` decoder. -/
def decEntV (bs : List w8) : Option (EntV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld getU64 (W64 0) r with
    | none => none
    | some (ix, r) =>
      match decFld getU64 (W64 0) r with
      | none => none
      | some (tm, r) =>
        match decFld decU8 (W8 0) r with
        | none => none
        | some (ty, r) =>
          match decFld decBytes [] r with
          | none => none
          | some (dt, r) =>
            match decFld decBytes [] r with
            | none => none
            | some (ex, r) => some (⟨ix, tm, ty, dt, ex⟩, r)

/-- `k` more entries, after `acc`. -/
def decEntsGo : Nat → List EntV → List w8 → Option (List EntV × List w8)
  | 0, acc, r => some (acc, r)
  | k + 1, acc, r =>
    match decEntV r with
    | none => none
    | some (e, r') => decEntsGo k (acc ++ [e]) r'

/-- The pure `[]Entry` decoder. -/
def decEnts (bs : List w8) : Option (List EntV × List w8) :=
  match getU64 bs with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then decEntsGo (uint.nat n) [] r else none

/-- The pure `AppendReq` decoder. -/
def decAEReqV (bs : List w8) : Option (AEReqV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decHeaderV hdr0 r with
    | none => none
    | some (h, r) =>
      match decFld getU64 (W64 0) r with
      | none => none
      | some (tm, r) =>
        match decFld decBytes [] r with
        | none => none
        | some (ld, r) =>
          match decFld getU64 (W64 0) r with
          | none => none
          | some (pv, r) =>
            match decFld getU64 (W64 0) r with
            | none => none
            | some (pt, r) =>
              match decFld decEnts [] r with
              | none => none
              | some (es, r) =>
                match decFld getU64 (W64 0) r with
                | none => none
                | some (lci, r) => some (⟨h, tm, ld, pv, pt, es, lci⟩, r)

/-- The pure `AppendResp` decoder. -/
def decAERespV (bs : List w8) : Option (AERespV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decBool false r with
    | none => none
    | some (fl, r) =>
      match decFld getTag [] r with
      | none => none
      | some (er, r) =>
        match decFld decHeaderV hdr0 r with
        | none => none
        | some (h, r) =>
          match decFld getU64 (W64 0) r with
          | none => none
          | some (tm, r) =>
            match decFld getU64 (W64 0) r with
            | none => none
            | some (ll, r) =>
              match decFld decBool false r with
              | none => none
              | some (sc, r) =>
                match decFld decBool false r with
                | none => none
                | some (nr, r) => some (⟨fl, er, h, tm, ll, sc, nr⟩, r)

/-- The pure `VoteReq` decoder. -/
def decVoteReqV (bs : List w8) : Option (VoteReqV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decHeaderV hdr0 r with
    | none => none
    | some (h, r) =>
      match decFld getU64 (W64 0) r with
      | none => none
      | some (tm, r) =>
        match decFld decBytes [] r with
        | none => none
        | some (cd, r) =>
          match decFld getU64 (W64 0) r with
          | none => none
          | some (li, r) =>
            match decFld getU64 (W64 0) r with
            | none => none
            | some (lt, r) =>
              match decFld decBool false r with
              | none => none
              | some (tr, r) => some (⟨h, tm, cd, li, lt, tr⟩, r)

/-- The pure `VoteResp` decoder. -/
def decVoteRespV (bs : List w8) : Option (VoteRespV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decBool false r with
    | none => none
    | some (fl, r) =>
      match decFld getTag [] r with
      | none => none
      | some (er, r) =>
        match decFld decHeaderV hdr0 r with
        | none => none
        | some (h, r) =>
          match decFld getU64 (W64 0) r with
          | none => none
          | some (tm, r) =>
            match decFld decBytes [] r with
            | none => none
            | some (ps, r) =>
              match decFld decBool false r with
              | none => none
              | some (gr, r) => some (⟨fl, er, h, tm, ps, gr⟩, r)

/-- The pure `PreVoteReq` decoder. -/
def decPreVoteReqV (bs : List w8) : Option (PreVoteReqV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decHeaderV hdr0 r with
    | none => none
    | some (h, r) =>
      match decFld getU64 (W64 0) r with
      | none => none
      | some (tm, r) =>
        match decFld getU64 (W64 0) r with
        | none => none
        | some (li, r) =>
          match decFld getU64 (W64 0) r with
          | none => none
          | some (lt, r) => some (⟨h, tm, li, lt⟩, r)

/-- The pure `PreVoteResp` decoder. -/
def decPreVoteRespV (bs : List w8) : Option (PreVoteRespV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decBool false r with
    | none => none
    | some (fl, r) =>
      match decFld getTag [] r with
      | none => none
      | some (er, r) =>
        match decFld decHeaderV hdr0 r with
        | none => none
        | some (h, r) =>
          match decFld getU64 (W64 0) r with
          | none => none
          | some (tm, r) =>
            match decFld decBool false r with
            | none => none
            | some (gr, r) => some (⟨fl, er, h, tm, gr⟩, r)

/-- The pure `SnapReq` decoder. -/
def decSnapReqV (bs : List w8) : Option (SnapReqV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decHeaderV hdr0 r with
    | none => none
    | some (h, r) =>
      match decFld getU64 (W64 0) r with
      | none => none
      | some (vr, r) =>
        match decFld getU64 (W64 0) r with
        | none => none
        | some (tm, r) =>
          match decFld decBytes [] r with
          | none => none
          | some (ld, r) =>
            match decFld getU64 (W64 0) r with
            | none => none
            | some (li, r) =>
              match decFld getU64 (W64 0) r with
              | none => none
              | some (lt, r) =>
                match decFld decBytes [] r with
                | none => none
                | some (ps, r) =>
                  match decFld decBytes [] r with
                  | none => none
                  | some (cf, r) =>
                    match decFld getU64 (W64 0) r with
                    | none => none
                    | some (ci, r) =>
                      match decFld getU64 (W64 0) r with
                      | none => none
                      | some (sz, r) =>
                        match decFld decBytes [] r with
                        | none => none
                        | some (dt, r) => some (⟨h, vr, tm, ld, li, lt, ps, cf, ci, sz, dt⟩, r)

/-- The pure `SnapResp` decoder. -/
def decSnapRespV (bs : List w8) : Option (SnapRespV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decBool false r with
    | none => none
    | some (fl, r) =>
      match decFld getTag [] r with
      | none => none
      | some (er, r) =>
        match decFld decHeaderV hdr0 r with
        | none => none
        | some (h, r) =>
          match decFld getU64 (W64 0) r with
          | none => none
          | some (tm, r) =>
            match decFld decBool false r with
            | none => none
            | some (sc, r) => some (⟨fl, er, h, tm, sc⟩, r)

/-- The pure `TimeoutReq` decoder (its header's value). -/
def decTimeoutReqV (bs : List w8) : Option (HdrV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decHeaderV hdr0 r with
    | none => none
    | some (h, r) => some (h, r)

/-- The pure `TimeoutResp` decoder. -/
def decTimeoutRespV (bs : List w8) : Option (TimeoutRespV × List w8) :=
  match decStructHdr bs with
  | none => none
  | some r =>
    match decFld decBool false r with
    | none => none
    | some (fl, r) =>
      match decFld getTag [] r with
      | none => none
      | some (er, r) =>
        match decFld decHeaderV hdr0 r with
        | none => none
        | some (h, r) => some (⟨fl, er, h⟩, r)

/-! ## Round trips -/

theorem getU64_enc (x : w64) (rest : List w8) : getU64 (u64Le x ++ rest) = some (x, rest) := by
  unfold getU64
  rw [ite_eq_left (by simp [u64Le_length])]
  have h8 := u64Le_length x
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
    u64Le_to_word]

theorem w64_len (n : Nat) (h : n < 2 ^ 64) : uint.nat (W64 n) = n := by
  show (BitVec.ofNat 64 n).toNat = n
  simp only [BitVec.toNat_ofNat]; omega

theorem getTag_encStr (s : GoString) (rest : List w8) (hl : (rpctransport.encStr s ++ rest).length < 2 ^ 64) :
    getTag (rpctransport.encStr s ++ rest) = some (s, rest) := by
  have hs : s.length < 2 ^ 64 := by
    simp only [rpctransport.encStr, List.length_append, u64Le_length] at hl; omega
  unfold getTag rpctransport.encStr
  rw [List.append_assoc, getU64_enc]
  simp only [w64_len _ hs, List.length_append, Nat.le_add_right, ite_true, List.take_left',
    List.drop_left']

theorem decU8_enc (c : w8) (rest : List w8) :
    decU8 (u64Le (W64 (uint.Z c)) ++ rest) = some (c, rest) := by
  unfold decU8
  rw [getU64_enc]
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

theorem len_le_bytesFlat (l : List w8) :
    l.length ≤ (l.map fun c => u64Le (W64 (uint.Z c))).flatten.length := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      u64Le_length]; omega

theorem decBytes_enc (x rest : List w8) (hl : (encBytes x ++ rest).length < 2 ^ 64) :
    decBytes (encBytes x ++ rest) = some (x, rest) := by
  have h2 := len_le_bytesFlat x
  have hx : x.length < 2 ^ 64 := by
    simp only [encBytes, List.length_append, u64Le_length] at hl; omega
  unfold decBytes encBytes
  rw [List.append_assoc, getU64_enc]
  have hle : x.length ≤ ((x.map fun c => u64Le (W64 (uint.Z c))).flatten ++ rest).length := by
    simp only [List.length_append]; omega
  simp only [w64_len _ hx, hle, ↓reduceIte, decU8sGo_enc, List.nil_append]

theorem decBool_enc (b : Bool) (rest : List w8) : decBool (encBool b ++ rest) = some (b, rest) := by
  cases b <;> simp [decBool, encBool] <;> decide

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

theorem fld_len_le (sent : Bool) (body rest : List w8) (h : sent = true) :
    (body ++ rest).length ≤ (fld sent body ++ rest).length := by
  subst h; simp [fld]

theorem decFld_fU64 (v : w64) (rest : List w8) :
    decFld getU64 (W64 0) (fU64 v ++ rest) = some (v, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact getU64_enc v rest

theorem decFld_fU8 (v : w8) (rest : List w8) :
    decFld decU8 (W8 0) (fU8 v ++ rest) = some (v, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact decU8_enc v rest

theorem decFld_fBool (v : Bool) (rest : List w8) :
    decFld decBool false (fBool v ++ rest) = some (v, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact decBool_enc v rest

theorem decFld_fStr (s rest : List w8) (hl : (fStr s ++ rest).length < 2 ^ 64) :
    decFld getTag [] (fStr s ++ rest) = some (s, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro hs; exact getTag_encStr s rest (Nat.lt_of_le_of_lt (fld_len_le _ _ _ hs) hl)

theorem decFld_fBytes (x rest : List w8) (hl : (fBytes x ++ rest).length < 2 ^ 64) :
    decFld decBytes [] (fBytes x ++ rest) = some (x, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro hs; exact decBytes_enc x rest (Nat.lt_of_le_of_lt (fld_len_le _ _ _ hs) hl)

/-- The length side conditions of a round trip: a suffix is no longer than the whole. -/
macro "len_tac" : tactic =>
  `(tactic| (simp only [List.length_append, List.length_cons, List.cons_append] at *; omega))

theorem decHeaderV_enc (h : HdrV) (rest : List w8) (hl : (encHdr h ++ rest).length < 2 ^ 64) :
    decHeaderV (encHdr h ++ rest) = some (h, rest) := by
  have e : encHdr h ++ rest = W8 1 :: (fU64 h.pv ++ (fBytes h.id ++ (fBytes h.addr ++ rest))) := by
    simp [encHdr, strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decHeaderV, decStructHdr, ↓reduceIte, decFld_fU64,
    decFld_fBytes, decFld_fBytes]

theorem decFld_fStruct {α : Type} (d : List w8 → Option (α × List w8)) (v0 v : α)
    (body rest : List w8) (h : d (body ++ rest) = some (v, rest)) :
    decFld d v0 (fStruct body ++ rest) = some (v, rest) :=
  decFld_fld d v0 v true body rest nofun (fun _ => h)

theorem decFld_fHdr (h : HdrV) (rest : List w8) (hl : (fStruct (encHdr h) ++ rest).length < 2 ^ 64) :
    decFld decHeaderV hdr0 (fStruct (encHdr h) ++ rest) = some (h, rest) := by
  apply decFld_fStruct
  apply decHeaderV_enc
  simp only [fStruct, fld, ↓reduceIte, List.cons_append, List.length_cons] at hl; omega

theorem decEntV_enc (e : EntV) (rest : List w8) (hl : (encEnt e ++ rest).length < 2 ^ 64) :
    decEntV (encEnt e ++ rest) = some (e, rest) := by
  have e' : encEnt e ++ rest = W8 1 :: (fU64 e.index ++ (fU64 e.term ++ (fU8 e.ty ++
      (fBytes e.data ++ (fBytes e.ext ++ rest))))) := by
    simp [encEnt, strct]
  rw [e'] at hl ⊢
  simp (disch := len_tac) only [decEntV, decStructHdr, ↓reduceIte, decFld_fU64, decFld_fU8,
    decFld_fBytes, decFld_fBytes]

theorem decEntsGo_enc (es acc : List EntV) (rest : List w8)
    (hl : ((es.map encEnt).flatten ++ rest).length < 2 ^ 64) :
    decEntsGo es.length acc ((es.map encEnt).flatten ++ rest) = some (acc ++ es, rest) := by
  induction es generalizing acc with
  | nil => simp [decEntsGo]
  | cons e es ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc] at hl ⊢
    simp only [decEntsGo, decEntV_enc e _ hl]
    rw [ih (acc ++ [e]) (by simp only [List.length_append] at hl ⊢; omega)]
    simp

theorem count_le_ents (es : List EntV) : es.length ≤ (es.map encEnt).flatten.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have : 0 < (encEnt e).length := by simp [encEnt, strct]
    omega

theorem decEnts_enc (es : List EntV) (rest : List w8)
    (hl : (encU64 (W64 es.length) ++ (es.map encEnt).flatten ++ rest).length < 2 ^ 64) :
    decEnts (encU64 (W64 es.length) ++ (es.map encEnt).flatten ++ rest) = some (es, rest) := by
  have hc := count_le_ents es
  have hn : es.length < 2 ^ 64 := by
    simp only [encU64, List.length_append, u64Le_length] at hl; omega
  unfold decEnts encU64
  rw [List.append_assoc, getU64_enc]
  have hle : es.length ≤ ((es.map encEnt).flatten ++ rest).length := by
    simp only [List.length_append]; omega
  simp only [w64_len _ hn, hle, ↓reduceIte]
  rw [decEntsGo_enc es [] rest (by simp only [encU64, List.length_append, u64Le_length] at hl ⊢; omega)]
  simp

theorem decFld_fEnts (es : List EntV) (rest : List w8) (hl : (fEnts es ++ rest).length < 2 ^ 64) :
    decFld decEnts [] (fEnts es ++ rest) = some (es, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro hs
    have hl' := Nat.lt_of_le_of_lt (fld_len_le _ _ _ hs) hl
    have hc := count_le_ents es
    have hn : es.length < 2 ^ 64 := by
      simp only [encU64, List.length_append, u64Le_length] at hl'; omega
    unfold decEnts encU64
    rw [List.append_assoc, getU64_enc]
    have hle : es.length ≤ ((es.map encEnt).flatten ++ rest).length := by
      simp only [List.length_append]; omega
    simp only [w64_len _ hn, hle, ↓reduceIte]
    rw [decEntsGo_enc es [] rest (by simp only [encU64, List.length_append, u64Le_length] at hl' ⊢; omega)]
    simp

theorem decAEReqV_enc (v : AEReqV) (rest : List w8)
    (hl : (strct [fStruct (encHdr v.hdr), fU64 v.term, fBytes v.leader, fU64 v.prev, fU64 v.prevTerm,
      fEnts v.ents, fU64 v.lci] ++ rest).length < 2 ^ 64) :
    decAEReqV (strct [fStruct (encHdr v.hdr), fU64 v.term, fBytes v.leader, fU64 v.prev,
      fU64 v.prevTerm, fEnts v.ents, fU64 v.lci] ++ rest) = some (v, rest) := by
  have e : strct [fStruct (encHdr v.hdr), fU64 v.term, fBytes v.leader, fU64 v.prev, fU64 v.prevTerm,
      fEnts v.ents, fU64 v.lci] ++ rest = W8 1 :: (fStruct (encHdr v.hdr) ++ (fU64 v.term ++
      (fBytes v.leader ++ (fU64 v.prev ++ (fU64 v.prevTerm ++ (fEnts v.ents ++ (fU64 v.lci ++
      rest))))))) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decAEReqV, decStructHdr, ↓reduceIte, decFld_fHdr, decFld_fU64,
    decFld_fBytes, decFld_fEnts]

theorem decAERespV_enc (v : AERespV) (rest : List w8)
    (hl : (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fU64 v.lastLog,
      fBool v.success, fBool v.noRetry] ++ rest).length < 2 ^ 64) :
    decAERespV (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term,
      fU64 v.lastLog, fBool v.success, fBool v.noRetry] ++ rest) = some (v, rest) := by
  have e : strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fU64 v.lastLog,
      fBool v.success, fBool v.noRetry] ++ rest = W8 1 :: (fBool v.failed ++ (fStr v.err ++
      (fStruct (encHdr v.hdr) ++ (fU64 v.term ++ (fU64 v.lastLog ++ (fBool v.success ++
      (fBool v.noRetry ++ rest))))))) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decAERespV, decStructHdr, ↓reduceIte, decFld_fBool, decFld_fStr,
    decFld_fHdr, decFld_fU64]

theorem decVoteReqV_enc (v : VoteReqV) (rest : List w8)
    (hl : (strct [fStruct (encHdr v.hdr), fU64 v.term, fBytes v.cand, fU64 v.lastIdx, fU64 v.lastTerm,
      fBool v.transfer] ++ rest).length < 2 ^ 64) :
    decVoteReqV (strct [fStruct (encHdr v.hdr), fU64 v.term, fBytes v.cand, fU64 v.lastIdx,
      fU64 v.lastTerm, fBool v.transfer] ++ rest) = some (v, rest) := by
  have e : strct [fStruct (encHdr v.hdr), fU64 v.term, fBytes v.cand, fU64 v.lastIdx, fU64 v.lastTerm,
      fBool v.transfer] ++ rest = W8 1 :: (fStruct (encHdr v.hdr) ++ (fU64 v.term ++
      (fBytes v.cand ++ (fU64 v.lastIdx ++ (fU64 v.lastTerm ++ (fBool v.transfer ++ rest)))))) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decVoteReqV, decStructHdr, ↓reduceIte, decFld_fHdr, decFld_fU64,
    decFld_fBytes, decFld_fBool]

theorem decVoteRespV_enc (v : VoteRespV) (rest : List w8)
    (hl : (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fBytes v.peers,
      fBool v.granted] ++ rest).length < 2 ^ 64) :
    decVoteRespV (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term,
      fBytes v.peers, fBool v.granted] ++ rest) = some (v, rest) := by
  have e : strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fBytes v.peers,
      fBool v.granted] ++ rest = W8 1 :: (fBool v.failed ++ (fStr v.err ++
      (fStruct (encHdr v.hdr) ++ (fU64 v.term ++ (fBytes v.peers ++ (fBool v.granted ++
      rest)))))) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decVoteRespV, decStructHdr, ↓reduceIte, decFld_fBool, decFld_fStr,
    decFld_fHdr, decFld_fU64, decFld_fBytes]

theorem decPreVoteReqV_enc (v : PreVoteReqV) (rest : List w8)
    (hl : (strct [fStruct (encHdr v.hdr), fU64 v.term, fU64 v.lastIdx, fU64 v.lastTerm] ++
      rest).length < 2 ^ 64) :
    decPreVoteReqV (strct [fStruct (encHdr v.hdr), fU64 v.term, fU64 v.lastIdx, fU64 v.lastTerm] ++
      rest) = some (v, rest) := by
  have e : strct [fStruct (encHdr v.hdr), fU64 v.term, fU64 v.lastIdx, fU64 v.lastTerm] ++ rest =
      W8 1 :: (fStruct (encHdr v.hdr) ++ (fU64 v.term ++ (fU64 v.lastIdx ++ (fU64 v.lastTerm ++
      rest)))) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decPreVoteReqV, decStructHdr, ↓reduceIte, decFld_fHdr, decFld_fU64]

theorem decPreVoteRespV_enc (v : PreVoteRespV) (rest : List w8)
    (hl : (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fBool v.granted] ++
      rest).length < 2 ^ 64) :
    decPreVoteRespV (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term,
      fBool v.granted] ++ rest) = some (v, rest) := by
  have e : strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fBool v.granted] ++
      rest = W8 1 :: (fBool v.failed ++ (fStr v.err ++ (fStruct (encHdr v.hdr) ++ (fU64 v.term ++
      (fBool v.granted ++ rest))))) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decPreVoteRespV, decStructHdr, ↓reduceIte, decFld_fBool,
    decFld_fStr, decFld_fHdr, decFld_fU64]

theorem decSnapReqV_enc (v : SnapReqV) (rest : List w8)
    (hl : (strct [fStruct (encHdr v.hdr), fU64 v.version, fU64 v.term, fBytes v.leader, fU64 v.lastIdx,
      fU64 v.lastTerm, fBytes v.peers, fBytes v.cfg, fU64 v.cfgIdx, fU64 v.size, fBytes v.data] ++
      rest).length < 2 ^ 64) :
    decSnapReqV (strct [fStruct (encHdr v.hdr), fU64 v.version, fU64 v.term, fBytes v.leader,
      fU64 v.lastIdx, fU64 v.lastTerm, fBytes v.peers, fBytes v.cfg, fU64 v.cfgIdx, fU64 v.size,
      fBytes v.data] ++ rest) = some (v, rest) := by
  have e : strct [fStruct (encHdr v.hdr), fU64 v.version, fU64 v.term, fBytes v.leader, fU64 v.lastIdx,
      fU64 v.lastTerm, fBytes v.peers, fBytes v.cfg, fU64 v.cfgIdx, fU64 v.size, fBytes v.data] ++
      rest = W8 1 :: (fStruct (encHdr v.hdr) ++ (fU64 v.version ++ (fU64 v.term ++
      (fBytes v.leader ++ (fU64 v.lastIdx ++ (fU64 v.lastTerm ++ (fBytes v.peers ++ (fBytes v.cfg ++
      (fU64 v.cfgIdx ++ (fU64 v.size ++ (fBytes v.data ++ rest))))))))))) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decSnapReqV, decStructHdr, ↓reduceIte, decFld_fHdr, decFld_fU64,
    decFld_fBytes, decFld_fBytes,
    decFld_fBytes, decFld_fBytes]

theorem decSnapRespV_enc (v : SnapRespV) (rest : List w8)
    (hl : (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fBool v.success] ++
      rest).length < 2 ^ 64) :
    decSnapRespV (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term,
      fBool v.success] ++ rest) = some (v, rest) := by
  have e : strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr), fU64 v.term, fBool v.success] ++
      rest = W8 1 :: (fBool v.failed ++ (fStr v.err ++ (fStruct (encHdr v.hdr) ++ (fU64 v.term ++
      (fBool v.success ++ rest))))) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decSnapRespV, decStructHdr, ↓reduceIte, decFld_fBool, decFld_fStr,
    decFld_fHdr, decFld_fU64]

theorem decTimeoutReqV_enc (h : HdrV) (rest : List w8)
    (hl : (strct [fStruct (encHdr h)] ++ rest).length < 2 ^ 64) :
    decTimeoutReqV (strct [fStruct (encHdr h)] ++ rest) = some (h, rest) := by
  have e : strct [fStruct (encHdr h)] ++ rest = W8 1 :: (fStruct (encHdr h) ++ rest) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decTimeoutReqV, decStructHdr, ↓reduceIte, decFld_fHdr]

theorem decTimeoutRespV_enc (v : TimeoutRespV) (rest : List w8)
    (hl : (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr)] ++ rest).length < 2 ^ 64) :
    decTimeoutRespV (strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr)] ++ rest) =
      some (v, rest) := by
  have e : strct [fBool v.failed, fStr v.err, fStruct (encHdr v.hdr)] ++ rest =
      W8 1 :: (fBool v.failed ++ (fStr v.err ++ (fStruct (encHdr v.hdr) ++ rest))) := by
    simp [strct]
  rw [e] at hl ⊢
  simp (disch := len_tac) only [decTimeoutRespV, decStructHdr, ↓reduceIte, decFld_fBool, decFld_fStr,
    decFld_fHdr]

/-- `rpcGetTag` of a top-level encoding: its type's name, then the body. -/
theorem getTag_tagged (t body : List w8) (hl : (tagged t body).length < 2 ^ 64) :
    getTag (tagged t body) = some (t, body) := by
  unfold tagged at *
  exact getTag_encStr t body hl


/-! ## The requests' encodings are injective (below the bound of a slice's bytes) -/

theorem tagged_body_inj {t b b' : List w8} (h : tagged t b = tagged t b') : b = b' := by
  unfold tagged at h; exact List.append_cancel_left h

theorem encAEReq_inj (v v' : AEReqV) (hl : (encAEReq v).length < 2 ^ 64) (h : encAEReq v = encAEReq v') :
    v = v' := by
  have hb := tagged_body_inj h
  have h1 := decAEReqV_enc v [] (by unfold encAEReq tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  have h2 := decAEReqV_enc v' [] (by rw [← hb]; unfold encAEReq tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  rw [← hb] at h2
  rw [h1] at h2
  cases h2; rfl

theorem encVoteReq_inj (v v' : VoteReqV) (hl : (encVoteReq v).length < 2 ^ 64) (h : encVoteReq v = encVoteReq v') :
    v = v' := by
  have hb := tagged_body_inj h
  have h1 := decVoteReqV_enc v [] (by unfold encVoteReq tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  have h2 := decVoteReqV_enc v' [] (by rw [← hb]; unfold encVoteReq tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  rw [← hb] at h2
  rw [h1] at h2
  cases h2; rfl

theorem encPreVoteReq_inj (v v' : PreVoteReqV) (hl : (encPreVoteReq v).length < 2 ^ 64) (h : encPreVoteReq v = encPreVoteReq v') :
    v = v' := by
  have hb := tagged_body_inj h
  have h1 := decPreVoteReqV_enc v [] (by unfold encPreVoteReq tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  have h2 := decPreVoteReqV_enc v' [] (by rw [← hb]; unfold encPreVoteReq tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  rw [← hb] at h2
  rw [h1] at h2
  cases h2; rfl

theorem encSnapReq_inj (v v' : SnapReqV) (hl : (encSnapReq v).length < 2 ^ 64) (h : encSnapReq v = encSnapReq v') :
    v = v' := by
  have hb := tagged_body_inj h
  have h1 := decSnapReqV_enc v [] (by unfold encSnapReq tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  have h2 := decSnapReqV_enc v' [] (by rw [← hb]; unfold encSnapReq tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  rw [← hb] at h2
  rw [h1] at h2
  cases h2; rfl

theorem encTimeoutReq_inj (v v' : HdrV) (hl : (encTimeoutReq v).length < 2 ^ 64) (h : encTimeoutReq v = encTimeoutReq v') :
    v = v' := by
  have hb := tagged_body_inj h
  have h1 := decTimeoutReqV_enc v [] (by unfold encTimeoutReq tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  have h2 := decTimeoutReqV_enc v' [] (by rw [← hb]; unfold encTimeoutReq tagged at hl; simp only [List.append_nil, List.length_append] at hl ⊢; omega)
  rw [← hb] at h2
  rw [h1] at h2
  cases h2; rfl

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
