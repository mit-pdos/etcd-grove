/-
QuePaxa's protobuf messages: pure values, their encodings, their Go representations, and the
kit's codec (interface of stage 1, `notes/stage1-plan.md`).

* **Values.** One pure record per message shape (`Batch` for the three client-batch messages,
  `DSlot` for both decided-slot messages, `Prop'`, `PM`, `RRProp`, `RR`, ...). Integers are the
  Go `int64` fields' values (`sint.Z`); strings are Go strings.
* **Encodings** (`enc*`): exactly `pb_gen.go`'s `pbenc_*` (proto3: a field equal to its zero value
  omitted, except repeated elements and present sub-messages; fields in number order; an
  `int64` as the varint of its two's complement).
* **Representations** (`rep*`): the Go struct at a pointer, read with fraction `dq`, with its
  nested pointers and slices; no unknown fields (`unknownFields` empty, in every nested message:
  protobuf's `Marshal` appends a message's unknown fields to its encoding, `internal/impl/
  encode.go`, so `enc*` is the encoding only of a message without them); the protobuf runtime
  fields `state`, `sizeCache` arbitrary.
* **The codec's preconditions** (`marshalPre`, `unmarshalPre`): `marshalPre m Ψ` is a message
  of one of the program's kinds, whose encoding, if well formed (valid UTF-8 strings), is
  `Ψ (some _)`'s argument, its representation given back; `unmarshalPre bs m Ψ` is a fresh zero
  message of one of the kinds, and on success, when `bs` is the encoding of a well formed value
  (so that it carries no unknown fields), its decoded value `v` with: any well formed value whose
  encoding is `bs` is `v`. (A successful decoding of other bytes gives nothing: protobuf keeps
  their unknown fields.)

Changed against the lab (notes/dsv-quepaxa.md): the lab's `pbCodec` instance of its protobuf
model's `PbCodec` (its generated codec `pbMarshal`/`pbUnmarshal`, proved by `kitCodecOk_holds`) is
gone; `proto.Marshal`/`proto.Unmarshal` (the real protobuf here) are hypotheses of the port, stated
with `marshalPre`/`unmarshalPre` (`Hyp.lean`). The representations are over the translation of
the fork's own `.pb.go` files (the same fields as the lab's).
-/
module

public import Dsverify.Proof.raxos.Pure.Smr
public import Dsverify.Proof.raxos.replica.src.Base
public import Dsverify.Proof.raxos.proto.client.Base

@[expose] public section

noncomputable section

namespace Perennial.raxos.msg

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open Perennial.raxos.pure (Batch)

/-! ## Values -/

/-- A decided slot (`ProposerMessage_DecidedSlot`, `Decisions_DecidedSlot`). -/
structure DSlot where
  index : Int
  ids : List GoString
  proposer : Int
deriving DecidableEq, Inhabited

/-- A proposal (`ProposerMessage_Proposal`). -/
structure Prop' where
  prio : Int
  pid : Int
  tid : Int
  ids : List GoString
  batches : List Batch
deriving DecidableEq, Inhabited

/-- A proposer's message (`ProposerMessage`). -/
structure PM where
  sender : Int
  index : Int
  p : Option Prop'
  s : Int
  slots : List DSlot
deriving DecidableEq, Inhabited

/-- A recorder's proposal in a reply (`RecorderResponse_Proposal`). -/
structure RRProp where
  prio : Int
  pid : Int
  tid : Int
  ids : List GoString
deriving DecidableEq, Inhabited

/-- A recorder's reply (`RecorderResponse`). -/
structure RR where
  s : Int
  f : Option RRProp
  m : Option RRProp
  notFound : Bool
deriving DecidableEq, Inhabited

/-! ## Encodings (`pb_gen.go`, `harness/pbcodec`) -/

/-- `AppendVarint`'s bytes for `v < 2^64`. -/
def varint (v : Nat) : List w8 :=
  if h : v < 128 then [W8 v] else W8 (v % 128 + 128) :: varint (v / 128)
termination_by v
decreasing_by omega

/-- An `int64` as `uint64(x)`. -/
def u64 (x : Int) : Nat := (x % 2 ^ 64).toNat

/-- A tag: field `num`, wire type `typ`. -/
def tag (num typ : Nat) : List w8 := varint (num * 8 + typ)

/-- A varint field, omitted at zero. -/
def fVarint (num : Nat) (x : Int) : List w8 := if x = 0 then [] else tag num 0 ++ varint (u64 x)

/-- A length-delimited field (always written: a repeated element, a present sub-message). -/
def fBytes (num : Nat) (b : List w8) : List w8 := tag num 2 ++ varint b.length ++ b

/-- A singular string field, omitted when empty. -/
def fStr (num : Nat) (s : GoString) : List w8 := if s = [] then [] else fBytes num s

/-- A bool field, omitted when false. -/
def fBool (num : Nat) (b : Bool) : List w8 := if b then tag num 0 ++ varint 1 else []

/-- A repeated string field. -/
def fStrs (num : Nat) (ss : List GoString) : List w8 := (ss.map (fBytes num)).flatten

/-- A single message (`*_SingleMessage`): its string. -/
def encSingle (m : GoString) : List w8 := fStr 1 m

/-- A client batch (`ProposerMessage_ClientBatch`, `DecideResponse_ClientBatch`,
`client.ClientBatch`: the same fields). -/
def encBatch (b : Batch) : List w8 :=
  fVarint 1 b.sender ++ (b.cmds.map (fun m => fBytes 2 (encSingle m))).flatten ++ fStr 3 b.id

/-- A decided slot. -/
def encDSlot (d : DSlot) : List w8 := fVarint 1 d.index ++ fStrs 2 d.ids ++ fVarint 3 d.proposer

def encProp (p : Prop') : List w8 :=
  fVarint 1 p.prio ++ fVarint 2 p.pid ++ fVarint 3 p.tid ++ fStrs 4 p.ids ++
    (p.batches.map (fun b => fBytes 5 (encBatch b))).flatten

def encPM (m : PM) : List w8 :=
  fVarint 1 m.sender ++ fVarint 2 m.index ++
    (match m.p with | some p => fBytes 3 (encProp p) | none => []) ++
    fVarint 4 m.s ++ (m.slots.map (fun d => fBytes 5 (encDSlot d))).flatten

def encRRProp (p : RRProp) : List w8 :=
  fVarint 1 p.prio ++ fVarint 2 p.pid ++ fVarint 3 p.tid ++ fStrs 4 p.ids

def encRR (r : RR) : List w8 :=
  fVarint 1 r.s ++ (match r.f with | some p => fBytes 2 (encRRProp p) | none => []) ++
    (match r.m with | some p => fBytes 3 (encRRProp p) | none => []) ++ fBool 4 r.notFound

/-- `DecideRequest`: the ids. -/
def encDReq (ids : List GoString) : List w8 := fStrs 1 ids

/-- `DecideResponse`: the batches. -/
def encDResp (bs : List Batch) : List w8 := (bs.map (fun b => fBytes 1 (encBatch b))).flatten

/-- `Decisions`: the decided slots. -/
def encDecs (ds : List DSlot) : List w8 := (ds.map (fun d => fBytes 5 (encDSlot d))).flatten

/-- `Empty`. -/
def encEmpty : List w8 := []

/-! ## Well-formed values (the codec's premise) -/

/-- An `int64`'s value. -/
def i64Ok (x : Int) : Prop := -2 ^ 63 ≤ x ∧ x < 2 ^ 63

/-- A continuation byte. -/
def contB (c : w8) : Bool := 0x80 ≤ c.toNat ∧ c.toNat ≤ 0xbf

/-- Valid UTF-8 (`harness/pbcodec`'s `ValidUTF8`, Go's `unicode/utf8.Valid`). -/
def validUtf8 : List w8 → Bool
  | [] => true
  | c :: rest =>
    if c.toNat < 0x80 then validUtf8 rest
    else if c.toNat < 0xc2 ∨ c.toNat > 0xf4 then false
    else if c.toNat < 0xe0 then
      match rest with
      | c1 :: r => contB c1 && validUtf8 r
      | [] => false
    else
      let lo := if c.toNat = 0xe0 then 0xa0 else if c.toNat = 0xf0 then 0x90 else 0x80
      let hi := if c.toNat = 0xed then 0x9f else if c.toNat = 0xf4 then 0x8f else 0xbf
      match rest with
      | c1 :: r =>
        if c1.toNat < lo ∨ c1.toNat > hi then false
        else if c.toNat < 0xf0 then
          match r with
          | c2 :: r' => contB c2 && validUtf8 r'
          | [] => false
        else
          match r with
          | c2 :: c3 :: r' => contB c2 && contB c3 && validUtf8 r'
          | _ => false
      | [] => false

/-- A string the codec accepts: valid UTF-8. -/
def strOk (s : GoString) : Prop := validUtf8 s = true

/-- An ASCII string (valid UTF-8). -/
def asciiOk (s : GoString) : Prop := ∀ b ∈ s, b.toNat < 128

def batchOk (b : Batch) : Prop := i64Ok b.sender ∧ strOk b.id ∧ ∀ m ∈ b.cmds, strOk m
/-- A batch the codec encodes into a frame: well formed, its encoding below `2^63` bytes (every
batch a replica holds came in such a frame or message). -/
def batchFit (b : Batch) : Prop := batchOk b ∧ (encBatch b).length < 2 ^ 63

def dslotOk (d : DSlot) : Prop := i64Ok d.index ∧ i64Ok d.proposer ∧ ∀ s ∈ d.ids, strOk s
def propOk (p : Prop') : Prop :=
  i64Ok p.prio ∧ i64Ok p.pid ∧ i64Ok p.tid ∧ (∀ s ∈ p.ids, strOk s) ∧ ∀ b ∈ p.batches, batchOk b
def pmOk (m : PM) : Prop :=
  i64Ok m.sender ∧ i64Ok m.index ∧ i64Ok m.s ∧ (∀ p, m.p = some p → propOk p) ∧
    ∀ d ∈ m.slots, dslotOk d
def rrPropOk (p : RRProp) : Prop :=
  i64Ok p.prio ∧ i64Ok p.pid ∧ i64Ok p.tid ∧ ∀ s ∈ p.ids, strOk s
def rrOk (r : RR) : Prop :=
  i64Ok r.s ∧ (∀ p, r.f = some p → rrPropOk p) ∧ (∀ p, r.m = some p → rrPropOk p)

/-! ## Go representations -/

section reps
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open raxos.replica.src in
/-- Pointers `ps` to single messages (of a type whose rep is `single`), one per string. -/
def repList {A : Type} (rep : Loc → DFrac → A → IProp GF) (ps : List Loc) (dq : DFrac)
    (xs : List A) : IProp GF :=
  iprop(⌜ps.length = xs.length⌝ ∗ [∗list] i ↦ p ∈ ps, ∃ x, ⌜xs[i]? = some x⌝ ∗ rep p dq x)

/-- `*ProposerMessage_ClientBatch_SingleMessage`. -/
def repPMSingle (l : Loc) (dq : DFrac) (m : GoString) : IProp GF :=
  iprop(∃ x : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage,
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ ⌜x.Message' = m⌝)

/-- `*ProposerMessage_ClientBatch`. -/
def repPMBatch (l : Loc) (dq : DFrac) (b : Batch) : IProp GF :=
  iprop(∃ (x : raxos.replica.src.ProposerMessage_ClientBatch) (ps : List Loc),
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ ⌜sint.Z x.Sender' = b.sender ∧ x.Id' = b.id⌝ ∗
    x.Messages' ↦*{dq} ps ∗ repList repPMSingle ps dq b.cmds)

/-- `*ProposerMessage_DecidedSlot`. -/
def repPMSlot (l : Loc) (dq : DFrac) (d : DSlot) : IProp GF :=
  iprop(∃ x : raxos.replica.src.ProposerMessage_DecidedSlot,
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.Index' = d.index ∧ sint.Z x.Proposer' = d.proposer⌝ ∗
    x.Ids' ↦*{dq} d.ids)

/-- `*ProposerMessage_Proposal`. -/
def repProp (l : Loc) (dq : DFrac) (p : Prop') : IProp GF :=
  iprop(∃ (x : raxos.replica.src.ProposerMessage_Proposal) (bps : List Loc),
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.Priority' = p.prio ∧ sint.Z x.ProposerId' = p.pid ∧ sint.Z x.ThreadId' = p.tid⌝ ∗
    x.Ids' ↦*{dq} p.ids ∗ x.ClientBatches' ↦*{dq} bps ∗ repList repPMBatch bps dq p.batches)

/-- `*ProposerMessage`. -/
def repPM (l : Loc) (dq : DFrac) (m : PM) : IProp GF :=
  iprop(∃ (x : raxos.replica.src.ProposerMessage) (sps : List Loc),
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.Sender' = m.sender ∧ sint.Z x.Index' = m.index ∧ sint.Z x.S' = m.s⌝ ∗
    (match m.p with
     | none => iprop(⌜x.P' = null⌝)
     | some p => repProp x.P' dq p) ∗
    x.DecidedSlots' ↦*{dq} sps ∗ repList repPMSlot sps dq m.slots)

/-- `*RecorderResponse_Proposal`. -/
def repRRProp (l : Loc) (dq : DFrac) (p : RRProp) : IProp GF :=
  iprop(∃ x : raxos.replica.src.RecorderResponse_Proposal,
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.Priority' = p.prio ∧ sint.Z x.ProposerId' = p.pid ∧ sint.Z x.ThreadId' = p.tid⌝ ∗
    x.Ids' ↦*{dq} p.ids)

/-- An optional sub-message at the pointer `l` (`nil`: absent). -/
def repOpt {A : Type} (rep : Loc → DFrac → A → IProp GF) (l : Loc) (dq : DFrac) :
    Option A → IProp GF
  | none => iprop(⌜l = null⌝)
  | some a => rep l dq a

/-- `*RecorderResponse`. -/
def repRR (l : Loc) (dq : DFrac) (r : RR) : IProp GF :=
  iprop(∃ x : raxos.replica.src.RecorderResponse,
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.S' = r.s ∧ x.ClientBatchesNotFound' = r.notFound⌝ ∗
    repOpt repRRProp x.F' dq r.f ∗ repOpt repRRProp x.M' dq r.m)

/-- `*DecideRequest`. -/
def repDReq (l : Loc) (dq : DFrac) (ids : List GoString) : IProp GF :=
  iprop(∃ x : raxos.replica.src.DecideRequest,
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ x.Ids' ↦*{dq} ids)

/-- `*DecideResponse_ClientBatch_SingleMessage`. -/
def repDRSingle (l : Loc) (dq : DFrac) (m : GoString) : IProp GF :=
  iprop(∃ x : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage,
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ ⌜x.Message' = m⌝)

/-- `*DecideResponse_ClientBatch`. -/
def repDRBatch (l : Loc) (dq : DFrac) (b : Batch) : IProp GF :=
  iprop(∃ (x : raxos.replica.src.DecideResponse_ClientBatch) (ps : List Loc),
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ ⌜sint.Z x.Sender' = b.sender ∧ x.Id' = b.id⌝ ∗
    x.Messages' ↦*{dq} ps ∗ repList repDRSingle ps dq b.cmds)

/-- `*DecideResponse`. -/
def repDResp (l : Loc) (dq : DFrac) (bs : List Batch) : IProp GF :=
  iprop(∃ (x : raxos.replica.src.DecideResponse) (ps : List Loc),
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ x.ClientBatches' ↦*{dq} ps ∗
    repList repDRBatch ps dq bs)

/-- `*Decisions_DecidedSlot`. -/
def repDecSlot (l : Loc) (dq : DFrac) (d : DSlot) : IProp GF :=
  iprop(∃ x : raxos.replica.src.Decisions_DecidedSlot,
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.Index' = d.index ∧ sint.Z x.Proposer' = d.proposer⌝ ∗
    x.Ids' ↦*{dq} d.ids)

/-- `*Decisions`. -/
def repDecs (l : Loc) (dq : DFrac) (ds : List DSlot) : IProp GF :=
  iprop(∃ (x : raxos.replica.src.Decisions) (ps : List Loc),
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ x.DecidedSlots' ↦*{dq} ps ∗
    repList repDecSlot ps dq ds)

/-- `*Empty`. -/
def repEmpty (l : Loc) (dq : DFrac) : IProp GF :=
  iprop(∃ x : raxos.replica.src.Empty, l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝)

/-- `*client.ClientBatch_SingleMessage`. -/
def repCSingle (l : Loc) (dq : DFrac) (m : GoString) : IProp GF :=
  iprop(∃ x : raxos.proto.client.ClientBatch_SingleMessage,
    l ↦{dq} x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ ⌜x.Message' = m⌝)

/-- A `client.ClientBatch` value's fields (its slice of messages read with `dq`), no unknown
fields. -/
def repCBVal (x : raxos.proto.client.ClientBatch) (dq : DFrac) (b : Batch) : IProp GF :=
  iprop(∃ ps : List Loc,
    ⌜sint.Z x.Sender' = b.sender ∧ x.Id' = b.id ∧ x.unknownFields'.len = W64 0⌝ ∗
    x.Messages' ↦*{dq} ps ∗ repList repCSingle ps dq b.cmds)

/-- `*client.ClientBatch`. -/
def repCB (l : Loc) (dq : DFrac) (b : Batch) : IProp GF :=
  iprop(∃ x : raxos.proto.client.ClientBatch, l ↦{dq} x ∗ repCBVal x dq b)

/-! ## The kinds of messages the program encodes and decodes, and the codec -/

/-- The interface holding the pointer `l` to a message of type `t`. -/
def ptrIface (t : go.GoType) (l : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType t) #l

/-- What the program marshals: a message of one of the kinds; its encoding if it is well formed
(valid UTF-8 strings), else the codec's error (`Ψ none`). -/
def marshalPre (m : GoInterface) (Ψ : Option (List w8) → IProp GF) : IProp GF :=
  iprop(
    (∃ l dq v, ⌜m = ptrIface raxos.replica.src.ProposerMessage.ty l⌝ ∗ repPM l dq v ∗
      (repPM l dq v -∗ ((⌜pmOk v⌝ -∗ Ψ (some (encPM v))) ∧ (⌜¬ (pmOk v)⌝ -∗ Ψ none)))) ∨
    (∃ l dq v, ⌜m = ptrIface raxos.replica.src.RecorderResponse.ty l⌝ ∗ repRR l dq v ∗
      (repRR l dq v -∗ ((⌜rrOk v⌝ -∗ Ψ (some (encRR v))) ∧ (⌜¬ (rrOk v)⌝ -∗ Ψ none)))) ∨
    (∃ l dq v, ⌜m = ptrIface raxos.replica.src.DecideRequest.ty l⌝ ∗
      repDReq l dq v ∗ (repDReq l dq v -∗ ((⌜∀ s ∈ v, strOk s⌝ -∗ Ψ (some (encDReq v))) ∧ (⌜¬ (∀ s ∈ v, strOk s)⌝ -∗ Ψ none)))) ∨
    (∃ l dq v, ⌜m = ptrIface raxos.replica.src.DecideResponse.ty l⌝ ∗
      repDResp l dq v ∗ (repDResp l dq v -∗ ((⌜∀ b ∈ v, batchOk b⌝ -∗ Ψ (some (encDResp v))) ∧ (⌜¬ (∀ b ∈ v, batchOk b)⌝ -∗ Ψ none)))) ∨
    (∃ l dq v, ⌜m = ptrIface raxos.replica.src.Decisions.ty l⌝ ∗
      repDecs l dq v ∗ (repDecs l dq v -∗ ((⌜∀ d ∈ v, dslotOk d⌝ -∗ Ψ (some (encDecs v))) ∧ (⌜¬ (∀ d ∈ v, dslotOk d)⌝ -∗ Ψ none)))) ∨
    (∃ l dq, ⌜m = ptrIface raxos.replica.src.Empty.ty l⌝ ∗ repEmpty l dq ∗
      (repEmpty l dq -∗ Ψ (some encEmpty))) ∨
    (∃ l dq v, ⌜m = ptrIface raxos.proto.client.ClientBatch.ty l⌝ ∗ repCB l dq v ∗
      (repCB l dq v -∗ ((⌜batchOk v⌝ -∗ Ψ (some (encBatch v))) ∧ (⌜¬ batchOk v⌝ -∗ Ψ none)))))

/-- Decoding into a fresh message of type `t` at `l` with value type `A`: on success the decoded
value `v` (owned, if `bs` is the encoding of a well formed value: only then does the message have
no unknown fields), which is any well formed value whose encoding is `bs`; on failure,
`Ψ false`. -/
def decInto {A : Type} (rep : Loc → DFrac → A → IProp GF) (ok : A → Prop) (enc : A → List w8)
    (bs : List w8) (l : Loc) (Ψ : Bool → IProp GF) : IProp GF :=
  iprop((∀ v, (⌜∃ v0, ok v0 ∧ enc v0 = bs⌝ -∗ rep l (DFrac.own 1) v) -∗
      ⌜∀ v0, ok v0 → enc v0 = bs → v = v0⌝ -∗ Ψ true) ∧
    Ψ false)

/-- What the program unmarshals into: a fresh zero message of one of the kinds. -/
def unmarshalPre (bs : List w8) (m : GoInterface) (Ψ : Bool → IProp GF) : IProp GF :=
  iprop(
    (∃ l, ⌜m = ptrIface raxos.replica.src.ProposerMessage.ty l⌝ ∗
      l ↦ (zero_val raxos.replica.src.ProposerMessage) ∗ decInto repPM pmOk encPM bs l Ψ) ∨
    (∃ l, ⌜m = ptrIface raxos.replica.src.RecorderResponse.ty l⌝ ∗
      l ↦ (zero_val raxos.replica.src.RecorderResponse) ∗ decInto repRR rrOk encRR bs l Ψ) ∨
    (∃ l, ⌜m = ptrIface raxos.replica.src.DecideRequest.ty l⌝ ∗
      l ↦ (zero_val raxos.replica.src.DecideRequest) ∗
      decInto repDReq (fun v => ∀ s ∈ v, strOk s) encDReq bs l Ψ) ∨
    (∃ l, ⌜m = ptrIface raxos.replica.src.DecideResponse.ty l⌝ ∗
      l ↦ (zero_val raxos.replica.src.DecideResponse) ∗
      decInto repDResp (fun v => ∀ b ∈ v, batchOk b) encDResp bs l Ψ) ∨
    (∃ l, ⌜m = ptrIface raxos.replica.src.Decisions.ty l⌝ ∗
      l ↦ (zero_val raxos.replica.src.Decisions) ∗
      decInto repDecs (fun v => ∀ d ∈ v, dslotOk d) encDecs bs l Ψ) ∨
    (∃ l, ⌜m = ptrIface raxos.replica.src.Empty.ty l⌝ ∗
      l ↦ (zero_val raxos.replica.src.Empty) ∗
      decInto (fun l dq (_ : Unit) => repEmpty l dq) (fun _ => True) (fun _ => encEmpty) bs l Ψ) ∨
    (∃ l, ⌜m = ptrIface raxos.proto.client.ClientBatch.ty l⌝ ∗
      l ↦ (zero_val raxos.proto.client.ClientBatch) ∗ decInto repCB batchOk encBatch bs l Ψ))

end reps

end Perennial.raxos.msg
