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
  encode.go`, so `enc*` is the encoding only of a message without them). Each message is a
  `pt*`: read with `dq = 1`, the whole struct (its protobuf runtime fields `state`, `sizeCache`
  arbitrary, owned); with any other `dq`, its other fields and the runtime fields in an invariant
  (protobuf writes them while marshalling: "Ownership of a message" below).
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

/-! ### Ownership of a message, and protobuf's runtime fields

protobuf-go (v1.36.12) writes two fields of a message the program never names: `proto.Marshal`
(and `proto.Size`, which gRPC's codec calls first) stores every message's `sizeCache` while
sizing it (`internal/impl/encode.go:67,123,128`, `atomic.StoreInt32`), and the generated
`ProtoReflect` stores its `state` on its first reflection (`pointer_unsafe.go:207-208`,
`StoreMessageInfo`, `atomic.StorePointer`). So a message read with a fraction cannot be the whole
struct's points-to. `pt*` is a message at `l` read with `dq`: owned (`dq = 1`), the whole struct
(the program may copy it: a struct load reads `state` and `sizeCache` too); shared (any other
`dq`), its other fields with `dq` (`fields*`) and the two runtime fields in an invariant
(`pbRtN`), which protobuf's atomic stores may open. Sharing an owned message allocates that
invariant (`pt*_persist`). (Review #24, finding 2.) -/

/-- The invariants holding shared messages' runtime fields. -/
def pbRtN : Namespace := ndot nroot "protobuf"

theorem discard_ne_own : (DFrac.discard : DFrac) ≠ DFrac.own 1 := by intro h; cases h

/-! ### `*ProposerMessage_ClientBatch_SingleMessage` -/

/-- The fields of a `*ProposerMessage_ClientBatch_SingleMessage` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsPMSingle (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' dq ∗
    "Message" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage go!"Message" l) v.Message' dq ∗
    "_" ∷ True)

theorem fieldsPMSingle_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) :
    fieldsPMSingle (GF := GF) l dq v ⊢ |==> fieldsPMSingle l .discard v := by
  unfold fieldsPMSingle
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Message;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsPMSingle_pers (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) :
    Persistent (fieldsPMSingle (GF := GF) l .discard v) := by
  unfold fieldsPMSingle; infer_instance

/-- Protobuf's runtime fields of a `*ProposerMessage_ClientBatch_SingleMessage` at `l`, owned. -/
def rtPMSingle (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*ProposerMessage_ClientBatch_SingleMessage` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptPMSingle (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsPMSingle l dq v ∗ inv pbRtN (rtPMSingle l))

theorem ptPMSingle_own (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) :
    ptPMSingle (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptPMSingle; exact if_pos rfl

theorem ptPMSingle_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) (h : dq ≠ DFrac.own 1) :
    ptPMSingle (GF := GF) l dq v = iprop(fieldsPMSingle l dq v ∗ inv pbRtN (rtPMSingle l)) := by
  unfold ptPMSingle; exact if_neg h

instance ptPMSingle_pers (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) :
    Persistent (ptPMSingle (GF := GF) l .discard v) := by
  rw [ptPMSingle_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*ProposerMessage_ClientBatch_SingleMessage`: an owned one gives its runtime fields to an invariant. -/
theorem ptPMSingle_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) :
    ptPMSingle (GF := GF) l dq v ⊢ |={E}=> ptPMSingle l .discard v := by
  rw [ptPMSingle_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptPMSingle_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtPMSingle (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtPMSingle; iexists _, _; iframe
    ipersist unknownFields; ipersist Message;
    imodintro; unfold fieldsPMSingle; iframe #; ipureintro; exact Hnn
  · rw [ptPMSingle_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsPMSingle_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*ProposerMessage_ClientBatch_SingleMessage`. -/
theorem ptPMSingle_share (E : CoPset) (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptPMSingle l .discard v := by
  rw [← ptPMSingle_own]; exact ptPMSingle_persist E l _ v

theorem ptPMSingle_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) :
    ptPMSingle (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptPMSingle_own]; exact typedPointsto_not_null _ _ _
  · rw [ptPMSingle_shared l dq v h]
    unfold fieldsPMSingle
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptPMSingle_fields (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) :
    ptPMSingle (GF := GF) l .discard v ⊢ fieldsPMSingle l .discard v := by
  rw [ptPMSingle_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptPMSingle_access_load_unknownFields (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' dq) (ptPMSingle l dq v) (ptPMSingle l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPMSingle_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPMSingle_shared l dq v h]
      unfold fieldsPMSingle
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPMSingle_access_load_Message (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage go!"Message" l) v.Message' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage go!"Message" l) v.Message' dq) (ptPMSingle l dq v) (ptPMSingle l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPMSingle_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage go!"Message" l) v.Message' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPMSingle_shared l dq v h]
      unfold fieldsPMSingle
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Message
      iintro Message
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*ProposerMessage_ClientBatch` -/

/-- The fields of a `*ProposerMessage_ClientBatch` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsPMBatch (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"unknownFields" l) v.unknownFields' dq ∗
    "Sender" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Sender" l) v.Sender' dq ∗
    "Messages" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Messages" l) v.Messages' dq ∗
    "Id" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Id" l) v.Id' dq ∗
    "_" ∷ True)

theorem fieldsPMBatch_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch) :
    fieldsPMBatch (GF := GF) l dq v ⊢ |==> fieldsPMBatch l .discard v := by
  unfold fieldsPMBatch
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Sender; ipersist Messages; ipersist Id;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsPMBatch_pers (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch) :
    Persistent (fieldsPMBatch (GF := GF) l .discard v) := by
  unfold fieldsPMBatch; infer_instance

/-- Protobuf's runtime fields of a `*ProposerMessage_ClientBatch` at `l`, owned. -/
def rtPMBatch (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*ProposerMessage_ClientBatch` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptPMBatch (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsPMBatch l dq v ∗ inv pbRtN (rtPMBatch l))

theorem ptPMBatch_own (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch) :
    ptPMBatch (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptPMBatch; exact if_pos rfl

theorem ptPMBatch_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch) (h : dq ≠ DFrac.own 1) :
    ptPMBatch (GF := GF) l dq v = iprop(fieldsPMBatch l dq v ∗ inv pbRtN (rtPMBatch l)) := by
  unfold ptPMBatch; exact if_neg h

instance ptPMBatch_pers (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch) :
    Persistent (ptPMBatch (GF := GF) l .discard v) := by
  rw [ptPMBatch_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*ProposerMessage_ClientBatch`: an owned one gives its runtime fields to an invariant. -/
theorem ptPMBatch_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch) :
    ptPMBatch (GF := GF) l dq v ⊢ |={E}=> ptPMBatch l .discard v := by
  rw [ptPMBatch_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptPMBatch_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtPMBatch (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtPMBatch; iexists _, _; iframe
    ipersist unknownFields; ipersist Sender; ipersist Messages; ipersist Id;
    imodintro; unfold fieldsPMBatch; iframe #; ipureintro; exact Hnn
  · rw [ptPMBatch_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsPMBatch_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*ProposerMessage_ClientBatch`. -/
theorem ptPMBatch_share (E : CoPset) (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptPMBatch l .discard v := by
  rw [← ptPMBatch_own]; exact ptPMBatch_persist E l _ v

theorem ptPMBatch_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_ClientBatch) :
    ptPMBatch (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptPMBatch_own]; exact typedPointsto_not_null _ _ _
  · rw [ptPMBatch_shared l dq v h]
    unfold fieldsPMBatch
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptPMBatch_fields (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch) :
    ptPMBatch (GF := GF) l .discard v ⊢ fieldsPMBatch l .discard v := by
  rw [ptPMBatch_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptPMBatch_access_load_unknownFields (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"unknownFields" l) v.unknownFields' dq) (ptPMBatch l dq v) (ptPMBatch l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPMBatch_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPMBatch_shared l dq v h]
      unfold fieldsPMBatch
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPMBatch_access_load_Sender (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Sender" l) v.Sender' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Sender" l) v.Sender' dq) (ptPMBatch l dq v) (ptPMBatch l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPMBatch_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Sender" l) v.Sender' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPMBatch_shared l dq v h]
      unfold fieldsPMBatch
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Sender
      iintro Sender
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPMBatch_access_load_Messages (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Messages" l) v.Messages' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Messages" l) v.Messages' dq) (ptPMBatch l dq v) (ptPMBatch l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPMBatch_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Messages" l) v.Messages' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPMBatch_shared l dq v h]
      unfold fieldsPMBatch
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Messages
      iintro Messages
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPMBatch_access_load_Id (l : Loc) (v : raxos.replica.src.ProposerMessage_ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Id" l) v.Id' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Id" l) v.Id' dq) (ptPMBatch l dq v) (ptPMBatch l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPMBatch_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_ClientBatch go!"Id" l) v.Id' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPMBatch_shared l dq v h]
      unfold fieldsPMBatch
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Id
      iintro Id
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*ProposerMessage_DecidedSlot` -/

/-- The fields of a `*ProposerMessage_DecidedSlot` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsPMSlot (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_DecidedSlot) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"unknownFields" l) v.unknownFields' dq ∗
    "Index" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Index" l) v.Index' dq ∗
    "Ids" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Ids" l) v.Ids' dq ∗
    "Proposer" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Proposer" l) v.Proposer' dq ∗
    "_" ∷ True)

theorem fieldsPMSlot_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_DecidedSlot) :
    fieldsPMSlot (GF := GF) l dq v ⊢ |==> fieldsPMSlot l .discard v := by
  unfold fieldsPMSlot
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Index; ipersist Ids; ipersist Proposer;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsPMSlot_pers (l : Loc) (v : raxos.replica.src.ProposerMessage_DecidedSlot) :
    Persistent (fieldsPMSlot (GF := GF) l .discard v) := by
  unfold fieldsPMSlot; infer_instance

/-- Protobuf's runtime fields of a `*ProposerMessage_DecidedSlot` at `l`, owned. -/
def rtPMSlot (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*ProposerMessage_DecidedSlot` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptPMSlot (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_DecidedSlot) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsPMSlot l dq v ∗ inv pbRtN (rtPMSlot l))

theorem ptPMSlot_own (l : Loc) (v : raxos.replica.src.ProposerMessage_DecidedSlot) :
    ptPMSlot (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptPMSlot; exact if_pos rfl

theorem ptPMSlot_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_DecidedSlot) (h : dq ≠ DFrac.own 1) :
    ptPMSlot (GF := GF) l dq v = iprop(fieldsPMSlot l dq v ∗ inv pbRtN (rtPMSlot l)) := by
  unfold ptPMSlot; exact if_neg h

instance ptPMSlot_pers (l : Loc) (v : raxos.replica.src.ProposerMessage_DecidedSlot) :
    Persistent (ptPMSlot (GF := GF) l .discard v) := by
  rw [ptPMSlot_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*ProposerMessage_DecidedSlot`: an owned one gives its runtime fields to an invariant. -/
theorem ptPMSlot_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_DecidedSlot) :
    ptPMSlot (GF := GF) l dq v ⊢ |={E}=> ptPMSlot l .discard v := by
  rw [ptPMSlot_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptPMSlot_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtPMSlot (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtPMSlot; iexists _, _; iframe
    ipersist unknownFields; ipersist Index; ipersist Ids; ipersist Proposer;
    imodintro; unfold fieldsPMSlot; iframe #; ipureintro; exact Hnn
  · rw [ptPMSlot_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsPMSlot_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*ProposerMessage_DecidedSlot`. -/
theorem ptPMSlot_share (E : CoPset) (l : Loc) (v : raxos.replica.src.ProposerMessage_DecidedSlot) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptPMSlot l .discard v := by
  rw [← ptPMSlot_own]; exact ptPMSlot_persist E l _ v

theorem ptPMSlot_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_DecidedSlot) :
    ptPMSlot (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptPMSlot_own]; exact typedPointsto_not_null _ _ _
  · rw [ptPMSlot_shared l dq v h]
    unfold fieldsPMSlot
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptPMSlot_fields (l : Loc) (v : raxos.replica.src.ProposerMessage_DecidedSlot) :
    ptPMSlot (GF := GF) l .discard v ⊢ fieldsPMSlot l .discard v := by
  rw [ptPMSlot_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptPMSlot_access_load_unknownFields (l : Loc) (v : raxos.replica.src.ProposerMessage_DecidedSlot) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"unknownFields" l) v.unknownFields' dq) (ptPMSlot l dq v) (ptPMSlot l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPMSlot_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPMSlot_shared l dq v h]
      unfold fieldsPMSlot
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPMSlot_access_load_Index (l : Loc) (v : raxos.replica.src.ProposerMessage_DecidedSlot) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Index" l) v.Index' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Index" l) v.Index' dq) (ptPMSlot l dq v) (ptPMSlot l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPMSlot_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Index" l) v.Index' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPMSlot_shared l dq v h]
      unfold fieldsPMSlot
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Index
      iintro Index
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPMSlot_access_load_Ids (l : Loc) (v : raxos.replica.src.ProposerMessage_DecidedSlot) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Ids" l) v.Ids' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Ids" l) v.Ids' dq) (ptPMSlot l dq v) (ptPMSlot l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPMSlot_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Ids" l) v.Ids' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPMSlot_shared l dq v h]
      unfold fieldsPMSlot
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Ids
      iintro Ids
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPMSlot_access_load_Proposer (l : Loc) (v : raxos.replica.src.ProposerMessage_DecidedSlot) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Proposer" l) v.Proposer' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Proposer" l) v.Proposer' dq) (ptPMSlot l dq v) (ptPMSlot l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPMSlot_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_DecidedSlot go!"Proposer" l) v.Proposer' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPMSlot_shared l dq v h]
      unfold fieldsPMSlot
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Proposer
      iintro Proposer
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*ProposerMessage_Proposal` -/

/-- The fields of a `*ProposerMessage_Proposal` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsProp (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_Proposal) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"unknownFields" l) v.unknownFields' dq ∗
    "Priority" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"Priority" l) v.Priority' dq ∗
    "ProposerId" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ProposerId" l) v.ProposerId' dq ∗
    "ThreadId" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ThreadId" l) v.ThreadId' dq ∗
    "Ids" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"Ids" l) v.Ids' dq ∗
    "ClientBatches" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ClientBatches" l) v.ClientBatches' dq ∗
    "_" ∷ True)

theorem fieldsProp_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_Proposal) :
    fieldsProp (GF := GF) l dq v ⊢ |==> fieldsProp l .discard v := by
  unfold fieldsProp
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Priority; ipersist ProposerId; ipersist ThreadId; ipersist Ids; ipersist ClientBatches;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsProp_pers (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) :
    Persistent (fieldsProp (GF := GF) l .discard v) := by
  unfold fieldsProp; infer_instance

/-- Protobuf's runtime fields of a `*ProposerMessage_Proposal` at `l`, owned. -/
def rtProp (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*ProposerMessage_Proposal` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptProp (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_Proposal) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsProp l dq v ∗ inv pbRtN (rtProp l))

theorem ptProp_own (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) :
    ptProp (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptProp; exact if_pos rfl

theorem ptProp_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_Proposal) (h : dq ≠ DFrac.own 1) :
    ptProp (GF := GF) l dq v = iprop(fieldsProp l dq v ∗ inv pbRtN (rtProp l)) := by
  unfold ptProp; exact if_neg h

instance ptProp_pers (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) :
    Persistent (ptProp (GF := GF) l .discard v) := by
  rw [ptProp_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*ProposerMessage_Proposal`: an owned one gives its runtime fields to an invariant. -/
theorem ptProp_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_Proposal) :
    ptProp (GF := GF) l dq v ⊢ |={E}=> ptProp l .discard v := by
  rw [ptProp_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptProp_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtProp (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtProp; iexists _, _; iframe
    ipersist unknownFields; ipersist Priority; ipersist ProposerId; ipersist ThreadId; ipersist Ids; ipersist ClientBatches;
    imodintro; unfold fieldsProp; iframe #; ipureintro; exact Hnn
  · rw [ptProp_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsProp_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*ProposerMessage_Proposal`. -/
theorem ptProp_share (E : CoPset) (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptProp l .discard v := by
  rw [← ptProp_own]; exact ptProp_persist E l _ v

theorem ptProp_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage_Proposal) :
    ptProp (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptProp_own]; exact typedPointsto_not_null _ _ _
  · rw [ptProp_shared l dq v h]
    unfold fieldsProp
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptProp_fields (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) :
    ptProp (GF := GF) l .discard v ⊢ fieldsProp l .discard v := by
  rw [ptProp_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptProp_access_load_unknownFields (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"unknownFields" l) v.unknownFields' dq) (ptProp l dq v) (ptProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptProp_shared l dq v h]
      unfold fieldsProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptProp_access_load_Priority (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"Priority" l) v.Priority' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"Priority" l) v.Priority' dq) (ptProp l dq v) (ptProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"Priority" l) v.Priority' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptProp_shared l dq v h]
      unfold fieldsProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Priority
      iintro Priority
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptProp_access_load_ProposerId (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ProposerId" l) v.ProposerId' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ProposerId" l) v.ProposerId' dq) (ptProp l dq v) (ptProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ProposerId" l) v.ProposerId' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptProp_shared l dq v h]
      unfold fieldsProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe ProposerId
      iintro ProposerId
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptProp_access_load_ThreadId (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ThreadId" l) v.ThreadId' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ThreadId" l) v.ThreadId' dq) (ptProp l dq v) (ptProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ThreadId" l) v.ThreadId' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptProp_shared l dq v h]
      unfold fieldsProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe ThreadId
      iintro ThreadId
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptProp_access_load_Ids (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"Ids" l) v.Ids' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"Ids" l) v.Ids' dq) (ptProp l dq v) (ptProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"Ids" l) v.Ids' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptProp_shared l dq v h]
      unfold fieldsProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Ids
      iintro Ids
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptProp_access_load_ClientBatches (l : Loc) (v : raxos.replica.src.ProposerMessage_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ClientBatches" l) v.ClientBatches' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ClientBatches" l) v.ClientBatches' dq) (ptProp l dq v) (ptProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage_Proposal go!"ClientBatches" l) v.ClientBatches' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptProp_shared l dq v h]
      unfold fieldsProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe ClientBatches
      iintro ClientBatches
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*ProposerMessage` -/

/-- The fields of a `*ProposerMessage` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsPM (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"unknownFields" l) v.unknownFields' dq ∗
    "Sender" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"Sender" l) v.Sender' dq ∗
    "Index" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"Index" l) v.Index' dq ∗
    "P" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"P" l) v.P' dq ∗
    "S" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"S" l) v.S' dq ∗
    "DecidedSlots" ∷ typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"DecidedSlots" l) v.DecidedSlots' dq ∗
    "_" ∷ True)

theorem fieldsPM_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage) :
    fieldsPM (GF := GF) l dq v ⊢ |==> fieldsPM l .discard v := by
  unfold fieldsPM
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Sender; ipersist Index; ipersist P; ipersist S; ipersist DecidedSlots;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsPM_pers (l : Loc) (v : raxos.replica.src.ProposerMessage) :
    Persistent (fieldsPM (GF := GF) l .discard v) := by
  unfold fieldsPM; infer_instance

/-- Protobuf's runtime fields of a `*ProposerMessage` at `l`, owned. -/
def rtPM (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*ProposerMessage` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptPM (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsPM l dq v ∗ inv pbRtN (rtPM l))

theorem ptPM_own (l : Loc) (v : raxos.replica.src.ProposerMessage) :
    ptPM (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptPM; exact if_pos rfl

theorem ptPM_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage) (h : dq ≠ DFrac.own 1) :
    ptPM (GF := GF) l dq v = iprop(fieldsPM l dq v ∗ inv pbRtN (rtPM l)) := by
  unfold ptPM; exact if_neg h

instance ptPM_pers (l : Loc) (v : raxos.replica.src.ProposerMessage) :
    Persistent (ptPM (GF := GF) l .discard v) := by
  rw [ptPM_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*ProposerMessage`: an owned one gives its runtime fields to an invariant. -/
theorem ptPM_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage) :
    ptPM (GF := GF) l dq v ⊢ |={E}=> ptPM l .discard v := by
  rw [ptPM_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptPM_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtPM (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtPM; iexists _, _; iframe
    ipersist unknownFields; ipersist Sender; ipersist Index; ipersist P; ipersist S; ipersist DecidedSlots;
    imodintro; unfold fieldsPM; iframe #; ipureintro; exact Hnn
  · rw [ptPM_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsPM_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*ProposerMessage`. -/
theorem ptPM_share (E : CoPset) (l : Loc) (v : raxos.replica.src.ProposerMessage) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptPM l .discard v := by
  rw [← ptPM_own]; exact ptPM_persist E l _ v

theorem ptPM_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.ProposerMessage) :
    ptPM (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptPM_own]; exact typedPointsto_not_null _ _ _
  · rw [ptPM_shared l dq v h]
    unfold fieldsPM
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptPM_fields (l : Loc) (v : raxos.replica.src.ProposerMessage) :
    ptPM (GF := GF) l .discard v ⊢ fieldsPM l .discard v := by
  rw [ptPM_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptPM_access_load_unknownFields (l : Loc) (v : raxos.replica.src.ProposerMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"unknownFields" l) v.unknownFields' dq) (ptPM l dq v) (ptPM l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPM_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPM_shared l dq v h]
      unfold fieldsPM
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPM_access_load_Sender (l : Loc) (v : raxos.replica.src.ProposerMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"Sender" l) v.Sender' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"Sender" l) v.Sender' dq) (ptPM l dq v) (ptPM l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPM_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"Sender" l) v.Sender' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPM_shared l dq v h]
      unfold fieldsPM
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Sender
      iintro Sender
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPM_access_load_Index (l : Loc) (v : raxos.replica.src.ProposerMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"Index" l) v.Index' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"Index" l) v.Index' dq) (ptPM l dq v) (ptPM l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPM_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"Index" l) v.Index' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPM_shared l dq v h]
      unfold fieldsPM
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Index
      iintro Index
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPM_access_load_P (l : Loc) (v : raxos.replica.src.ProposerMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"P" l) v.P' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"P" l) v.P' dq) (ptPM l dq v) (ptPM l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPM_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"P" l) v.P' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPM_shared l dq v h]
      unfold fieldsPM
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe P
      iintro P
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPM_access_load_S (l : Loc) (v : raxos.replica.src.ProposerMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"S" l) v.S' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"S" l) v.S' dq) (ptPM l dq v) (ptPM l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPM_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"S" l) v.S' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPM_shared l dq v h]
      unfold fieldsPM
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe S
      iintro S
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptPM_access_load_DecidedSlots (l : Loc) (v : raxos.replica.src.ProposerMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"DecidedSlots" l) v.DecidedSlots' dq) (typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"DecidedSlots" l) v.DecidedSlots' dq) (ptPM l dq v) (ptPM l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptPM_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.ProposerMessage go!"DecidedSlots" l) v.DecidedSlots' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptPM_shared l dq v h]
      unfold fieldsPM
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe DecidedSlots
      iintro DecidedSlots
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*RecorderResponse_Proposal` -/

/-- The fields of a `*RecorderResponse_Proposal` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsRRProp (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse_Proposal) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"unknownFields" l) v.unknownFields' dq ∗
    "Priority" ∷ typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"Priority" l) v.Priority' dq ∗
    "ProposerId" ∷ typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"ProposerId" l) v.ProposerId' dq ∗
    "ThreadId" ∷ typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"ThreadId" l) v.ThreadId' dq ∗
    "Ids" ∷ typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"Ids" l) v.Ids' dq ∗
    "_" ∷ True)

theorem fieldsRRProp_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse_Proposal) :
    fieldsRRProp (GF := GF) l dq v ⊢ |==> fieldsRRProp l .discard v := by
  unfold fieldsRRProp
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Priority; ipersist ProposerId; ipersist ThreadId; ipersist Ids;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsRRProp_pers (l : Loc) (v : raxos.replica.src.RecorderResponse_Proposal) :
    Persistent (fieldsRRProp (GF := GF) l .discard v) := by
  unfold fieldsRRProp; infer_instance

/-- Protobuf's runtime fields of a `*RecorderResponse_Proposal` at `l`, owned. -/
def rtRRProp (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*RecorderResponse_Proposal` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptRRProp (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse_Proposal) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsRRProp l dq v ∗ inv pbRtN (rtRRProp l))

theorem ptRRProp_own (l : Loc) (v : raxos.replica.src.RecorderResponse_Proposal) :
    ptRRProp (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptRRProp; exact if_pos rfl

theorem ptRRProp_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse_Proposal) (h : dq ≠ DFrac.own 1) :
    ptRRProp (GF := GF) l dq v = iprop(fieldsRRProp l dq v ∗ inv pbRtN (rtRRProp l)) := by
  unfold ptRRProp; exact if_neg h

instance ptRRProp_pers (l : Loc) (v : raxos.replica.src.RecorderResponse_Proposal) :
    Persistent (ptRRProp (GF := GF) l .discard v) := by
  rw [ptRRProp_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*RecorderResponse_Proposal`: an owned one gives its runtime fields to an invariant. -/
theorem ptRRProp_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse_Proposal) :
    ptRRProp (GF := GF) l dq v ⊢ |={E}=> ptRRProp l .discard v := by
  rw [ptRRProp_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptRRProp_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtRRProp (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtRRProp; iexists _, _; iframe
    ipersist unknownFields; ipersist Priority; ipersist ProposerId; ipersist ThreadId; ipersist Ids;
    imodintro; unfold fieldsRRProp; iframe #; ipureintro; exact Hnn
  · rw [ptRRProp_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsRRProp_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*RecorderResponse_Proposal`. -/
theorem ptRRProp_share (E : CoPset) (l : Loc) (v : raxos.replica.src.RecorderResponse_Proposal) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptRRProp l .discard v := by
  rw [← ptRRProp_own]; exact ptRRProp_persist E l _ v

theorem ptRRProp_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse_Proposal) :
    ptRRProp (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptRRProp_own]; exact typedPointsto_not_null _ _ _
  · rw [ptRRProp_shared l dq v h]
    unfold fieldsRRProp
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptRRProp_fields (l : Loc) (v : raxos.replica.src.RecorderResponse_Proposal) :
    ptRRProp (GF := GF) l .discard v ⊢ fieldsRRProp l .discard v := by
  rw [ptRRProp_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptRRProp_access_load_unknownFields (l : Loc) (v : raxos.replica.src.RecorderResponse_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"unknownFields" l) v.unknownFields' dq) (ptRRProp l dq v) (ptRRProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptRRProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptRRProp_shared l dq v h]
      unfold fieldsRRProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptRRProp_access_load_Priority (l : Loc) (v : raxos.replica.src.RecorderResponse_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"Priority" l) v.Priority' dq) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"Priority" l) v.Priority' dq) (ptRRProp l dq v) (ptRRProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptRRProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"Priority" l) v.Priority' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptRRProp_shared l dq v h]
      unfold fieldsRRProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Priority
      iintro Priority
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptRRProp_access_load_ProposerId (l : Loc) (v : raxos.replica.src.RecorderResponse_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"ProposerId" l) v.ProposerId' dq) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"ProposerId" l) v.ProposerId' dq) (ptRRProp l dq v) (ptRRProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptRRProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"ProposerId" l) v.ProposerId' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptRRProp_shared l dq v h]
      unfold fieldsRRProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe ProposerId
      iintro ProposerId
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptRRProp_access_load_ThreadId (l : Loc) (v : raxos.replica.src.RecorderResponse_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"ThreadId" l) v.ThreadId' dq) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"ThreadId" l) v.ThreadId' dq) (ptRRProp l dq v) (ptRRProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptRRProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"ThreadId" l) v.ThreadId' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptRRProp_shared l dq v h]
      unfold fieldsRRProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe ThreadId
      iintro ThreadId
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptRRProp_access_load_Ids (l : Loc) (v : raxos.replica.src.RecorderResponse_Proposal) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"Ids" l) v.Ids' dq) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"Ids" l) v.Ids' dq) (ptRRProp l dq v) (ptRRProp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptRRProp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.RecorderResponse_Proposal go!"Ids" l) v.Ids' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptRRProp_shared l dq v h]
      unfold fieldsRRProp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Ids
      iintro Ids
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*RecorderResponse` -/

/-- The fields of a `*RecorderResponse` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsRR (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"unknownFields" l) v.unknownFields' dq ∗
    "S" ∷ typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"S" l) v.S' dq ∗
    "F" ∷ typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"F" l) v.F' dq ∗
    "M" ∷ typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"M" l) v.M' dq ∗
    "ClientBatchesNotFound" ∷ typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"ClientBatchesNotFound" l) v.ClientBatchesNotFound' dq ∗
    "_" ∷ True)

theorem fieldsRR_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse) :
    fieldsRR (GF := GF) l dq v ⊢ |==> fieldsRR l .discard v := by
  unfold fieldsRR
  iintro H
  iNamed H
  ipersist unknownFields; ipersist S; ipersist F; ipersist M; ipersist ClientBatchesNotFound;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsRR_pers (l : Loc) (v : raxos.replica.src.RecorderResponse) :
    Persistent (fieldsRR (GF := GF) l .discard v) := by
  unfold fieldsRR; infer_instance

/-- Protobuf's runtime fields of a `*RecorderResponse` at `l`, owned. -/
def rtRR (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*RecorderResponse` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptRR (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsRR l dq v ∗ inv pbRtN (rtRR l))

theorem ptRR_own (l : Loc) (v : raxos.replica.src.RecorderResponse) :
    ptRR (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptRR; exact if_pos rfl

theorem ptRR_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse) (h : dq ≠ DFrac.own 1) :
    ptRR (GF := GF) l dq v = iprop(fieldsRR l dq v ∗ inv pbRtN (rtRR l)) := by
  unfold ptRR; exact if_neg h

instance ptRR_pers (l : Loc) (v : raxos.replica.src.RecorderResponse) :
    Persistent (ptRR (GF := GF) l .discard v) := by
  rw [ptRR_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*RecorderResponse`: an owned one gives its runtime fields to an invariant. -/
theorem ptRR_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse) :
    ptRR (GF := GF) l dq v ⊢ |={E}=> ptRR l .discard v := by
  rw [ptRR_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptRR_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtRR (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtRR; iexists _, _; iframe
    ipersist unknownFields; ipersist S; ipersist F; ipersist M; ipersist ClientBatchesNotFound;
    imodintro; unfold fieldsRR; iframe #; ipureintro; exact Hnn
  · rw [ptRR_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsRR_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*RecorderResponse`. -/
theorem ptRR_share (E : CoPset) (l : Loc) (v : raxos.replica.src.RecorderResponse) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptRR l .discard v := by
  rw [← ptRR_own]; exact ptRR_persist E l _ v

theorem ptRR_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.RecorderResponse) :
    ptRR (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptRR_own]; exact typedPointsto_not_null _ _ _
  · rw [ptRR_shared l dq v h]
    unfold fieldsRR
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptRR_fields (l : Loc) (v : raxos.replica.src.RecorderResponse) :
    ptRR (GF := GF) l .discard v ⊢ fieldsRR l .discard v := by
  rw [ptRR_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptRR_access_load_unknownFields (l : Loc) (v : raxos.replica.src.RecorderResponse) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"unknownFields" l) v.unknownFields' dq) (ptRR l dq v) (ptRR l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptRR_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptRR_shared l dq v h]
      unfold fieldsRR
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptRR_access_load_S (l : Loc) (v : raxos.replica.src.RecorderResponse) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"S" l) v.S' dq) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"S" l) v.S' dq) (ptRR l dq v) (ptRR l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptRR_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"S" l) v.S' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptRR_shared l dq v h]
      unfold fieldsRR
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe S
      iintro S
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptRR_access_load_F (l : Loc) (v : raxos.replica.src.RecorderResponse) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"F" l) v.F' dq) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"F" l) v.F' dq) (ptRR l dq v) (ptRR l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptRR_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"F" l) v.F' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptRR_shared l dq v h]
      unfold fieldsRR
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe F
      iintro F
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptRR_access_load_M (l : Loc) (v : raxos.replica.src.RecorderResponse) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"M" l) v.M' dq) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"M" l) v.M' dq) (ptRR l dq v) (ptRR l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptRR_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"M" l) v.M' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptRR_shared l dq v h]
      unfold fieldsRR
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe M
      iintro M
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptRR_access_load_ClientBatchesNotFound (l : Loc) (v : raxos.replica.src.RecorderResponse) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"ClientBatchesNotFound" l) v.ClientBatchesNotFound' dq) (typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"ClientBatchesNotFound" l) v.ClientBatchesNotFound' dq) (ptRR l dq v) (ptRR l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptRR_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.RecorderResponse go!"ClientBatchesNotFound" l) v.ClientBatchesNotFound' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptRR_shared l dq v h]
      unfold fieldsRR
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe ClientBatchesNotFound
      iintro ClientBatchesNotFound
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*DecideRequest` -/

/-- The fields of a `*DecideRequest` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsDReq (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideRequest) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.DecideRequest go!"unknownFields" l) v.unknownFields' dq ∗
    "Ids" ∷ typedPointsto (structFieldRef raxos.replica.src.DecideRequest go!"Ids" l) v.Ids' dq ∗
    "_" ∷ True)

theorem fieldsDReq_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideRequest) :
    fieldsDReq (GF := GF) l dq v ⊢ |==> fieldsDReq l .discard v := by
  unfold fieldsDReq
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Ids;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsDReq_pers (l : Loc) (v : raxos.replica.src.DecideRequest) :
    Persistent (fieldsDReq (GF := GF) l .discard v) := by
  unfold fieldsDReq; infer_instance

/-- Protobuf's runtime fields of a `*DecideRequest` at `l`, owned. -/
def rtDReq (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.DecideRequest go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.DecideRequest go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*DecideRequest` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptDReq (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideRequest) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsDReq l dq v ∗ inv pbRtN (rtDReq l))

theorem ptDReq_own (l : Loc) (v : raxos.replica.src.DecideRequest) :
    ptDReq (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptDReq; exact if_pos rfl

theorem ptDReq_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideRequest) (h : dq ≠ DFrac.own 1) :
    ptDReq (GF := GF) l dq v = iprop(fieldsDReq l dq v ∗ inv pbRtN (rtDReq l)) := by
  unfold ptDReq; exact if_neg h

instance ptDReq_pers (l : Loc) (v : raxos.replica.src.DecideRequest) :
    Persistent (ptDReq (GF := GF) l .discard v) := by
  rw [ptDReq_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*DecideRequest`: an owned one gives its runtime fields to an invariant. -/
theorem ptDReq_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideRequest) :
    ptDReq (GF := GF) l dq v ⊢ |={E}=> ptDReq l .discard v := by
  rw [ptDReq_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptDReq_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtDReq (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtDReq; iexists _, _; iframe
    ipersist unknownFields; ipersist Ids;
    imodintro; unfold fieldsDReq; iframe #; ipureintro; exact Hnn
  · rw [ptDReq_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsDReq_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*DecideRequest`. -/
theorem ptDReq_share (E : CoPset) (l : Loc) (v : raxos.replica.src.DecideRequest) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptDReq l .discard v := by
  rw [← ptDReq_own]; exact ptDReq_persist E l _ v

theorem ptDReq_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideRequest) :
    ptDReq (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptDReq_own]; exact typedPointsto_not_null _ _ _
  · rw [ptDReq_shared l dq v h]
    unfold fieldsDReq
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptDReq_fields (l : Loc) (v : raxos.replica.src.DecideRequest) :
    ptDReq (GF := GF) l .discard v ⊢ fieldsDReq l .discard v := by
  rw [ptDReq_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptDReq_access_load_unknownFields (l : Loc) (v : raxos.replica.src.DecideRequest) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.DecideRequest go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.DecideRequest go!"unknownFields" l) v.unknownFields' dq) (ptDReq l dq v) (ptDReq l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDReq_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.DecideRequest go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDReq_shared l dq v h]
      unfold fieldsDReq
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptDReq_access_load_Ids (l : Loc) (v : raxos.replica.src.DecideRequest) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.DecideRequest go!"Ids" l) v.Ids' dq) (typedPointsto (structFieldRef raxos.replica.src.DecideRequest go!"Ids" l) v.Ids' dq) (ptDReq l dq v) (ptDReq l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDReq_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.DecideRequest go!"Ids" l) v.Ids' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDReq_shared l dq v h]
      unfold fieldsDReq
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Ids
      iintro Ids
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*DecideResponse_ClientBatch_SingleMessage` -/

/-- The fields of a `*DecideResponse_ClientBatch_SingleMessage` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsDRSingle (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' dq ∗
    "Message" ∷ typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch_SingleMessage go!"Message" l) v.Message' dq ∗
    "_" ∷ True)

theorem fieldsDRSingle_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) :
    fieldsDRSingle (GF := GF) l dq v ⊢ |==> fieldsDRSingle l .discard v := by
  unfold fieldsDRSingle
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Message;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsDRSingle_pers (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) :
    Persistent (fieldsDRSingle (GF := GF) l .discard v) := by
  unfold fieldsDRSingle; infer_instance

/-- Protobuf's runtime fields of a `*DecideResponse_ClientBatch_SingleMessage` at `l`, owned. -/
def rtDRSingle (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch_SingleMessage go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch_SingleMessage go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*DecideResponse_ClientBatch_SingleMessage` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptDRSingle (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsDRSingle l dq v ∗ inv pbRtN (rtDRSingle l))

theorem ptDRSingle_own (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) :
    ptDRSingle (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptDRSingle; exact if_pos rfl

theorem ptDRSingle_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) (h : dq ≠ DFrac.own 1) :
    ptDRSingle (GF := GF) l dq v = iprop(fieldsDRSingle l dq v ∗ inv pbRtN (rtDRSingle l)) := by
  unfold ptDRSingle; exact if_neg h

instance ptDRSingle_pers (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) :
    Persistent (ptDRSingle (GF := GF) l .discard v) := by
  rw [ptDRSingle_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*DecideResponse_ClientBatch_SingleMessage`: an owned one gives its runtime fields to an invariant. -/
theorem ptDRSingle_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) :
    ptDRSingle (GF := GF) l dq v ⊢ |={E}=> ptDRSingle l .discard v := by
  rw [ptDRSingle_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptDRSingle_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtDRSingle (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtDRSingle; iexists _, _; iframe
    ipersist unknownFields; ipersist Message;
    imodintro; unfold fieldsDRSingle; iframe #; ipureintro; exact Hnn
  · rw [ptDRSingle_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsDRSingle_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*DecideResponse_ClientBatch_SingleMessage`. -/
theorem ptDRSingle_share (E : CoPset) (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptDRSingle l .discard v := by
  rw [← ptDRSingle_own]; exact ptDRSingle_persist E l _ v

theorem ptDRSingle_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) :
    ptDRSingle (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptDRSingle_own]; exact typedPointsto_not_null _ _ _
  · rw [ptDRSingle_shared l dq v h]
    unfold fieldsDRSingle
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptDRSingle_fields (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) :
    ptDRSingle (GF := GF) l .discard v ⊢ fieldsDRSingle l .discard v := by
  rw [ptDRSingle_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptDRSingle_access_load_unknownFields (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' dq) (ptDRSingle l dq v) (ptDRSingle l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDRSingle_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDRSingle_shared l dq v h]
      unfold fieldsDRSingle
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptDRSingle_access_load_Message (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch_SingleMessage go!"Message" l) v.Message' dq) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch_SingleMessage go!"Message" l) v.Message' dq) (ptDRSingle l dq v) (ptDRSingle l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDRSingle_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch_SingleMessage go!"Message" l) v.Message' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDRSingle_shared l dq v h]
      unfold fieldsDRSingle
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Message
      iintro Message
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*DecideResponse_ClientBatch` -/

/-- The fields of a `*DecideResponse_ClientBatch` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsDRBatch (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"unknownFields" l) v.unknownFields' dq ∗
    "Sender" ∷ typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Sender" l) v.Sender' dq ∗
    "Messages" ∷ typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Messages" l) v.Messages' dq ∗
    "Id" ∷ typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Id" l) v.Id' dq ∗
    "_" ∷ True)

theorem fieldsDRBatch_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch) :
    fieldsDRBatch (GF := GF) l dq v ⊢ |==> fieldsDRBatch l .discard v := by
  unfold fieldsDRBatch
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Sender; ipersist Messages; ipersist Id;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsDRBatch_pers (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch) :
    Persistent (fieldsDRBatch (GF := GF) l .discard v) := by
  unfold fieldsDRBatch; infer_instance

/-- Protobuf's runtime fields of a `*DecideResponse_ClientBatch` at `l`, owned. -/
def rtDRBatch (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*DecideResponse_ClientBatch` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptDRBatch (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsDRBatch l dq v ∗ inv pbRtN (rtDRBatch l))

theorem ptDRBatch_own (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch) :
    ptDRBatch (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptDRBatch; exact if_pos rfl

theorem ptDRBatch_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch) (h : dq ≠ DFrac.own 1) :
    ptDRBatch (GF := GF) l dq v = iprop(fieldsDRBatch l dq v ∗ inv pbRtN (rtDRBatch l)) := by
  unfold ptDRBatch; exact if_neg h

instance ptDRBatch_pers (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch) :
    Persistent (ptDRBatch (GF := GF) l .discard v) := by
  rw [ptDRBatch_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*DecideResponse_ClientBatch`: an owned one gives its runtime fields to an invariant. -/
theorem ptDRBatch_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch) :
    ptDRBatch (GF := GF) l dq v ⊢ |={E}=> ptDRBatch l .discard v := by
  rw [ptDRBatch_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptDRBatch_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtDRBatch (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtDRBatch; iexists _, _; iframe
    ipersist unknownFields; ipersist Sender; ipersist Messages; ipersist Id;
    imodintro; unfold fieldsDRBatch; iframe #; ipureintro; exact Hnn
  · rw [ptDRBatch_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsDRBatch_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*DecideResponse_ClientBatch`. -/
theorem ptDRBatch_share (E : CoPset) (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptDRBatch l .discard v := by
  rw [← ptDRBatch_own]; exact ptDRBatch_persist E l _ v

theorem ptDRBatch_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse_ClientBatch) :
    ptDRBatch (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptDRBatch_own]; exact typedPointsto_not_null _ _ _
  · rw [ptDRBatch_shared l dq v h]
    unfold fieldsDRBatch
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptDRBatch_fields (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch) :
    ptDRBatch (GF := GF) l .discard v ⊢ fieldsDRBatch l .discard v := by
  rw [ptDRBatch_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptDRBatch_access_load_unknownFields (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"unknownFields" l) v.unknownFields' dq) (ptDRBatch l dq v) (ptDRBatch l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDRBatch_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDRBatch_shared l dq v h]
      unfold fieldsDRBatch
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptDRBatch_access_load_Sender (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Sender" l) v.Sender' dq) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Sender" l) v.Sender' dq) (ptDRBatch l dq v) (ptDRBatch l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDRBatch_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Sender" l) v.Sender' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDRBatch_shared l dq v h]
      unfold fieldsDRBatch
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Sender
      iintro Sender
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptDRBatch_access_load_Messages (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Messages" l) v.Messages' dq) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Messages" l) v.Messages' dq) (ptDRBatch l dq v) (ptDRBatch l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDRBatch_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Messages" l) v.Messages' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDRBatch_shared l dq v h]
      unfold fieldsDRBatch
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Messages
      iintro Messages
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptDRBatch_access_load_Id (l : Loc) (v : raxos.replica.src.DecideResponse_ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Id" l) v.Id' dq) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Id" l) v.Id' dq) (ptDRBatch l dq v) (ptDRBatch l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDRBatch_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.DecideResponse_ClientBatch go!"Id" l) v.Id' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDRBatch_shared l dq v h]
      unfold fieldsDRBatch
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Id
      iintro Id
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*DecideResponse` -/

/-- The fields of a `*DecideResponse` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsDResp (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.DecideResponse go!"unknownFields" l) v.unknownFields' dq ∗
    "ClientBatches" ∷ typedPointsto (structFieldRef raxos.replica.src.DecideResponse go!"ClientBatches" l) v.ClientBatches' dq ∗
    "_" ∷ True)

theorem fieldsDResp_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse) :
    fieldsDResp (GF := GF) l dq v ⊢ |==> fieldsDResp l .discard v := by
  unfold fieldsDResp
  iintro H
  iNamed H
  ipersist unknownFields; ipersist ClientBatches;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsDResp_pers (l : Loc) (v : raxos.replica.src.DecideResponse) :
    Persistent (fieldsDResp (GF := GF) l .discard v) := by
  unfold fieldsDResp; infer_instance

/-- Protobuf's runtime fields of a `*DecideResponse` at `l`, owned. -/
def rtDResp (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.DecideResponse go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.DecideResponse go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*DecideResponse` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptDResp (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsDResp l dq v ∗ inv pbRtN (rtDResp l))

theorem ptDResp_own (l : Loc) (v : raxos.replica.src.DecideResponse) :
    ptDResp (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptDResp; exact if_pos rfl

theorem ptDResp_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse) (h : dq ≠ DFrac.own 1) :
    ptDResp (GF := GF) l dq v = iprop(fieldsDResp l dq v ∗ inv pbRtN (rtDResp l)) := by
  unfold ptDResp; exact if_neg h

instance ptDResp_pers (l : Loc) (v : raxos.replica.src.DecideResponse) :
    Persistent (ptDResp (GF := GF) l .discard v) := by
  rw [ptDResp_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*DecideResponse`: an owned one gives its runtime fields to an invariant. -/
theorem ptDResp_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse) :
    ptDResp (GF := GF) l dq v ⊢ |={E}=> ptDResp l .discard v := by
  rw [ptDResp_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptDResp_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtDResp (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtDResp; iexists _, _; iframe
    ipersist unknownFields; ipersist ClientBatches;
    imodintro; unfold fieldsDResp; iframe #; ipureintro; exact Hnn
  · rw [ptDResp_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsDResp_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*DecideResponse`. -/
theorem ptDResp_share (E : CoPset) (l : Loc) (v : raxos.replica.src.DecideResponse) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptDResp l .discard v := by
  rw [← ptDResp_own]; exact ptDResp_persist E l _ v

theorem ptDResp_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.DecideResponse) :
    ptDResp (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptDResp_own]; exact typedPointsto_not_null _ _ _
  · rw [ptDResp_shared l dq v h]
    unfold fieldsDResp
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptDResp_fields (l : Loc) (v : raxos.replica.src.DecideResponse) :
    ptDResp (GF := GF) l .discard v ⊢ fieldsDResp l .discard v := by
  rw [ptDResp_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptDResp_access_load_unknownFields (l : Loc) (v : raxos.replica.src.DecideResponse) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse go!"unknownFields" l) v.unknownFields' dq) (ptDResp l dq v) (ptDResp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDResp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.DecideResponse go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDResp_shared l dq v h]
      unfold fieldsDResp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptDResp_access_load_ClientBatches (l : Loc) (v : raxos.replica.src.DecideResponse) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse go!"ClientBatches" l) v.ClientBatches' dq) (typedPointsto (structFieldRef raxos.replica.src.DecideResponse go!"ClientBatches" l) v.ClientBatches' dq) (ptDResp l dq v) (ptDResp l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDResp_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.DecideResponse go!"ClientBatches" l) v.ClientBatches' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDResp_shared l dq v h]
      unfold fieldsDResp
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe ClientBatches
      iintro ClientBatches
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*Decisions_DecidedSlot` -/

/-- The fields of a `*Decisions_DecidedSlot` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsDecSlot (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions_DecidedSlot) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"unknownFields" l) v.unknownFields' dq ∗
    "Index" ∷ typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Index" l) v.Index' dq ∗
    "Ids" ∷ typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Ids" l) v.Ids' dq ∗
    "Proposer" ∷ typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Proposer" l) v.Proposer' dq ∗
    "_" ∷ True)

theorem fieldsDecSlot_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions_DecidedSlot) :
    fieldsDecSlot (GF := GF) l dq v ⊢ |==> fieldsDecSlot l .discard v := by
  unfold fieldsDecSlot
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Index; ipersist Ids; ipersist Proposer;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsDecSlot_pers (l : Loc) (v : raxos.replica.src.Decisions_DecidedSlot) :
    Persistent (fieldsDecSlot (GF := GF) l .discard v) := by
  unfold fieldsDecSlot; infer_instance

/-- Protobuf's runtime fields of a `*Decisions_DecidedSlot` at `l`, owned. -/
def rtDecSlot (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*Decisions_DecidedSlot` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptDecSlot (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions_DecidedSlot) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsDecSlot l dq v ∗ inv pbRtN (rtDecSlot l))

theorem ptDecSlot_own (l : Loc) (v : raxos.replica.src.Decisions_DecidedSlot) :
    ptDecSlot (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptDecSlot; exact if_pos rfl

theorem ptDecSlot_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions_DecidedSlot) (h : dq ≠ DFrac.own 1) :
    ptDecSlot (GF := GF) l dq v = iprop(fieldsDecSlot l dq v ∗ inv pbRtN (rtDecSlot l)) := by
  unfold ptDecSlot; exact if_neg h

instance ptDecSlot_pers (l : Loc) (v : raxos.replica.src.Decisions_DecidedSlot) :
    Persistent (ptDecSlot (GF := GF) l .discard v) := by
  rw [ptDecSlot_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*Decisions_DecidedSlot`: an owned one gives its runtime fields to an invariant. -/
theorem ptDecSlot_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions_DecidedSlot) :
    ptDecSlot (GF := GF) l dq v ⊢ |={E}=> ptDecSlot l .discard v := by
  rw [ptDecSlot_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptDecSlot_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtDecSlot (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtDecSlot; iexists _, _; iframe
    ipersist unknownFields; ipersist Index; ipersist Ids; ipersist Proposer;
    imodintro; unfold fieldsDecSlot; iframe #; ipureintro; exact Hnn
  · rw [ptDecSlot_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsDecSlot_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*Decisions_DecidedSlot`. -/
theorem ptDecSlot_share (E : CoPset) (l : Loc) (v : raxos.replica.src.Decisions_DecidedSlot) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptDecSlot l .discard v := by
  rw [← ptDecSlot_own]; exact ptDecSlot_persist E l _ v

theorem ptDecSlot_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions_DecidedSlot) :
    ptDecSlot (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptDecSlot_own]; exact typedPointsto_not_null _ _ _
  · rw [ptDecSlot_shared l dq v h]
    unfold fieldsDecSlot
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptDecSlot_fields (l : Loc) (v : raxos.replica.src.Decisions_DecidedSlot) :
    ptDecSlot (GF := GF) l .discard v ⊢ fieldsDecSlot l .discard v := by
  rw [ptDecSlot_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptDecSlot_access_load_unknownFields (l : Loc) (v : raxos.replica.src.Decisions_DecidedSlot) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"unknownFields" l) v.unknownFields' dq) (ptDecSlot l dq v) (ptDecSlot l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDecSlot_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDecSlot_shared l dq v h]
      unfold fieldsDecSlot
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptDecSlot_access_load_Index (l : Loc) (v : raxos.replica.src.Decisions_DecidedSlot) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Index" l) v.Index' dq) (typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Index" l) v.Index' dq) (ptDecSlot l dq v) (ptDecSlot l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDecSlot_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Index" l) v.Index' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDecSlot_shared l dq v h]
      unfold fieldsDecSlot
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Index
      iintro Index
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptDecSlot_access_load_Ids (l : Loc) (v : raxos.replica.src.Decisions_DecidedSlot) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Ids" l) v.Ids' dq) (typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Ids" l) v.Ids' dq) (ptDecSlot l dq v) (ptDecSlot l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDecSlot_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Ids" l) v.Ids' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDecSlot_shared l dq v h]
      unfold fieldsDecSlot
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Ids
      iintro Ids
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptDecSlot_access_load_Proposer (l : Loc) (v : raxos.replica.src.Decisions_DecidedSlot) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Proposer" l) v.Proposer' dq) (typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Proposer" l) v.Proposer' dq) (ptDecSlot l dq v) (ptDecSlot l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDecSlot_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.Decisions_DecidedSlot go!"Proposer" l) v.Proposer' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDecSlot_shared l dq v h]
      unfold fieldsDecSlot
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Proposer
      iintro Proposer
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*Decisions` -/

/-- The fields of a `*Decisions` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsDecs (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.Decisions go!"unknownFields" l) v.unknownFields' dq ∗
    "DecidedSlots" ∷ typedPointsto (structFieldRef raxos.replica.src.Decisions go!"DecidedSlots" l) v.DecidedSlots' dq ∗
    "_" ∷ True)

theorem fieldsDecs_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions) :
    fieldsDecs (GF := GF) l dq v ⊢ |==> fieldsDecs l .discard v := by
  unfold fieldsDecs
  iintro H
  iNamed H
  ipersist unknownFields; ipersist DecidedSlots;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsDecs_pers (l : Loc) (v : raxos.replica.src.Decisions) :
    Persistent (fieldsDecs (GF := GF) l .discard v) := by
  unfold fieldsDecs; infer_instance

/-- Protobuf's runtime fields of a `*Decisions` at `l`, owned. -/
def rtDecs (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.Decisions go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.Decisions go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*Decisions` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptDecs (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsDecs l dq v ∗ inv pbRtN (rtDecs l))

theorem ptDecs_own (l : Loc) (v : raxos.replica.src.Decisions) :
    ptDecs (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptDecs; exact if_pos rfl

theorem ptDecs_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions) (h : dq ≠ DFrac.own 1) :
    ptDecs (GF := GF) l dq v = iprop(fieldsDecs l dq v ∗ inv pbRtN (rtDecs l)) := by
  unfold ptDecs; exact if_neg h

instance ptDecs_pers (l : Loc) (v : raxos.replica.src.Decisions) :
    Persistent (ptDecs (GF := GF) l .discard v) := by
  rw [ptDecs_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*Decisions`: an owned one gives its runtime fields to an invariant. -/
theorem ptDecs_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions) :
    ptDecs (GF := GF) l dq v ⊢ |={E}=> ptDecs l .discard v := by
  rw [ptDecs_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptDecs_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtDecs (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtDecs; iexists _, _; iframe
    ipersist unknownFields; ipersist DecidedSlots;
    imodintro; unfold fieldsDecs; iframe #; ipureintro; exact Hnn
  · rw [ptDecs_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsDecs_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*Decisions`. -/
theorem ptDecs_share (E : CoPset) (l : Loc) (v : raxos.replica.src.Decisions) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptDecs l .discard v := by
  rw [← ptDecs_own]; exact ptDecs_persist E l _ v

theorem ptDecs_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.Decisions) :
    ptDecs (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptDecs_own]; exact typedPointsto_not_null _ _ _
  · rw [ptDecs_shared l dq v h]
    unfold fieldsDecs
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptDecs_fields (l : Loc) (v : raxos.replica.src.Decisions) :
    ptDecs (GF := GF) l .discard v ⊢ fieldsDecs l .discard v := by
  rw [ptDecs_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptDecs_access_load_unknownFields (l : Loc) (v : raxos.replica.src.Decisions) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.Decisions go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.Decisions go!"unknownFields" l) v.unknownFields' dq) (ptDecs l dq v) (ptDecs l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDecs_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.Decisions go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDecs_shared l dq v h]
      unfold fieldsDecs
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptDecs_access_load_DecidedSlots (l : Loc) (v : raxos.replica.src.Decisions) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.Decisions go!"DecidedSlots" l) v.DecidedSlots' dq) (typedPointsto (structFieldRef raxos.replica.src.Decisions go!"DecidedSlots" l) v.DecidedSlots' dq) (ptDecs l dq v) (ptDecs l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptDecs_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.Decisions go!"DecidedSlots" l) v.DecidedSlots' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptDecs_shared l dq v h]
      unfold fieldsDecs
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe DecidedSlots
      iintro DecidedSlots
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*Empty` -/

/-- The fields of a `*Empty` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsEmpty (l : Loc) (dq : DFrac) (v : raxos.replica.src.Empty) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.replica.src.Empty go!"unknownFields" l) v.unknownFields' dq ∗
    "_" ∷ True)

theorem fieldsEmpty_persist (l : Loc) (dq : DFrac) (v : raxos.replica.src.Empty) :
    fieldsEmpty (GF := GF) l dq v ⊢ |==> fieldsEmpty l .discard v := by
  unfold fieldsEmpty
  iintro H
  iNamed H
  ipersist unknownFields;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsEmpty_pers (l : Loc) (v : raxos.replica.src.Empty) :
    Persistent (fieldsEmpty (GF := GF) l .discard v) := by
  unfold fieldsEmpty; infer_instance

/-- Protobuf's runtime fields of a `*Empty` at `l`, owned. -/
def rtEmpty (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.replica.src.Empty go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.replica.src.Empty go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*Empty` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptEmpty (l : Loc) (dq : DFrac) (v : raxos.replica.src.Empty) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsEmpty l dq v ∗ inv pbRtN (rtEmpty l))

theorem ptEmpty_own (l : Loc) (v : raxos.replica.src.Empty) :
    ptEmpty (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptEmpty; exact if_pos rfl

theorem ptEmpty_shared (l : Loc) (dq : DFrac) (v : raxos.replica.src.Empty) (h : dq ≠ DFrac.own 1) :
    ptEmpty (GF := GF) l dq v = iprop(fieldsEmpty l dq v ∗ inv pbRtN (rtEmpty l)) := by
  unfold ptEmpty; exact if_neg h

instance ptEmpty_pers (l : Loc) (v : raxos.replica.src.Empty) :
    Persistent (ptEmpty (GF := GF) l .discard v) := by
  rw [ptEmpty_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*Empty`: an owned one gives its runtime fields to an invariant. -/
theorem ptEmpty_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.replica.src.Empty) :
    ptEmpty (GF := GF) l dq v ⊢ |={E}=> ptEmpty l .discard v := by
  rw [ptEmpty_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptEmpty_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtEmpty (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtEmpty; iexists _, _; iframe
    ipersist unknownFields;
    imodintro; unfold fieldsEmpty; iframe #; ipureintro; exact Hnn
  · rw [ptEmpty_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsEmpty_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*Empty`. -/
theorem ptEmpty_share (E : CoPset) (l : Loc) (v : raxos.replica.src.Empty) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptEmpty l .discard v := by
  rw [← ptEmpty_own]; exact ptEmpty_persist E l _ v

theorem ptEmpty_not_null (l : Loc) (dq : DFrac) (v : raxos.replica.src.Empty) :
    ptEmpty (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptEmpty_own]; exact typedPointsto_not_null _ _ _
  · rw [ptEmpty_shared l dq v h]
    unfold fieldsEmpty
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptEmpty_fields (l : Loc) (v : raxos.replica.src.Empty) :
    ptEmpty (GF := GF) l .discard v ⊢ fieldsEmpty l .discard v := by
  rw [ptEmpty_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptEmpty_access_load_unknownFields (l : Loc) (v : raxos.replica.src.Empty) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.replica.src.Empty go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.replica.src.Empty go!"unknownFields" l) v.unknownFields' dq) (ptEmpty l dq v) (ptEmpty l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptEmpty_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.replica.src.Empty go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptEmpty_shared l dq v h]
      unfold fieldsEmpty
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*ClientBatch_SingleMessage` -/

/-- The fields of a `*ClientBatch_SingleMessage` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsCSingle (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch_SingleMessage) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.proto.client.ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' dq ∗
    "Message" ∷ typedPointsto (structFieldRef raxos.proto.client.ClientBatch_SingleMessage go!"Message" l) v.Message' dq ∗
    "_" ∷ True)

theorem fieldsCSingle_persist (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch_SingleMessage) :
    fieldsCSingle (GF := GF) l dq v ⊢ |==> fieldsCSingle l .discard v := by
  unfold fieldsCSingle
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Message;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsCSingle_pers (l : Loc) (v : raxos.proto.client.ClientBatch_SingleMessage) :
    Persistent (fieldsCSingle (GF := GF) l .discard v) := by
  unfold fieldsCSingle; infer_instance

/-- Protobuf's runtime fields of a `*ClientBatch_SingleMessage` at `l`, owned. -/
def rtCSingle (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.proto.client.ClientBatch_SingleMessage go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.proto.client.ClientBatch_SingleMessage go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*ClientBatch_SingleMessage` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptCSingle (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch_SingleMessage) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsCSingle l dq v ∗ inv pbRtN (rtCSingle l))

theorem ptCSingle_own (l : Loc) (v : raxos.proto.client.ClientBatch_SingleMessage) :
    ptCSingle (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptCSingle; exact if_pos rfl

theorem ptCSingle_shared (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch_SingleMessage) (h : dq ≠ DFrac.own 1) :
    ptCSingle (GF := GF) l dq v = iprop(fieldsCSingle l dq v ∗ inv pbRtN (rtCSingle l)) := by
  unfold ptCSingle; exact if_neg h

instance ptCSingle_pers (l : Loc) (v : raxos.proto.client.ClientBatch_SingleMessage) :
    Persistent (ptCSingle (GF := GF) l .discard v) := by
  rw [ptCSingle_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*ClientBatch_SingleMessage`: an owned one gives its runtime fields to an invariant. -/
theorem ptCSingle_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch_SingleMessage) :
    ptCSingle (GF := GF) l dq v ⊢ |={E}=> ptCSingle l .discard v := by
  rw [ptCSingle_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptCSingle_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtCSingle (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtCSingle; iexists _, _; iframe
    ipersist unknownFields; ipersist Message;
    imodintro; unfold fieldsCSingle; iframe #; ipureintro; exact Hnn
  · rw [ptCSingle_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsCSingle_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*ClientBatch_SingleMessage`. -/
theorem ptCSingle_share (E : CoPset) (l : Loc) (v : raxos.proto.client.ClientBatch_SingleMessage) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptCSingle l .discard v := by
  rw [← ptCSingle_own]; exact ptCSingle_persist E l _ v

theorem ptCSingle_not_null (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch_SingleMessage) :
    ptCSingle (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptCSingle_own]; exact typedPointsto_not_null _ _ _
  · rw [ptCSingle_shared l dq v h]
    unfold fieldsCSingle
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptCSingle_fields (l : Loc) (v : raxos.proto.client.ClientBatch_SingleMessage) :
    ptCSingle (GF := GF) l .discard v ⊢ fieldsCSingle l .discard v := by
  rw [ptCSingle_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptCSingle_access_load_unknownFields (l : Loc) (v : raxos.proto.client.ClientBatch_SingleMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' dq) (ptCSingle l dq v) (ptCSingle l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptCSingle_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.proto.client.ClientBatch_SingleMessage go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptCSingle_shared l dq v h]
      unfold fieldsCSingle
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptCSingle_access_load_Message (l : Loc) (v : raxos.proto.client.ClientBatch_SingleMessage) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch_SingleMessage go!"Message" l) v.Message' dq) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch_SingleMessage go!"Message" l) v.Message' dq) (ptCSingle l dq v) (ptCSingle l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptCSingle_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.proto.client.ClientBatch_SingleMessage go!"Message" l) v.Message' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptCSingle_shared l dq v h]
      unfold fieldsCSingle
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Message
      iintro Message
      iframe; iframe #; ipureintro; exact Hl_nn

/-! ### `*ClientBatch` -/

/-- The fields of a `*ClientBatch` at `l` the program reads: all but protobuf's runtime fields
`state`, `sizeCache`. -/
def fieldsCB (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch) : IProp GF :=
  iprop("%Hl_nn" ∷ ⌜l ≠ null⌝ ∗
    "unknownFields" ∷ typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"unknownFields" l) v.unknownFields' dq ∗
    "Sender" ∷ typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Sender" l) v.Sender' dq ∗
    "Messages" ∷ typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Messages" l) v.Messages' dq ∗
    "Id" ∷ typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Id" l) v.Id' dq ∗
    "_" ∷ True)

theorem fieldsCB_persist (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch) :
    fieldsCB (GF := GF) l dq v ⊢ |==> fieldsCB l .discard v := by
  unfold fieldsCB
  iintro H
  iNamed H
  ipersist unknownFields; ipersist Sender; ipersist Messages; ipersist Id;
  imodintro; iframe #; ipureintro; exact Hl_nn

instance fieldsCB_pers (l : Loc) (v : raxos.proto.client.ClientBatch) :
    Persistent (fieldsCB (GF := GF) l .discard v) := by
  unfold fieldsCB; infer_instance

/-- Protobuf's runtime fields of a `*ClientBatch` at `l`, owned. -/
def rtCB (l : Loc) : IProp GF :=
  iprop(∃ (st : _root_.Perennial.google_golang_org.protobuf.internal.impl.MessageState) (sc : w32),
    typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"state" l) st (DFrac.own 1) ∗
    typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"sizeCache" l) sc (DFrac.own 1))

open scoped Classical in
/-- A `*ClientBatch` at `l` read with `dq`: owned (`dq = 1`), the whole struct; shared, its fields
with `dq` and its runtime fields protobuf's, in an invariant. -/
def ptCB (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch) : IProp GF :=
  if dq = DFrac.own 1 then iprop(l ↦ v) else iprop(fieldsCB l dq v ∗ inv pbRtN (rtCB l))

theorem ptCB_own (l : Loc) (v : raxos.proto.client.ClientBatch) :
    ptCB (GF := GF) l (DFrac.own 1) v = iprop(l ↦ v) := by
  unfold ptCB; exact if_pos rfl

theorem ptCB_shared (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch) (h : dq ≠ DFrac.own 1) :
    ptCB (GF := GF) l dq v = iprop(fieldsCB l dq v ∗ inv pbRtN (rtCB l)) := by
  unfold ptCB; exact if_neg h

instance ptCB_pers (l : Loc) (v : raxos.proto.client.ClientBatch) :
    Persistent (ptCB (GF := GF) l .discard v) := by
  rw [ptCB_shared _ _ _ discard_ne_own]; infer_instance

/-- Sharing a `*ClientBatch`: an owned one gives its runtime fields to an invariant. -/
theorem ptCB_persist (E : CoPset) (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch) :
    ptCB (GF := GF) l dq v ⊢ |={E}=> ptCB l .discard v := by
  rw [ptCB_shared l .discard v discard_ne_own]
  by_cases h : dq = DFrac.own 1
  · subst h
    rw [ptCB_own]
    iintro Hv
    ihave %Hnn := typedPointsto_not_null $$ Hv
    iStructNamed Hv
    imod inv_alloc pbRtN E (rtCB (GF := GF) l) $$ [state sizeCache] with #Hi
    · inext; unfold rtCB; iexists _, _; iframe
    ipersist unknownFields; ipersist Sender; ipersist Messages; ipersist Id;
    imodintro; unfold fieldsCB; iframe #; ipureintro; exact Hnn
  · rw [ptCB_shared l dq v h]
    iintro ⟨Hf, #Hi⟩
    imod fieldsCB_persist _ _ _ $$ Hf with #Hf
    imodintro; iframe #

/-- Sharing a freshly owned `*ClientBatch`. -/
theorem ptCB_share (E : CoPset) (l : Loc) (v : raxos.proto.client.ClientBatch) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢ |={E}=> ptCB l .discard v := by
  rw [← ptCB_own]; exact ptCB_persist E l _ v

theorem ptCB_not_null (l : Loc) (dq : DFrac) (v : raxos.proto.client.ClientBatch) :
    ptCB (GF := GF) l dq v ⊢ ⌜l ≠ null⌝ := by
  by_cases h : dq = DFrac.own 1
  · subst h; rw [ptCB_own]; exact typedPointsto_not_null _ _ _
  · rw [ptCB_shared l dq v h]
    unfold fieldsCB
    iintro ⟨H, -⟩
    iNamed H
    ipureintro; exact Hl_nn

theorem ptCB_fields (l : Loc) (v : raxos.proto.client.ClientBatch) :
    ptCB (GF := GF) l .discard v ⊢ fieldsCB l .discard v := by
  rw [ptCB_shared l _ v discard_ne_own]; iintro ⟨H, -⟩; iexact H

instance (priority := high) ptCB_access_load_unknownFields (l : Loc) (v : raxos.proto.client.ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"unknownFields" l) v.unknownFields' dq) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"unknownFields" l) v.unknownFields' dq) (ptCB l dq v) (ptCB l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptCB_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"unknownFields" l) v.unknownFields' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptCB_shared l dq v h]
      unfold fieldsCB
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe unknownFields
      iintro unknownFields
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptCB_access_load_Sender (l : Loc) (v : raxos.proto.client.ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Sender" l) v.Sender' dq) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Sender" l) v.Sender' dq) (ptCB l dq v) (ptCB l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptCB_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Sender" l) v.Sender' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptCB_shared l dq v h]
      unfold fieldsCB
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Sender
      iintro Sender
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptCB_access_load_Messages (l : Loc) (v : raxos.proto.client.ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Messages" l) v.Messages' dq) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Messages" l) v.Messages' dq) (ptCB l dq v) (ptCB l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptCB_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Messages" l) v.Messages' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptCB_shared l dq v h]
      unfold fieldsCB
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Messages
      iintro Messages
      iframe; iframe #; ipureintro; exact Hl_nn

instance (priority := high) ptCB_access_load_Id (l : Loc) (v : raxos.proto.client.ClientBatch) (dq : DFrac) :
    Access (PROP := IProp GF) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Id" l) v.Id' dq) (typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Id" l) v.Id' dq) (ptCB l dq v) (ptCB l dq v) where
  access := by
    by_cases h : dq = DFrac.own 1
    · subst h; rw [ptCB_own]
      exact Access.access (A := typedPointsto (structFieldRef raxos.proto.client.ClientBatch go!"Id" l) v.Id' (DFrac.own 1))
        (P := typedPointsto l v (DFrac.own 1))
    · rw [ptCB_shared l dq v h]
      unfold fieldsCB
      iintro ⟨H, #Hi⟩
      iNamed H
      iframe Id
      iintro Id
      iframe; iframe #; ipureintro; exact Hl_nn


open raxos.replica.src in
/-- Pointers `ps` to single messages (of a type whose rep is `single`), one per string. -/
def repList {A : Type} (rep : Loc → DFrac → A → IProp GF) (ps : List Loc) (dq : DFrac)
    (xs : List A) : IProp GF :=
  iprop(⌜ps.length = xs.length⌝ ∗ [∗list] i ↦ p ∈ ps, ∃ x, ⌜xs[i]? = some x⌝ ∗ rep p dq x)

/-- `*ProposerMessage_ClientBatch_SingleMessage`. -/
def repPMSingle (l : Loc) (dq : DFrac) (m : GoString) : IProp GF :=
  iprop(∃ x : raxos.replica.src.ProposerMessage_ClientBatch_SingleMessage,
    ptPMSingle l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ ⌜x.Message' = m⌝)

/-- `*ProposerMessage_ClientBatch`. -/
def repPMBatch (l : Loc) (dq : DFrac) (b : Batch) : IProp GF :=
  iprop(∃ (x : raxos.replica.src.ProposerMessage_ClientBatch) (ps : List Loc),
    ptPMBatch l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ ⌜sint.Z x.Sender' = b.sender ∧ x.Id' = b.id⌝ ∗
    x.Messages' ↦*{dq} ps ∗ repList repPMSingle ps dq b.cmds)

/-- `*ProposerMessage_DecidedSlot`. -/
def repPMSlot (l : Loc) (dq : DFrac) (d : DSlot) : IProp GF :=
  iprop(∃ x : raxos.replica.src.ProposerMessage_DecidedSlot,
    ptPMSlot l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.Index' = d.index ∧ sint.Z x.Proposer' = d.proposer⌝ ∗
    x.Ids' ↦*{dq} d.ids)

/-- `*ProposerMessage_Proposal`. -/
def repProp (l : Loc) (dq : DFrac) (p : Prop') : IProp GF :=
  iprop(∃ (x : raxos.replica.src.ProposerMessage_Proposal) (bps : List Loc),
    ptProp l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.Priority' = p.prio ∧ sint.Z x.ProposerId' = p.pid ∧ sint.Z x.ThreadId' = p.tid⌝ ∗
    x.Ids' ↦*{dq} p.ids ∗ x.ClientBatches' ↦*{dq} bps ∗ repList repPMBatch bps dq p.batches)

/-- `*ProposerMessage`. -/
def repPM (l : Loc) (dq : DFrac) (m : PM) : IProp GF :=
  iprop(∃ (x : raxos.replica.src.ProposerMessage) (sps : List Loc),
    ptPM l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.Sender' = m.sender ∧ sint.Z x.Index' = m.index ∧ sint.Z x.S' = m.s⌝ ∗
    (match m.p with
     | none => iprop(⌜x.P' = null⌝)
     | some p => repProp x.P' dq p) ∗
    x.DecidedSlots' ↦*{dq} sps ∗ repList repPMSlot sps dq m.slots)

/-- `*RecorderResponse_Proposal`. -/
def repRRProp (l : Loc) (dq : DFrac) (p : RRProp) : IProp GF :=
  iprop(∃ x : raxos.replica.src.RecorderResponse_Proposal,
    ptRRProp l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
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
    ptRR l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.S' = r.s ∧ x.ClientBatchesNotFound' = r.notFound⌝ ∗
    repOpt repRRProp x.F' dq r.f ∗ repOpt repRRProp x.M' dq r.m)

/-- `*DecideRequest`. -/
def repDReq (l : Loc) (dq : DFrac) (ids : List GoString) : IProp GF :=
  iprop(∃ x : raxos.replica.src.DecideRequest,
    ptDReq l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ x.Ids' ↦*{dq} ids)

/-- `*DecideResponse_ClientBatch_SingleMessage`. -/
def repDRSingle (l : Loc) (dq : DFrac) (m : GoString) : IProp GF :=
  iprop(∃ x : raxos.replica.src.DecideResponse_ClientBatch_SingleMessage,
    ptDRSingle l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ ⌜x.Message' = m⌝)

/-- `*DecideResponse_ClientBatch`. -/
def repDRBatch (l : Loc) (dq : DFrac) (b : Batch) : IProp GF :=
  iprop(∃ (x : raxos.replica.src.DecideResponse_ClientBatch) (ps : List Loc),
    ptDRBatch l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ ⌜sint.Z x.Sender' = b.sender ∧ x.Id' = b.id⌝ ∗
    x.Messages' ↦*{dq} ps ∗ repList repDRSingle ps dq b.cmds)

/-- `*DecideResponse`. -/
def repDResp (l : Loc) (dq : DFrac) (bs : List Batch) : IProp GF :=
  iprop(∃ (x : raxos.replica.src.DecideResponse) (ps : List Loc),
    ptDResp l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ x.ClientBatches' ↦*{dq} ps ∗
    repList repDRBatch ps dq bs)

/-- `*Decisions_DecidedSlot`. -/
def repDecSlot (l : Loc) (dq : DFrac) (d : DSlot) : IProp GF :=
  iprop(∃ x : raxos.replica.src.Decisions_DecidedSlot,
    ptDecSlot l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗
    ⌜sint.Z x.Index' = d.index ∧ sint.Z x.Proposer' = d.proposer⌝ ∗
    x.Ids' ↦*{dq} d.ids)

/-- `*Decisions`. -/
def repDecs (l : Loc) (dq : DFrac) (ds : List DSlot) : IProp GF :=
  iprop(∃ (x : raxos.replica.src.Decisions) (ps : List Loc),
    ptDecs l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ x.DecidedSlots' ↦*{dq} ps ∗
    repList repDecSlot ps dq ds)

/-- `*Empty`. -/
def repEmpty (l : Loc) (dq : DFrac) : IProp GF :=
  iprop(∃ x : raxos.replica.src.Empty, ptEmpty l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝)

/-- `*client.ClientBatch_SingleMessage`. -/
def repCSingle (l : Loc) (dq : DFrac) (m : GoString) : IProp GF :=
  iprop(∃ x : raxos.proto.client.ClientBatch_SingleMessage,
    ptCSingle l dq x ∗ ⌜x.unknownFields'.len = W64 0⌝ ∗ ⌜x.Message' = m⌝)

/-- A `client.ClientBatch` value's fields (its slice of messages read with `dq`), no unknown
fields. -/
def repCBVal (x : raxos.proto.client.ClientBatch) (dq : DFrac) (b : Batch) : IProp GF :=
  iprop(∃ ps : List Loc,
    ⌜sint.Z x.Sender' = b.sender ∧ x.Id' = b.id ∧ x.unknownFields'.len = W64 0⌝ ∗
    x.Messages' ↦*{dq} ps ∗ repList repCSingle ps dq b.cmds)

/-- `*client.ClientBatch`. -/
def repCB (l : Loc) (dq : DFrac) (b : Batch) : IProp GF :=
  iprop(∃ x : raxos.proto.client.ClientBatch, ptCB l dq x ∗ repCBVal x dq b)

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
