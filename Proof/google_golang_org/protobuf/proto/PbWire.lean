/-
**A descriptor-driven wire semantics of protobuf: a candidate, NOTHING TRUSTS IT YET** (protobuf
stage 0', `mit-pdos/etcd-grove#20`, kaashoek's item 2 (b); the plan
`mit-pdos/perennial#659`). No axiom, spec or proof refers to this module; it is wired into nothing
(a defs module that only `PbWireVectors.lean`, its tests, imports). The repository keeps one
trusted protobuf semantics, pbgen (`notes/decisions.md`, "Trusted generated code", 2026-11-19),
and the per-type Lean models of `InvProto.lean`; whether this module ever becomes a trusted
meaning of "protobuf" (replacing per-type encoder axioms, `enc_ok`) is a decision for
upamanyus and kaashoek (#20, item 2 (a)), and it would then need an axiom review of its own.

**What it is.** For a message descriptor (`Msg`: the fields of a protobuf message type, as
`models/pbdesc` dumps them from the registered descriptors) and a message value (`Value.msg`:
its populated fields by number, and its unknown-field bytes), `encode` is the bytes
protobuf-go v1.36.12's `proto.Marshal` writes (`none`: the error it returns), and `decode` the
message `proto.Unmarshal` fills in (`none`: its error). Both are total, computable functions
by structural recursion: `encode` of a small message reduces by `rfl`; `decode`, whose nesting
bound is 10000 levels, is checked by evaluation (`#guard`). Evidence: `PbWireVectors.lean`, whose
vectors are written by `examples/pbwire` (protobuf-go, and pbgen's codec where pbgen's subset
covers the type) and checked here by `#guard` at every build.

**Covered:** the integer kinds (`int32`, `int64`, `uint32`, `uint64`, `sint32`, `sint64`,
`fixed32`, `fixed64`, `sfixed32`, `sfixed64`), `bool`, enums (open and closed: protobuf-go's fast
path does not check a closed enum's values), `string` (validated UTF-8 or not: proto3 and proto2),
`bytes`, messages; singular fields with implicit presence (proto3), with explicit presence (proto2
`optional`, proto3 `optional`, messages), repeated fields packed or not, oneofs; unknown fields.
**Not covered** (the descriptor cannot say them: `examples/pbwire`'s renderer refuses them):
`float`/`double`, groups, maps, extensions, `required`, MessageSet; `proto.Size`, `Merge`,
`Clone`, non-default options.

**The encoding** (`encode`; protobuf-go v1.36.12 by file and line, `internal/impl/` unless said):
- the fields outside any oneof in increasing number order, then the oneofs' members in the oneofs'
  declaration order (`encode.go:176` walks `orderedCoderFields`, sorted by number,
  `codec_message.go:158`, then, in a message with oneofs, by `order.LegacyFieldOrder`, "marshal
  oneofs last", `codec_message.go:177-184`), then the unknown fields' bytes verbatim
  (`encode.go:220-224`);
- each record: the tag `varint(num * 8 + wire type)` (`protowire.AppendTag`), then the value: a
  varint (wire type 0) of the 64-bit two's complement (`int32`, `int64`, enums: an `int32` is
  sign-extended, 10 bytes when negative), of the value (`uint32`, `uint64`), of its ZigZag
  (`sint32`, `sint64`), 0 or 1 (`bool`); 4 little-endian bytes (5: `fixed32`, `sfixed32`), 8 (1:
  `fixed64`, `sfixed64`); a length and the bytes (2: `string`, `bytes`, a message's encoding);
- implicit presence: omitted at the zero value (`codec_tables.go:200-203`, the `NoZero` coders);
  explicit presence: written whenever present, zero or not; repeated: one record per element, or,
  packed, one record of the elements' values without tags, omitted when empty
  (`appendUint64PackedSlice`, `codec_gen.go`);
- a validated string (`utf8`, proto3) that is not valid UTF-8: an error
  (`appendStringNoZeroValidateUTF8`, `codec_gen.go:5107`).

**The decoding** (`decode`; `decode.go:125-236`, `unmarshalPointerEager`), from an empty message,
the input's records in order:
- a tag (a varint: at most 10 bytes, the 10th 0 or 1, `protowire.ConsumeVarint`; possibly not
  minimal); its number must be in `1 .. 2^29 - 1` and its wire type not 4 (end group: no group is
  open at a message's level), else an error (`decode.go:154-166`);
- a field of the descriptor with its own wire type, or a repeated scalar with wire type 2
  (packed: the values to the record's end, each whole, `consumeUint64Slice`): its value, of the Go
  type (a varint truncated: `int32(v)`, `uint32(v)`, `v != 0`, `int32(DecodeZigZag(v & 0xffffffff))`);
  a singular field takes it ("last one wins"), a repeated one appends it; a singular message merges
  the record into the message already there (decodes it into that message, `consumeMessageInfo`,
  `codec_field.go:175`), a repeated one appends a fresh message; a oneof member clears the oneof's
  other member (a message member already set merges, `codec_field.go:53-59`); a validated string
  that is not UTF-8: an error;
- any other record (a number the descriptor does not have, or a field's number with another wire
  type, the coders' `errUnknown`): skipped by `protowire.ConsumeFieldValue` (its groups nested at
  most 10001 deep, an end group of the right number, wire types 6 and 7 errors) and kept in the
  unknown fields as its tag re-encoded minimally and its value verbatim (`decode.go:222-229`);
- nesting: each message takes one of 10000 levels, the outermost included (`decode.go:105`).
A decoded message is in the canonical form `canonical` describes (what Go can observe of it: an
implicit-presence field at its zero value is absent).
-/
module

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace PbWire

/-! ## Descriptors -/

/-- A field's kind (`protoreflect.Kind`, the ones covered); a message kind names its type. -/
inductive Kind where
  | int32 | int64 | uint32 | uint64 | sint32 | sint64 | bool | enum
  | fixed32 | fixed64 | sfixed32 | sfixed64 | string | bytes
  | message (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- A field's cardinality and presence: singular with implicit presence (a proto3 scalar outside
any oneof: absent at its zero value), singular with explicit presence (proto2 `optional`, proto3
`optional`, a oneof member, every message field), repeated. -/
inductive Card where
  | implicit | explicit | repeated
  deriving DecidableEq, Repr, Inhabited

/-- A field of a message descriptor. `oneof`: the (non-synthetic) oneof it belongs to; `packed`:
a repeated scalar encoded packed; `utf8`: a string whose bytes are validated (proto3's). -/
structure Field where
  name : String
  num : Nat
  kind : Kind
  card : Card
  packed : Bool := false
  oneof : Option String := none
  utf8 : Bool := false
  deriving Repr, Inhabited

/-- A message descriptor: its full name and its fields, in declaration order (the oneofs are
written in their declaration order, `Msg.position`). -/
structure Msg where
  name : String
  fields : List Field
  deriving Repr, Inhabited

/-- The descriptors of a closure of message types, looked up by full name. -/
abbrev Desc := List Msg

def Desc.lookup (D : Desc) (name : String) : Option Msg := D.find? (·.name == name)

def Msg.field? (m : Msg) (num : Nat) : Option Field := m.fields.find? (·.num == num)

/-! ## Values -/

abbrev Byte := BitVec 8

/-- A message value. A field's value is an integer (every integer kind and enums: the Go value,
signed or not), a `bool`, bytes (`bytes`, and a `string`'s UTF-8 bytes), a message (its populated
fields by number, and its unknown fields' bytes), or a list (a repeated field's elements). -/
inductive Value where
  | int (x : Int)
  | bool (b : Bool)
  | bytes (bs : List Byte)
  | msg (fields : List (Nat × Value)) (unknown : List Byte)
  | list (vs : List Value)
  deriving Repr, Inhabited, BEq

/-- The empty message. -/
def Value.empty : Value := .msg [] []

/-! ## Wire primitives (`encoding/protowire`) -/

/-- The varint of `n` with at most `k` more bytes (`protowire.AppendVarint` for `k = 10`,
`n < 2^64`). -/
def varintK : Nat → Nat → List Byte
  | 0, n => [BitVec.ofNat 8 n]
  | k + 1, n => if n < 128 then [BitVec.ofNat 8 n] else BitVec.ofNat 8 (n % 128 + 128) :: varintK k (n / 128)

/-- `protowire.AppendVarint` (its argument a `uint64`: `n < 2^64`). -/
def varint (n : Nat) : List Byte := varintK 9 n

/-- `k` little-endian bytes of `n` (`protowire.AppendFixed32`/`AppendFixed64`, `k = 4, 8`). -/
def fixedLE : Nat → Nat → List Byte
  | 0, _ => []
  | k + 1, n => BitVec.ofNat 8 n :: fixedLE k (n / 256)

def tag (num wt : Nat) : List Byte := varint (num * 8 + wt)

/-- The 64-bit two's complement of `x` (`uint64(x)` of an `int64`). -/
def u64 (x : Int) : Nat := (x % (2 ^ 64 : Int)).toNat

/-- `protowire.EncodeZigZag`. -/
def zigzag (x : Int) : Nat := if 0 ≤ x then (2 * x).toNat else (-2 * x - 1).toNat

/-- `protowire.DecodeZigZag` of a value below `2^64`. -/
def unzigzag (v : Nat) : Int := if v % 2 = 0 then (v / 2 : Nat) else -((v / 2 : Nat) : Int) - 1

/-- The signed value of the low `w` bits of `v` (`int32(v)`, `int64(v)`). -/
def signed (w : Nat) (v : Nat) : Int :=
  let r := v % 2 ^ w
  if r < 2 ^ (w - 1) then r else (r : Int) - (2 ^ w : Nat)

/-- `protowire.ConsumeVarint`: the value and the rest; at most 10 bytes, the 10th 0 or 1 (`k`:
the index of the byte read). -/
def readVarintK (k : Nat) : List Byte → Option (Nat × List Byte)
  | [] => none
  | b :: bs =>
    if k = 9 then (if b.toNat ≤ 1 then some (b.toNat * 2 ^ 63, bs) else none)
    else if b.toNat < 128 then some (b.toNat * 2 ^ (7 * k), bs)
    else (readVarintK (k + 1) bs).map fun (v, r) => (v + (b.toNat - 128) * 2 ^ (7 * k), r)

def readVarint (bs : List Byte) : Option (Nat × List Byte) := readVarintK 0 bs

/-- `k` little-endian bytes. -/
def readFixed (k : Nat) (bs : List Byte) : Option (Nat × List Byte) :=
  if bs.length < k then none
  else some ((bs.take k).foldr (fun b acc => b.toNat + 256 * acc) 0, bs.drop k)

/-- `protowire.ConsumeBytes`: a length, then that many bytes. -/
def readBytes (bs : List Byte) : Option (List Byte × List Byte) := do
  let (m, r) ← readVarint bs
  if r.length < m then none else some (r.take m, r.drop m)

/-! ## UTF-8 (`unicode/utf8.Valid`) -/

/-- `unicode/utf8.Valid`: well-formed UTF-8, no surrogates, no overlong forms, at most
U+10FFFF (Go's `acceptRanges`, `unicode/utf8/utf8.go`). -/
def validUTF8 : List Byte → Bool
  | [] => true
  | b0 :: rest =>
    let x := b0.toNat
    let cont (b : Byte) (lo hi : Nat) := lo ≤ b.toNat && b.toNat ≤ hi
    if x < 0x80 then validUTF8 rest
    else if 0xC2 ≤ x && x ≤ 0xDF then
      match rest with
      | b1 :: r => cont b1 0x80 0xBF && validUTF8 r
      | _ => false
    else if 0xE0 ≤ x && x ≤ 0xEF then
      let (lo, hi) := if x = 0xE0 then (0xA0, 0xBF) else if x = 0xED then (0x80, 0x9F) else (0x80, 0xBF)
      match rest with
      | b1 :: b2 :: r => cont b1 lo hi && cont b2 0x80 0xBF && validUTF8 r
      | _ => false
    else if 0xF0 ≤ x && x ≤ 0xF4 then
      let (lo, hi) := if x = 0xF0 then (0x90, 0xBF) else if x = 0xF4 then (0x80, 0x8F) else (0x80, 0xBF)
      match rest with
      | b1 :: b2 :: b3 :: r => cont b1 lo hi && cont b2 0x80 0xBF && cont b3 0x80 0xBF && validUTF8 r
      | _ => false
    else false

/-! ## Encoding -/

/-- The wire type of a kind's values. -/
def Kind.wireType : Kind → Nat
  | .fixed64 | .sfixed64 => 1
  | .fixed32 | .sfixed32 => 5
  | .string | .bytes | .message _ => 2
  | _ => 0

def Kind.isScalar : Kind → Bool
  | .string | .bytes | .message _ => false
  | _ => true

def inRange (lo hi : Int) (x : Int) : Bool := lo ≤ x && x < hi

/-- A non-message value's wire bytes (no tag), `none` if it is not of the kind (or out of its Go
type's range) or a validated string is not UTF-8. -/
def scalarPayload (k : Kind) (utf8 : Bool) : Value → Option (List Byte)
  | .int x =>
    match k with
    | .int32 | .enum => if inRange (-2 ^ 31) (2 ^ 31) x then some (varint (u64 x)) else none
    | .int64 => if inRange (-2 ^ 63) (2 ^ 63) x then some (varint (u64 x)) else none
    | .uint32 => if inRange 0 (2 ^ 32) x then some (varint x.toNat) else none
    | .uint64 => if inRange 0 (2 ^ 64) x then some (varint x.toNat) else none
    | .sint32 => if inRange (-2 ^ 31) (2 ^ 31) x then some (varint (zigzag x)) else none
    | .sint64 => if inRange (-2 ^ 63) (2 ^ 63) x then some (varint (zigzag x)) else none
    | .fixed32 => if inRange 0 (2 ^ 32) x then some (fixedLE 4 x.toNat) else none
    | .sfixed32 => if inRange (-2 ^ 31) (2 ^ 31) x then some (fixedLE 4 (u64 x)) else none
    | .fixed64 => if inRange 0 (2 ^ 64) x then some (fixedLE 8 x.toNat) else none
    | .sfixed64 => if inRange (-2 ^ 63) (2 ^ 63) x then some (fixedLE 8 (u64 x)) else none
    | _ => none
  | .bool b => if k == .bool then some [BitVec.ofNat 8 (if b then 1 else 0)] else none
  | .bytes bs =>
    match k with
    | .bytes => some (varint bs.length ++ bs)
    | .string => if !utf8 || validUTF8 bs then some (varint bs.length ++ bs) else none
    | _ => none
  | _ => none

/-- A value at its kind's zero (absent, for implicit presence). -/
def Value.isZero : Value → Bool
  | .int 0 | .bool false | .bytes [] => true
  | _ => false

/-- The oneofs of a message in declaration order (a oneof's members are declared together, so
the order of their first members is the oneofs' declaration order). -/
def Msg.oneofs (m : Msg) : List String :=
  m.fields.foldl (fun os f => match f.oneof with
    | some o => if os.contains o then os else os ++ [o]
    | none => os) []

/-- Where a field is written (`codec_message.go:177-184`: "to preserve compatibility with
historic wire output, marshal oneofs last", `order.LegacyFieldOrder`): a field outside any oneof
at its number, a oneof member after every such field, the oneofs in declaration order (only one
member of a oneof is ever written). -/
def Msg.position (m : Msg) (f : Field) : Nat :=
  match f.oneof with
  | none => f.num
  | some o => 2 ^ 29 + m.oneofs.idxOf o

/-- Stable insertion by position. -/
def insertByPos (p : Nat × List Byte) : List (Nat × List Byte) → List (Nat × List Byte)
  | [] => [p]
  | q :: qs => if p.1 < q.1 then p :: q :: qs else q :: insertByPos p qs

def sortByPos (ps : List (Nat × List Byte)) : List (Nat × List Byte) := ps.foldr insertByPos []

/-- Numbers strictly increasing (a message value's canonical field order). -/
def strictlyIncreasing : List Nat → Bool
  | a :: b :: rest => a < b && strictlyIncreasing (b :: rest)
  | _ => true

/-- At most one member of each oneof is populated. -/
def oneofsOk (m : Msg) (nums : List Nat) : Bool :=
  let os := nums.filterMap fun n => (m.field? n).bind (·.oneof)
  os.all fun o => os.count o ≤ 1

/-- A message's encoding from its fields' records: canonical order and oneofs checked, records
by position, then the unknown fields. -/
def assemble (md : Msg) (fs : List (Nat × Value)) (ps : List (Nat × List Byte)) (unk : List Byte) :
    Option (List Byte) :=
  if strictlyIncreasing (fs.map (·.1)) && oneofsOk md (fs.map (·.1)) then
    some ((sortByPos ps).flatMap (·.2) ++ unk)
  else none

mutual
/-- A message's populated fields, each with its position and its records. -/
def encFields (D : Desc) (m : Msg) : List (Nat × Value) → Option (List (Nat × List Byte))
  | [] => some []
  | p :: rest => do
    let b ← encPair D m p
    let r ← encFields D m rest
    pure (b :: r)

/-- One populated field: its position and its records. -/
def encPair (D : Desc) (m : Msg) : Nat × Value → Option (Nat × List Byte)
  | (n, v) => do
    let f ← m.field? n
    let b ← encField D f v
    pure (m.position f, b)

/-- A field's records (none at an implicit-presence zero). -/
def encField (D : Desc) (f : Field) : Value → Option (List Byte)
  | .msg fs unk =>
    match f.kind, f.card with
    | .message name, .explicit => do
      let md ← D.lookup name
      let ps ← encFields D md fs
      let body ← assemble md fs ps unk
      pure (tag f.num 2 ++ varint body.length ++ body)
    | _, _ => none
  | .list vs =>
    if f.card != .repeated then none
    else if f.packed && f.kind.isScalar then do
      let ps ← vs.mapM (scalarPayload f.kind f.utf8)
      let body := ps.flatten
      if vs.isEmpty then pure [] else pure (tag f.num 2 ++ varint body.length ++ body)
    else encList D f vs
  | v =>
    if f.card == .repeated then none
    else if f.card == .implicit && v.isZero then some []
    else do
      let p ← scalarPayload f.kind f.utf8 v
      pure (tag f.num f.kind.wireType ++ p)

/-- A repeated field's elements, one record each (not packed). -/
def encList (D : Desc) (f : Field) : List Value → Option (List Byte)
  | [] => some []
  | .msg fs unk :: vs =>
    match f.kind with
    | .message name => do
      let md ← D.lookup name
      let ps ← encFields D md fs
      let body ← assemble md fs ps unk
      let r ← encList D f vs
      pure (tag f.num 2 ++ varint body.length ++ body ++ r)
    | _ => none
  | v :: vs => do
    let p ← scalarPayload f.kind f.utf8 v
    let r ← encList D f vs
    pure (tag f.num f.kind.wireType ++ p ++ r)
end

/-- **`proto.Marshal`** of a message value of type `name` (`none`: Marshal's error). -/
def encode (D : Desc) (name : String) : Value → Option (List Byte)
  | .msg fs unk => do
    let md ← D.lookup name
    let ps ← encFields D md fs
    assemble md fs ps unk
  | _ => none

/-! ## Decoding -/

/-- `protowire.ConsumeFieldValue` of a field numbered `num` of wire type `wt` (inside groups,
nested at most `g - 1` more deep): the rest of the input. `fuel` exceeds the input's length, so it
never runs out (each step consumes a byte). -/
def skipValue : (fuel g num wt : Nat) → List Byte → Option (List Byte)
  | 0, _, _, _, _ => none
  | fuel + 1, g, num, wt, bs =>
    match wt with
    | 0 => (readVarint bs).map (·.2)
    | 1 => (readFixed 8 bs).map (·.2)
    | 5 => (readFixed 4 bs).map (·.2)
    | 2 => (readBytes bs).map (·.2)
    | 3 =>
      if g = 0 then none
      else
        -- the group's fields, to its end-group tag
        match readVarint bs with
        | none => none
        | some (t, r) =>
          let num2 := t / 8
          let wt2 := t % 8
          if num2 == 0 || num2 > 2 ^ 31 - 1 then none
          else if wt2 = 4 then (if num2 = num then some r else none)
          else do
            let r' ← skipValue fuel (g - 1) num2 wt2 r
            -- continue the same group (the group's own depth `g`)
            skipValue fuel g num 3 r'
    | _ => none

/-- Read one value of a scalar kind (not `string`/`bytes`) from its wire bytes. -/
def readScalar (k : Kind) (bs : List Byte) : Option (Value × List Byte) :=
  match k.wireType with
  | 0 => (readVarint bs).map fun (v, r) =>
    (match k with
     | .bool => .bool (v != 0)
     | .int32 | .enum => .int (signed 32 v)
     | .int64 => .int (signed 64 v)
     | .uint32 => .int (v % 2 ^ 32 : Nat)
     | .sint32 => .int (unzigzag (v % 2 ^ 32))
     | .sint64 => .int (unzigzag v)
     | _ => .int v, r)
  | 1 => (readFixed 8 bs).map fun (v, r) =>
    (match k with | .sfixed64 => .int (signed 64 v) | _ => .int v, r)
  | _ => (readFixed 4 bs).map fun (v, r) =>
    (match k with | .sfixed32 => .int (signed 32 v) | _ => .int v, r)

/-- All the values of a packed record. `fuel` exceeds the bytes' length. -/
def readPacked (k : Kind) : Nat → List Byte → Option (List Value)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, bs => do
    let (v, r) ← readScalar k bs
    let vs ← readPacked k fuel r
    pure (v :: vs)

/-- The field `n`'s current value. -/
def getField (fs : List (Nat × Value)) (n : Nat) : Option Value := (fs.find? (·.1 == n)).map (·.2)

/-- Set field `n` (keeping the numbers increasing); `none` removes it. -/
def setField (n : Nat) (v : Option Value) : List (Nat × Value) → List (Nat × Value)
  | [] => match v with | some v => [(n, v)] | none => []
  | (m, w) :: rest =>
    if m < n then (m, w) :: setField n v rest
    else if m = n then (match v with | some v => (n, v) :: rest | none => rest)
    else match v with | some v => (n, v) :: (m, w) :: rest | none => (m, w) :: rest

/-- Store a singular field's new value: an implicit-presence zero is absent; a oneof member clears
the oneof's other members. -/
def storeSingular (md : Msg) (f : Field) (v : Value) (fs : List (Nat × Value)) : List (Nat × Value) :=
  let fs := match f.oneof with
    | none => fs
    | some o => md.fields.foldl (fun fs g => if g.oneof == some o && g.num != f.num then setField g.num none fs else fs) fs
  setField f.num (if f.card == .implicit && v.isZero then none else some v) fs

/-- Append to a repeated field (an empty list is absent). -/
def appendRep (n : Nat) (vs : List Value) (fs : List (Nat × Value)) : List (Nat × Value) :=
  match getField fs n, vs with
  | _, [] => fs
  | some (.list old), _ => setField n (some (.list (old ++ vs))) fs
  | _, _ => setField n (some (.list vs)) fs

/-- What a known field's decoder does with a record: stores it (the new fields, the rest), routes
it to the unknown fields (`errUnknown`), or fails. -/
inductive Step where
  | ok (fs : List (Nat × Value)) (rest : List Byte)
  | unknown
  | err

/-- A known field's record (`f`, wire type `wt`, the bytes after the tag), into the message's
fields `fs`; `sub` decodes a nested message's bytes into a message value (one level deeper). -/
def decKnown (sub : Msg → List Byte → Value → Option Value) (D : Desc) (md : Msg) (f : Field)
    (wt : Nat) (bs : List Byte) (fs : List (Nat × Value)) : Step :=
  match f.kind with
  | .message name =>
    if wt != 2 then .unknown
    else match readBytes bs, D.lookup name with
      | some (payload, r), some smd =>
        if f.card == .repeated then
          match sub smd payload Value.empty with
          | some v => .ok (appendRep f.num [v] fs) r
          | none => .err
        else
          let cur := match getField fs f.num with
            | some v@(.msg _ _) => v
            | _ => Value.empty
          match sub smd payload cur with
          | some v => .ok (storeSingular md f v fs) r
          | none => .err
      | _, _ => .err
  | .string | .bytes =>
    if wt != 2 then .unknown
    else match readBytes bs with
      | some (v, r) =>
        if f.kind == .string && f.utf8 && !validUTF8 v then .err
        else if f.card == .repeated then .ok (appendRep f.num [.bytes v] fs) r
        else .ok (storeSingular md f (.bytes v) fs) r
      | none => .err
  | k =>
    if wt = k.wireType then
      match readScalar k bs with
      | some (v, r) =>
        if f.card == .repeated then .ok (appendRep f.num [v] fs) r
        else .ok (storeSingular md f v fs) r
      | none => .err
    else if wt == 2 && f.card == .repeated then
      match readBytes bs with
      | some (payload, r) =>
        match readPacked k (payload.length + 1) payload with
        | some vs => .ok (appendRep f.num vs fs) r
        | none => .err
      | none => .err
    else .unknown

/-- The records of a message's bytes, decoded into the message value `acc` (`fuel` exceeds the
bytes' length). -/
def decLoop (sub : Msg → List Byte → Value → Option Value) (D : Desc) (md : Msg) :
    Nat → List Byte → List (Nat × Value) → List Byte → Option Value
  | _, [], fs, unk => some (.msg fs unk)
  | 0, _, _, _ => none
  | fuel + 1, bs, fs, unk =>
    match readVarint bs with
    | none => none
    | some (t, r) =>
      let num := t / 8
      let wt := t % 8
      if num == 0 || num > 2 ^ 29 - 1 || wt == 4 then none
      else
        let st := match md.field? num with
          | none => Step.unknown
          | some f => decKnown sub D md f wt r fs
        match st with
        | .ok fs' r' => decLoop sub D md fuel r' fs' unk
        | .unknown =>
          match skipValue (r.length + 1) 10001 num wt r with
          | some r' => decLoop sub D md fuel r' fs (unk ++ tag num wt ++ r.take (r.length - r'.length))
          | none => none
        | .err => none

/-- A message's bytes decoded into `acc`, with `d` levels of nesting left (this one included). -/
def decMsg (D : Desc) : Nat → Msg → List Byte → Value → Option Value
  | 0, _, _, _ => none
  | d + 1, md, bs, acc =>
    match acc with
    | .msg fs unk => decLoop (decMsg D d) D md (bs.length + 1) bs fs unk
    | _ => none

/-- **`proto.Unmarshal`** of `bs` as a message of type `name` (`none`: Unmarshal's error). -/
def decode (D : Desc) (name : String) (bs : List Byte) : Option Value := do
  let md ← D.lookup name
  decMsg D 10000 md bs Value.empty

/-! ## Notation for tests -/

def hexDigit (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else 0

def hexBytes : List Char → List Byte
  | a :: b :: rest => BitVec.ofNat 8 (16 * hexDigit a + hexDigit b) :: hexBytes rest
  | _ => []

/-- Bytes from lowercase hex. -/
def hex (s : String) : List Byte := hexBytes s.toList

/-- Lowercase hex of bytes (`hex`'s inverse). -/
def toHex (bs : List Byte) : String :=
  let d (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
  String.ofList (bs.flatMap fun b => [d (b.toNat / 16), d (b.toNat % 16)])

/-! ## Examples -/

/-- A small descriptor for the examples below (raftpb's `Entry` and `ConfState`, a proto3
message with a oneof). -/
def exDesc : Desc :=
  [ { name := "raftpb.Entry", fields :=
      [ { name := "Term", num := 2, kind := .uint64, card := .explicit },
        { name := "Index", num := 3, kind := .uint64, card := .explicit },
        { name := "Type", num := 1, kind := .enum, card := .explicit },
        { name := "Data", num := 4, kind := .bytes, card := .explicit } ] },
    { name := "raftpb.ConfState", fields :=
      [ { name := "voters", num := 1, kind := .uint64, card := .repeated },
        { name := "auto_leave", num := 5, kind := .bool, card := .explicit } ] },
    { name := "ex.O", fields :=
      [ { name := "a", num := 1, kind := .int32, card := .implicit },
        { name := "y", num := 5, kind := .string, card := .explicit, oneof := some "o", utf8 := true },
        { name := "b", num := 3, kind := .sint64, card := .implicit },
        { name := "x", num := 2, kind := .int32, card := .explicit, oneof := some "o" },
        { name := "p", num := 4, kind := .fixed32, card := .repeated, packed := true } ] } ]

-- Entry{Term: 1, Index: 2, Type: 0, Data: []byte{}}: explicit presence writes the zeros.
example : encode exDesc "raftpb.Entry"
    (.msg [(1, .int 0), (2, .int 1), (3, .int 2), (4, .bytes [])] []) = some (hex "0800100118022200") := by
  rfl

-- A negative int32 is sign-extended: 10 bytes.
example : encode exDesc "ex.O" (.msg [(1, .int (-1))] []) = some (hex "08ffffffffffffffffff01") := by
  rfl

-- ConfState's voters, unpacked; the decoder takes them packed too.
example : encode exDesc "raftpb.ConfState" (.msg [(1, .list [.int 1, .int 2])] []) =
    some (hex "08010802") := by rfl
#guard decode exDesc "raftpb.ConfState" (hex "0a020102") ==
    some (.msg [(1, .list [.int 1, .int 2])] [])

-- The oneof member y (5) is written after every field outside the oneof (b, 3).
example : encode exDesc "ex.O" (.msg [(3, .int (-1)), (5, .bytes (hex "61"))] []) =
    some (hex "18012a0161") := by rfl
-- So is the oneof member x (2): after b (3), though its number is smaller.
example : encode exDesc "ex.O" (.msg [(2, .int 7), (3, .int 1)] []) = some (hex "18021007") := by
  rfl

-- An unknown field (number 9) is kept, its tag re-encoded minimally; a non-minimal tag is read.
#guard decode exDesc "raftpb.ConfState" (hex "c80005") == some (.msg [] (hex "4805"))

-- The last occurrence of a singular field wins; a oneof member clears the other.
#guard decode exDesc "ex.O" (hex "100118022a0162") ==
    some (.msg [(3, .int 1), (5, .bytes (hex "62"))] [])

-- Invalid UTF-8 in a validated string: both directions fail.
example : encode exDesc "ex.O" (.msg [(5, .bytes (hex "ff"))] []) = none := by rfl
#guard decode exDesc "ex.O" (hex "2a01ff") == none

end PbWire
end EtcdGrove
end Perennial
