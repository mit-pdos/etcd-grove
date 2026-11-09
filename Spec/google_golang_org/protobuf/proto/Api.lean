/-
# protobuf-go's `proto` package: the trust boundary (batch 2a)

protobuf-go (`google.golang.org/protobuf/proto`, v1.36.12 at the pin) is not translated: its specs
are **assumed**, each one true of protobuf-go's code at the pin (the file of each says why). They
are stated over one vocabulary, fixed here, so that no statement is quantified over a model a
caller builds (the soundness bug of the old `pbEnc_ok`/`PbType` and grpc's `ProtoMsg`, whose wire
model was a record any caller could fill: `specs-ref/notes/pbenc-ok-inconsistent.md`,
`grpc-msg-models.md`), and no encoding is keyed by an address (`per-type-blockers.md` (b)).

## Vocabulary

* `Content` (opaque type): **a message's protobuf content**: every field of the message and of
  the messages it reaches, the unknown fields included, up to `proto.Equal`. It is a value, not
  an address: two messages at different addresses, in different heaps, hold the same content when
  `proto.Equal` says so. What a message *means* (a `RangeRequest`'s model, a raft `Entry`'s) is the
  message's own package's: each message predicate of the other batches (W0's `rangeReqOwn`, 3h's,
  R1's `msgPts`) is related to `msgAt` by a law of its owner, `xOwn p dq m ⊣⊢ ∃ c, msgAt X.ty p dq c
  ∗ ⌜xModels c m⌝`, with `xModels` a pure relation that is a function of the content
  (`req/go_etcd_io_etcd_api_v3_etcdserverpb.md`, "from 2a").
* `msgAt t p dq c` (opaque; timeless; persistent at `DFrac.discard`): **the message of Go type `*t`
  at `p` holds `c`**: the fraction `dq` of its fields and of everything it reaches (submessages,
  byte slices, slices of submessages, oneof wrappers); `p ≠ null`. Its `sizeCache` field, which
  `Size` and `Marshal` write, is inside it, written atomically (protobuf-go stores it with
  `atomic.StoreInt32`), so concurrent readers holding fractions may marshal the same message.
  Intended realization: per Go type, the owner's field-by-field predicate; there is no single
  generic definition, which is why it is opaque here and each owner proves the relation law.
* `encSize c`: **`proto.Size` of the content**, each reference counted (a submessage held `n`
  times counts `n` times); `depth c`: its nesting depth (a message without submessages: `1`).
* `marshalOk c` (opaque `Prop`): `proto.Marshal` accepts the content: every proto3 `string` field
  holds valid UTF-8, every proto2 required field is set. etcd's and raft's messages have no
  required fields; their `string` fields (user, role and member names, URLs, passwords) are what a
  client chose. The owners state which of their messages always marshal (raft's entries, a
  `ConfChange` built by a client: only `bytes` fields).
* `encodes t c bs` (opaque `Prop`): `bs` is a wire encoding of the content `c` of a `*t` (decoding
  is a function: `encodes_fun`).
* `noMaps t`, `marshalOut t c`: `Marshal` is deterministic for a type without maps (3h's request:
  every founder of a raft cluster appends the same bootstrap bytes); `zero`: a fresh message's
  content (`zero_facts`).
* `mergeDst t p c` (round 1, 3h's review F1): a destination `Merge` may write in place.
* `merge c c'`: `proto.Merge`'s result (repeated fields appended, set scalars and submessages
  taken from `c'`); what it is for a given message type is that type's owner's law.

## The limits (why some specs take `Content.fits`)

* protobuf-go's marshaling allocates `proto.Size` bytes before checking anything
  (`proto/encode.go`), and Go's `make` panics above `2 ^ 48` bytes on linux/amd64 (`maxAlloc`);
  a message whose submessages are shared can be that large with little memory
  (`issues/grpc-codec-alloc-before-size-check.md`). So `Marshal` (and grpc's send, which calls it)
  takes `encSize c < marshalMax`.
* Marshaling, sizing, cloning and comparing recurse once per level of nesting, on the goroutine's
  stack (at most 1 GB: a fatal error beyond it, about a million levels); unmarshaling refuses more
  than `10000` levels (`protowire`'s `RecursionLimit`, an error, not a panic). The specs take
  `depth c < depthMax` (`10000`): far below the stack's limit, and exactly what unmarshaling
  accepts, so a message so bounded round-trips.

`Content.fits c` is both. A message of a non-recursive type (every raft message, every etcd
message but the transaction's `TxnRequest`/`RequestOp`/`TxnResponse`/`ResponseOp`) fits whenever
its byte slices are distinct allocations (the owners' laws); the recursive ones are bounded where
they are built (the client) or accepted (the server's `checkTxnRequest` and `--max-txn-ops`).

## Laws

`msgAt_timeless`, `msgAt_discard_persistent`, `msgAt_ne_null`, `msgAt_agree`, `msgAt_persist`,
`encodes_fun`.
-/
module

public import GeneratedProof.google_golang_org.protobuf.proto
public import Spec.PkgInit.google_golang_org.protobuf.proto

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Proto

open Iris Iris.BI

/-- **A message's protobuf content** (see the header): opaque. -/
opaque ContentT : { T : Type // Nonempty T } := ⟨Unit, ⟨()⟩⟩

def Content : Type := ContentT.1

instance : Nonempty Content := ContentT.2

/-- `proto.Size` of the content (each reference counted). -/
opaque encSize : Content → Nat

/-- The nesting depth of the content. -/
opaque depth : Content → Nat

/-- protobuf-go's decoding recursion limit (`protowire.DefaultRecursionLimit`). -/
def depthMax : Nat := 10000

/-- Go's largest allocation on linux/amd64 (`maxAlloc`): marshaling allocates the size first. -/
def marshalMax : Nat := 2 ^ 48

/-- **The content can be marshaled without a panic** (and unmarshaled back). -/
def Content.fits (c : Content) : Prop := encSize c < marshalMax ∧ depth c < depthMax

/-- `proto.Marshal` accepts the content (valid UTF-8 strings, required fields set). -/
opaque marshalOk : Content → Prop

/-- `bs` is a wire encoding of the content `c` of a `*t`. -/
opaque encodes (t : go.GoType) (c : Content) (bs : List w8) : Prop

/-- `proto.Merge`'s result. -/
opaque merge (_c c' : Content) : Content := c'

/-- **The message type `*t` has no map field** (opaque; true of every etcd and raft message):
`Marshal`'s output is then a function of the content (fields in field-number order,
`orderedCoderFields`; unknown fields as stored; only map iteration is randomized). -/
opaque noMaps (t : go.GoType) : Prop

/-- **`Marshal`'s output** for a type without map fields (opaque function of the content). -/
opaque marshalOut (t : go.GoType) (c : Content) : List w8

/-- **The zero content** (a `new(T)`'s, of any type: no field set). -/
opaque zero : Content

def zero_facts.spec : Prop := ∀ t, encodes t zero [] ∧ depth zero = 1 ∧ marshalOk zero

def marshalOut_encodes.spec : Prop := ∀ t c, noMaps t → marshalOk c → encodes t c (marshalOut t c)

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-- **The message of Go type `*t` at `p` holds `c`** (fraction `dq` of it and what it reaches). -/
opaque msgAt (t : go.GoType) (p : Loc) (dq : DFrac) (c : Content) : IProp GF := iprop(True)

/-- The `proto.Message` interface value of the message `*t` at `p`. -/
def msgVal (t : go.GoType) (p : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType t) #p

def msgAt_timeless.spec : Prop := ∀ t p dq c, Timeless (msgAt (GF := GF) t p dq c)

def msgAt_discard_persistent.spec : Prop := ∀ t p c, Persistent (msgAt (GF := GF) t p DFrac.discard c)

def msgAt_ne_null.spec : Prop := ∀ t p dq c, msgAt (GF := GF) t p dq c ⊢ ⌜p ≠ null⌝

/-- Two holdings of one message agree on its content. -/
def msgAt_agree.spec : Prop := ∀ t p dq dq' c c',
  msgAt (GF := GF) t p dq c ∗ msgAt t p dq' c' ⊢ ⌜c = c'⌝

/-- **A message `Merge` may write into** (exclusive; per type, its owner's): the message at `p`
holds `c`, owned, with its repeated fields' slices owned **to their capacity** and its set
submessages owned writable (protobuf-go merges in place: it appends to a destination's repeated
field, writing its spare capacity, and merges into a set submessage,
`internal/impl/merge.go:159-184`). `msgAt t p (own 1) c` alone does not give it: a message may hold
its submessages read-only and a slice without its capacity (a raft `MsgApp`'s entries, a sub-slice
of the leader's log). The owners' laws introduce it (3h: a fresh message, `mergeDst_zero`; a
`RangeResponse` whose `Kvs` were appended by `Merge` itself). -/
opaque mergeDst (t : go.GoType) (p : Loc) (c : Content) : IProp GF := iprop(True)

/-- A fresh message (no field set) may be merged into. -/
def mergeDst_zero.spec : Prop := ∀ t p, msgAt (GF := GF) t p (DFrac.own 1) zero ⊢ mergeDst t p zero

/-- A merge destination is an owned message. -/
def mergeDst_msgAt.spec : Prop := ∀ t p c, mergeDst (GF := GF) t p c ⊢ msgAt t p (DFrac.own 1) c

/-- An owned message may be made read-only for good. -/
def msgAt_persist.spec : Prop := ∀ t p c,
  msgAt (GF := GF) t p (DFrac.own 1) c ⊢ |==> msgAt t p DFrac.discard c

end res

/-- Decoding is a function: bytes encode at most one content of a type. -/
def encodes_fun.spec : Prop := ∀ t c c' bs, encodes t c bs → encodes t c' bs → c = c'

end Proto
end EtcdGrove
end Perennial
