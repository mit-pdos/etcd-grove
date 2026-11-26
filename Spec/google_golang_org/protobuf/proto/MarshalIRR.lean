/-
`proto.Marshal` of an `*etcdserverpb.InternalRaftRequest`: the trust boundary
(`google.golang.org/protobuf` is names-only; the decoding `apply.irrDecode` is opaque,
`apply/InvRequest.lean`). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path"). A second statement about `proto.Marshal`, for
another message type than mvcc's `KeyValue` (`Marshal.lean`): kept apart because this one names
the apply package's request model, which mvcc's proofs must not import (as `pbutil.
MustUnmarshalMessage`'s cases, but in a file of its own); the two have disjoint premises.

**What it says** (`processInternalRaftRequestOnce` marshals the request it proposes; of a request
within protobuf-go's recursion limit, "The depth" below): either an
error (protobuf-go rejects a proto3 string field that is not valid UTF-8, e.g. a `Header.Username`
from the auth store, `applyErrIs`; 2026-10-12, the request path's unit 3a, for `togRPCError`), or a
fresh slice of bytes that decode (`irrDecode`) to the request: the same id and
header, the same kind (`dispatchKind`), and the same model altogether when no range end of its
KV requests is `[0]` (`irrNoZeroEnd`). The exception is the model's, not the encoding's: a
request's range end denotes `[0]` both for the bytes `"\x00"` and for an empty non-nil slice
(`txn.rangeEndOf`, mvcc's reading after `mkGteRange`), and the wire turns an empty slice into
`nil` (the key alone), so for such a request the decoded model may have `[]` where it had `[0]`.
A request decoded from the wire (the gRPC server's) has no empty non-nil slice, so its encoding
decodes to it; that is the premise unit 2 will state of the handlers' requests.

**The error arm is false of Go (open; mapkeys, 2026-11-26, the map-key audit's F1,
`notes/axiom-review/errkeys-proto-renewhttp.md`).** Invalid UTF-8 is the only failure this call
has. At the pin (protobuf-go v1.36.12) the generated messages' fast path returns the struct value
`impl.errInvalidUTF8{}` (`internal/impl/codec_gen.go:5041-5049`, `codec_field.go:17-21`); the
reflective path returns `errors.InvalidUTF8(name)`, a `*prefixError`. `proto.Marshal` passes either
on unwrapped (`proto/encode.go:105-116, 198-204`). Both have `Unwrap() error`, so neither is a leaf
error (`statusErrOk`, in `applyErrIs`'s `srvErrOk`). The struct is not a key of `togRPCError`'s map
either (`errKeyOk`: `nil`, pointers, `deadlineExceededError{}`, `InvalidCostError`). The docstring
used to say every protobuf error is a pointer, which is wrong. Real etcd never reaches this arm:
gRPC's decoding validates every proto3 string, and the auth store's usernames come from such strings.
Neither fix is in reach yet. One is a UTF-8 premise, as `MarshalUser.lean:49` has. The other is
widening `errKeyOk` (after translating `errInvalidUTF8` as the field-less struct it is: it is
names-only, so its `==` is opaque) together with `srvErrOk` to non-leaf errors. The premise needs
`apply.internalRaftRequestIs` to carry the strings' validity from every proposer, and the
widening needs grpc's `status.FromError` spec to walk `Unwrap`.

**The keys and values are no longer than the encoding** (2026-10-30, `notes/keylen.md`, for the
keys; 2026-10-31, `notes/vallen.md`, extended to the values; the user's approvals,
`notes/decisions.md`, "The key-length law" and "The value-length law"): every key and every value
the decoded request puts (`irrPutsLe`: its `Put`'s key and value, its transaction's puts' at any
depth) is at most `bs.length` bytes. protobuf encodes a set `bytes` field as its tag, its length
and then all its bytes, and `proto.Marshal` emits every set field of every nested message, so each
decoded key and value is a contiguous region of `bs`. Stated over the decoded `rq'` (what the apply
side applies), not `rq`.

**The depth** (2026-10-31, `notes/irr-depth.md`, the axiom review `axiom/txn-nested-wire`'s
attack 9, `issues/etcd-txn-nested-depth-apply-panic.md`; the user's approval, `notes/decisions.md`,
"A depth premise for `proto.MarshalIRR`"): the claim is made of a request within protobuf-go's
recursion limit only (`apply.irrDepthOk`, the premise). At the pin (protobuf-go v1.36.12),
`proto.Unmarshal` (`pbutil.MustUnmarshalMessage`'s) decodes with `RecursionLimit:
protowire.DefaultRecursionLimit` = 10000 (`proto/decode.go:61-63`, `encoding/protowire/wire.go:28`),
which `MessageInfo.unmarshalPointer` decrements on entry to every message, the top one included,
failing below 0 (`internal/impl/decode.go:105`); a nested message field (singular, repeated, a
oneof's member) decodes with the decremented count. So the bytes decode iff every message is at
most 10000 levels deep. Scalar and `bytes` fields and a oneof wrapper (`RequestOp_RequestTxn`, a
Go wrapper, no message) cost no level; unknown fields are skipped against a fresh limit
(`protowire.ConsumeFieldValue`). The only recursion of the request is its transaction
(`TxnRequest`/`RequestOp`): every other field is a non-recursive message at most two levels deep
(`AuthUserAddRequest` with its `UserAddOptions`, ...), so the request is at most 3 deep without a
transaction, and with one its transaction's depth plus one (`TxnModel.msgDepth`;
`internalRaftRequestIs` and `txnRequestIsW` own every field of the messages, so the model's tree
has the heap's shape). Marshalling has no depth check: the code also returns bytes for a deeper
request (up to Go's stack), which then do not decode; this statement claims nothing of it (no
caller has a use for such bytes).

The size caches protobuf-go stores in the messages (atomically) are outside the model:
`internalRaftRequestIs` and the KV requests' predicates do not own them; except a user addition's
`Options` and a permission grant's `Permission`, whose caches are in invariants (`auth.userOptsIs`,
`auth.ownPermW`; auth-schema-srv A3), which this call stores.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.IrrDepth
public import GeneratedProof.google_golang_org.protobuf.proto

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-! ## The requests whose model the wire keeps (pure) -/

mutual
/-- No range end of the operation (a get's, a delete's, a nested transaction's comparisons' and
operations') is `[0]`. -/
def txnOpNoZeroEnd : TxnOp → Prop
  | .get o => o.base.rangeEnd ≠ [W8 0]
  | .delete o => o.base.rangeEnd ≠ [W8 0]
  | .txn cs ts es => (∀ c ∈ cs, c.rangeEnd ≠ [W8 0]) ∧ txnOpsNoZeroEnd ts ∧ txnOpsNoZeroEnd es
  | _ => True

def txnOpsNoZeroEnd : List TxnOp → Prop
  | [] => True
  | op :: ops => txnOpNoZeroEnd op ∧ txnOpsNoZeroEnd ops
end

/-- **No range end of the request's KV requests is `[0]`** (see the file header). -/
def irrNoZeroEnd (rq : apply.IRRModel) : Prop :=
  (∀ o, rq.range = some o → o.base.rangeEnd ≠ [W8 0]) ∧
  (∀ o, rq.deleteRange = some o → o.base.rangeEnd ≠ [W8 0]) ∧
  (∀ t, rq.txn = some t →
    (∀ c ∈ t.cmps, c.rangeEnd ≠ [W8 0]) ∧ txnOpsNoZeroEnd t.thenOps ∧ txnOpsNoZeroEnd t.elseOps)

/-- The request `rq` with the header `h` (`processInternalRaftRequestOnce` sets `r.Header`). -/
def apply.withHeader (rq : apply.IRRModel) (h : apply.HeaderModel) : apply.IRRModel :=
  { rq with header := some h }

@[simp] theorem apply.withHeader_txn (rq : apply.IRRModel) (h : apply.HeaderModel) :
    (apply.withHeader rq h).txn = rq.txn := rfl

@[simp] theorem apply.withHeader_txnW (rq : apply.IRRModel) (h : apply.HeaderModel) :
    (apply.withHeader rq h).txnW = rq.txnW := rfl

@[simp] theorem apply.irrDepthOk_withHeader (rq : apply.IRRModel) (h : apply.HeaderModel) :
    apply.irrDepthOk (apply.withHeader rq h) ↔ apply.irrDepthOk rq := Iff.rfl

/-- **What the encoding of `rq` decodes to**: `rq'` with the same id, header and kind, and
`rq` itself when no range end is `[0]`. -/
def irrWireOf (rq rq' : apply.IRRModel) : Prop :=
  rq'.id = rq.id ∧ rq'.header = rq.header ∧ apply.dispatchKind rq' = apply.dispatchKind rq ∧
    (irrNoZeroEnd rq → rq' = rq)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- See the file header.
(errors-is-deadline, 2026-11-23) Since then the post's `applyErrIs` also says that the error tree's
errors of type `context.deadlineExceededError` hold `deadlineExceededError{}` (`deTyped`). Go's
typing makes this true of every Go error: `deadlineExceededError` is a field-less struct type, whose
only value is `deadlineExceededError{}`. The model does not type interface values, and `togRPCError`
compares the error with `context.DeadlineExceeded`, so the fact is stated. It was accepted by the
coordinator under the user's approval of the same typing class (2026-11-23), and review was
requested on #31. -/
abbrev proto.MarshalIRR.spec : Prop :=
  ∀ (p : Loc) (rq : apply.IRRModel),
  -- (2026-10-31, `axiom/txn-nested-wire`'s attack 9) the request within protobuf-go's recursion
  -- limit (`apply.irrDepthOk`): a deeper one is encoded but does not decode
  apply.irrDepthOk rq →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      apply.internalRaftRequestIs p rq }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.InternalRaftRequest.ty) #p)))
  {{ (d : GoSlice) (err : GoInterface), RET (PairV #d #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (bs : List w8) (rq' : apply.IRRModel),
        d ↦* bs ∗ ownSliceCap w8 d (DFrac.own 1) ∗
        ⌜apply.irrDecode bs = some rq' ∧ irrWireOf rq rq' ∧ (rq.header ≠ none → bs ≠ []) ∧
          apply.irrPutsLe bs.length rq'⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err) }}

end spec

end EtcdGrove
end Perennial
