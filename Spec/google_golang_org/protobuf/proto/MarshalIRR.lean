/-
`proto.Marshal` of an `*etcdserverpb.InternalRaftRequest`: the trust boundary
(`google.golang.org/protobuf` is names-only; the decoding `apply.irrDecode` is opaque,
`apply/InvRequest.lean`). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path"). A second statement about `proto.Marshal`, for
another message type than mvcc's `KeyValue` (`Marshal.lean`): kept apart because this one names
the apply package's request model, which mvcc's proofs must not import (as `pbutil.
MustUnmarshalMessage`'s cases, but in a file of its own); the two have disjoint premises.

**What it says** (`processInternalRaftRequestOnce` marshals the request it proposes): either an
error (protobuf-go rejects a string field that is not valid UTF-8, a `Header.Username` from the
auth store; protobuf-go's errors are pointer errors, `*prefixError` with an `Is` method comparing
the target with its sentinel, `*wrapError` with `Unwrap` too, and `Error()` returns: so in an error
tree for every target, a safe map key, with a message, `applyErrIs`; 2026-10-12, the request
path's unit 3a, for `togRPCError`), or a fresh slice of bytes that decode (`irrDecode`) to the request: the same id and
header, the same kind (`dispatchKind`), and the same model altogether when no range end of its
KV requests is `[0]` (`irrNoZeroEnd`). The exception is the model's, not the encoding's: a
request's range end denotes `[0]` both for the bytes `"\x00"` and for an empty non-nil slice
(`txn.rangeEndOf`, mvcc's reading after `mkGteRange`), and the wire turns an empty slice into
`nil` (the key alone), so for such a request the decoded model may have `[]` where it had `[0]`.
A request decoded from the wire (the gRPC server's) has no empty non-nil slice, so its encoding
decodes to it; that is the premise unit 2 will state of the handlers' requests.

The size caches protobuf-go stores in the messages (atomically) are outside the model:
`internalRaftRequestIs` and the KV requests' predicates do not own them.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest
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

/-- **What the encoding of `rq` decodes to**: `rq'` with the same id, header and kind, and
`rq` itself when no range end is `[0]`. -/
def irrWireOf (rq rq' : apply.IRRModel) : Prop :=
  rq'.id = rq.id ∧ rq'.header = rq.header ∧ apply.dispatchKind rq' = apply.dispatchKind rq ∧
    (irrNoZeroEnd rq → rq' = rq)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- See the file header. -/
abbrev proto.MarshalIRR.spec : Prop :=
  ∀ (p : Loc) (rq : apply.IRRModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      apply.internalRaftRequestIs p rq }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.InternalRaftRequest.ty) #p)))
  {{ (d : GoSlice) (err : GoInterface), RET (PairV #d #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (bs : List w8) (rq' : apply.IRRModel),
        d ↦* bs ∗ ownSliceCap w8 d (DFrac.own 1) ∗
        ⌜apply.irrDecode bs = some rq' ∧ irrWireOf rq rq'⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err) }}

end spec

end EtcdGrove
end Perennial
