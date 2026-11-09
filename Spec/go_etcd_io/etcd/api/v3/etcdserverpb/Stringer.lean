/-
# The request messages as `fmt.Stringer`s (verify round, A6 completeness F6)

etcd's loggers take a request as a `fmt.Stringer` (`txn.WarnOfExpensive*`): a message pointer
(protobuf's `String()`, `protoimpl.X.MessageStringOf`), `NewLoggableTxnRequest`'s wrapper, or the
apply's `*InternalRaftStringer`. `String()` reads the message, so a stringer holds what it reads:
`stringerAt s` (**not persistent**), given back by every call of `String()`. A share of a message is
one (`stringerAt_msg`, the share given back when the stringer is); a read-only message gives a
persistent one (`stringerAt_discard`). Re-review (R-A6, second tier): each law takes the depth bound
`depth c < depthMax` (protobuf's text marshaling recurses per level, as `Marshal` does).
Recheck (RR4), where callers get it: a non-transaction request from `holds_depth` (at most `3`); a
transaction from `holds_depth_txn` (`depth c ≤ txnMsgDepth t`) and the caller's bound on
`txnMsgDepth t` (the gRPC checks, `V3rpc.txnCheck_checked`; `t.readonly`: at most `3`); a decoded
message from `Proto.Unmarshal.spec`'s success case (the apply's entry: `Apply.irrMsgAt_msg`).

Replaces txn's provisional persistent `Txn.stringerOk` ("3h's", `txn/Api.lean`), which no law could
introduce soundly: the request path's `Range` logs a request its caller holds only a fraction of and
gets back (`EtcdServer.Range`'s deferred `WarnOfExpensiveReadOnlyRangeRequest`), so a persistent "its
`String()` returns" would outlive the share that makes the read safe (a later writer races it).
Requested of apply-txn: `stringerOk` := `EtcdServerPb.stringerAt`, given back by the `Warn*` specs.

Intended realization: `∃ t p dq c, s = msgVal t p ∗ msgAt t p dq c` (a message), or a
`txnRequestStringer` holding such a share of its request (`NewLoggableTxnRequest`).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api
public import Perennial.Code.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI
open go_etcd_io.etcd.api.v3

/-- **`s` is a `fmt.Stringer` whose `String()` returns** (holding what it reads; not persistent). -/
opaque stringerAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : GoInterface) : IProp GF := iprop(True)

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`s.String()`** returns some string, the stringer given back. -/
def stringerAt_call.spec : Prop := ∀ (s : GoInterface),
  {{ stringerAt (GF := GF) s }}
    (App (Val (s @!! fmt.Stringer.ty @!! go!"String")) (Val #()))
  {{ (str : GoString), RET #str; stringerAt s }}

/-- **A share of a message is a stringer** (protobuf's `String()` reads it), the share given back
with the stringer. -/
def stringerAt_msg.spec : Prop := ∀ (t : go.GoType) (p : Loc) (dq : DFrac) (c : Proto.Content),
  Proto.msgAt (GF := GF) t p dq c ∗ ⌜Proto.depth c < Proto.depthMax⌝ ⊢
    stringerAt (Proto.msgVal t p) ∗ (stringerAt (Proto.msgVal t p) -∗ Proto.msgAt t p dq c)

/-- A read-only message is a stringer for good. -/
def stringerAt_discard.spec : Prop := ∀ (t : go.GoType) (p : Loc) (c : Proto.Content),
  Proto.msgAt (GF := GF) t p DFrac.discard c ∗ ⌜Proto.depth c < Proto.depthMax⌝ ⊢ □ stringerAt (Proto.msgVal t p)

/-- **The apply's `&pb.InternalRaftStringer{Request: r}` over a read-only request is a stringer for
good** (verify-round, apply-txn's request: the dispatch's deferred `WarnOfExpensiveRequest` and
`WarnOfFailedRequest`, `uber_applier.go:99,101`). Its `String()` reads its `Request` field and the
request message (protobuf's text of it, with the password fields of the auth requests redacted,
`raft_internal_stringer.go`); both read-only here, so the stringer is persistent. The wrapper's
field is persisted by its allocator (Go's `↦` persist law). -/
def stringerAt_irr.spec : Prop := ∀ (w r : Loc) (c : Proto.Content),
  (w.[etcdserverpb.InternalRaftStringer, go!"Request"] ↦□ r : IProp GF) ∗
    Proto.msgAt etcdserverpb.InternalRaftRequest.ty r DFrac.discard c ∗ ⌜Proto.depth c < Proto.depthMax⌝ ⊢
  □ stringerAt (interface.mkOk (go.GoType.PointerType etcdserverpb.InternalRaftStringer.ty) #w)

end laws

end EtcdServerPb
end EtcdGrove
end Perennial
