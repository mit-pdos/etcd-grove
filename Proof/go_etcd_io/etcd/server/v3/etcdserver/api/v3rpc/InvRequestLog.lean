/-
The request log's view of a request (etcd#21764, pr-verify): what `logLightweightRequestInfo`
reads of the request `req` the log interceptor passes it (`any`, the decoded request), per its
type switch. Lean-first (no Rocq counterpart).

`LwReq` names the switch's cases: a non-nil request of one of the six types the switch logs
fields of, or `other` (nil, or a value of any other dynamic type, which only gets the method,
the remote and the duration). `lwReqIs req u` holds the fields read, read-only: a range's and a
delete's `Key` and `RangeEnd`, a put's `Key` (never its value), a transaction's comparisons
(each not nil, its `Key` and `RangeEnd` as bytes, since the log converts them to strings), a
lease grant's `TTL` and `ID`, a revoke's `ID`. A decoded request is all of this: protobuf-go
never decodes a nil message, and decoding allocates every repeated message element.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-- The cases of `logLightweightRequestInfo`'s type switch, with the request's pointer. -/
inductive LwReq where
  | range (r : Loc)
  | put (r : Loc)
  | del (r : Loc)
  | txn (r : Loc)
  | grant (r : Loc)
  | revoke (r : Loc)
  | other

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The six request types the switch names, as the dynamic types of `req`. -/
def lwTypes : List go.GoType :=
  [go.GoType.PointerType etcdserverpb.RangeRequest.ty,
   go.GoType.PointerType etcdserverpb.PutRequest.ty,
   go.GoType.PointerType etcdserverpb.DeleteRangeRequest.ty,
   go.GoType.PointerType etcdserverpb.TxnRequest.ty,
   go.GoType.PointerType etcdserverpb.LeaseGrantRequest.ty,
   go.GoType.PointerType etcdserverpb.LeaseRevokeRequest.ty]

/-- **A comparison as the log reads it** (persistent): not nil, its `Key` and `RangeEnd` slices
read-only, with their bytes. -/
def lwCmpIs (c : Loc) : IProp GF :=
  iprop(□ (⌜c ≠ null⌝ ∗ ∃ (ksl esl : GoSlice) (k e : GoString),
    structFieldRef etcdserverpb.Compare go!"Key" c ↦□ ksl ∗ ksl ↦*□ k ∗
    structFieldRef etcdserverpb.Compare go!"RangeEnd" c ↦□ esl ∗ esl ↦*□ e))

instance lwCmpIs_persistent (c : Loc) : Persistent (lwCmpIs (GF := GF) c) := by
  unfold lwCmpIs; infer_instance

/-- **The request `req` as `logLightweightRequestInfo` reads it**, in the switch's case `u`
(persistent; see the file header). -/
def lwReqIs (req : GoInterface) : LwReq → IProp GF
  | .range r => iprop(⌜req = interface.mkOk (go.GoType.PointerType etcdserverpb.RangeRequest.ty) #r ∧
      r ≠ null⌝ ∗ □ ∃ (ksl esl : GoSlice),
      structFieldRef etcdserverpb.RangeRequest go!"Key" r ↦□ ksl ∗
      structFieldRef etcdserverpb.RangeRequest go!"RangeEnd" r ↦□ esl)
  | .put r => iprop(⌜req = interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #r ∧
      r ≠ null⌝ ∗ □ ∃ (ksl : GoSlice),
      structFieldRef etcdserverpb.PutRequest go!"Key" r ↦□ ksl)
  | .del r => iprop(⌜req = interface.mkOk (go.GoType.PointerType etcdserverpb.DeleteRangeRequest.ty) #r ∧
      r ≠ null⌝ ∗ □ ∃ (ksl esl : GoSlice),
      structFieldRef etcdserverpb.DeleteRangeRequest go!"Key" r ↦□ ksl ∗
      structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" r ↦□ esl)
  | .txn r => iprop(⌜req = interface.mkOk (go.GoType.PointerType etcdserverpb.TxnRequest.ty) #r ∧
      r ≠ null⌝ ∗ □ ∃ (csl : GoSlice) (cps : List Loc),
      structFieldRef etcdserverpb.TxnRequest go!"Compare" r ↦□ csl ∗ csl ↦*□ cps ∗
      ∀ (i : Nat) (c : Loc), ⌜cps[i]? = some c⌝ -∗ lwCmpIs c)
  | .grant r => iprop(⌜req = interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseGrantRequest.ty) #r ∧
      r ≠ null⌝ ∗ □ ∃ (ttl id : w64),
      structFieldRef etcdserverpb.LeaseGrantRequest go!"TTL" r ↦□ ttl ∗
      structFieldRef etcdserverpb.LeaseGrantRequest go!"ID" r ↦□ id)
  | .revoke r => iprop(⌜req = interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseRevokeRequest.ty) #r ∧
      r ≠ null⌝ ∗ □ ∃ (id : w64),
      structFieldRef etcdserverpb.LeaseRevokeRequest go!"ID" r ↦□ id)
  | .other => iprop(⌜∀ ii : GoInterfaceOk, req = GoInterface.ok ii → ii.ty ∉ lwTypes⌝)

instance lwReqIs_persistent (req : GoInterface) (u : LwReq) :
    Persistent (lwReqIs (GF := GF) req u) := by
  cases u <;> unfold lwReqIs <;> infer_instance

end defs

end v3rpc
end EtcdGrove
end Perennial
