/-
**The client's leases over gRPC** (item 1, branch `lease-client`, 2026-10-18): the vocabulary of
the unary half of the client's `lessor` (`client/v3/lease.go`: `Grant`, `Revoke`), of the retry
lease client and the generated stub (`retry.go`, `api/etcdserverpb/rpc_grpc.pb.go`) it calls,
and etcd's specs of the `Lease` service's `LeaseGrant` and `LeaseRevoke` that the cache's lease
contract (`isEtcdLease`, `cache/v3/InvEtcdTxn.lean`) asks of the server. The keep-alive half (the
lessor's lock invariant, its goroutines) is `InvLessor.lean`. Lean-first (no Rocq counterpart).

**Messages** (`ProtoMsg` instances, trusted wire models as the KV service's, `InvKVConn.lean`):
a `LeaseGrantRequest`'s model is its `(TTL, ID)`, a `LeaseRevokeRequest`'s its `ID`, both held by
the sender as the owned struct and by the server's decoded copy read-only; a `LeaseGrantResponse`'s
model is every field the client reads (`LeaseGrantRespM`: the header, `ID`, `TTL`, `Error`), a
`LeaseRevokeResponse`'s its header (`LeaseRevokeRespM`), held read-only by the server's response
and the client's decoded reply alike.

**The objects**: `leaseStubAt lc conn` (the generated `*leaseClient` on `conn`), `retryLeaseAt rlc
conn` (a `*retryLeaseClient` over one), `lessorRemoteAt l addr` (what `Grant`, `Revoke` and the
keep-alive loop read of a `*lessor`: its `remote`, a retry lease client over a connection to
`addr`, and its call options, both fixed since `NewLeaseFromLeaseClient`).

**etcd's specs** (`etcdLeaseGrantSpec`, `etcdLeaseRevokeSpec`; predicate transformers, at any etcd
model `EM`): whatever the request, a reply message whose header revision etcd has reached
(`etcdReached`), and for a grant a lease ID other than `NoLease` (`0`): what `isEtcdLease`
promises of `Grant` and `Revoke`. That etcd's server registers them (`EtcdServer.LeaseGrant`,
`LeaseRevoke` and their gRPC handlers at `v3rpc.etcdModelOfServer E`) is the client lease's stage
(c), not done: the client's results take the registrations as premises, as the KV's do
(`isEtcdKVE_of_kv`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

/-! ## Messages -/

section model
variable [ext : FfiSyntax]

/-- A `*pb.LeaseGrantResponse` as the wire carries it: its header, `ID`, `TTL`, `Error`. -/
structure LeaseGrantRespM where
  hdr : HdrM
  id : w64
  ttl : w64
  err : GoString

/-- A `*pb.LeaseRevokeResponse` as the wire carries it: its header. -/
structure LeaseRevokeRespM where
  hdr : HdrM

end model

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `*pb.LeaseGrantResponse` `l` holds the message `m`** (read-only). -/
def leaseGrantRespMsg (l : Loc) (m : LeaseGrantRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ h : Loc,
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" l ↦□ m.id ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"TTL" l ↦□ m.ttl ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Error" l ↦□ m.err)

instance leaseGrantRespMsg_persistent (l : Loc) (m : LeaseGrantRespM) :
    Persistent (leaseGrantRespMsg (GF := GF) l m) := by
  unfold leaseGrantRespMsg; infer_instance

/-- **The `*pb.LeaseRevokeResponse` `l` holds the message `m`** (read-only). -/
def leaseRevokeRespMsg (l : Loc) (m : LeaseRevokeRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ h : Loc,
    structFieldRef etcdserverpb.LeaseRevokeResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr)

instance leaseRevokeRespMsg_persistent (l : Loc) (m : LeaseRevokeRespM) :
    Persistent (leaseRevokeRespMsg (GF := GF) l m) := by
  unfold leaseRevokeRespMsg; infer_instance

/-- **A `*pb.LeaseGrantRequest`** on the wire: its `(TTL, ID)`. -/
def pbLeaseGrantRequest : ProtoMsg GF where
  ty := etcdserverpb.LeaseGrantRequest.ty
  M := w64 × w64
  send inp m := iprop(∃ req : etcdserverpb.LeaseGrantRequest, inp ↦ req ∗ ⌜m = (req.TTL', req.ID')⌝)
  recv r m := iprop(structFieldRef etcdserverpb.LeaseGrantRequest go!"TTL" r ↦□ m.1 ∗
    structFieldRef etcdserverpb.LeaseGrantRequest go!"ID" r ↦□ m.2)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.LeaseGrantRequest))
  own l := iprop(∃ v : etcdserverpb.LeaseGrantRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.LeaseGrantResponse`** on the wire (`leaseGrantRespMsg`). -/
def pbLeaseGrantResponse : ProtoMsg GF where
  ty := etcdserverpb.LeaseGrantResponse.ty
  M := LeaseGrantRespM
  send := leaseGrantRespMsg
  recv := leaseGrantRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.LeaseGrantResponse))
  own l := iprop(∃ v : etcdserverpb.LeaseGrantResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.LeaseRevokeRequest`** on the wire: its `ID`. -/
def pbLeaseRevokeRequest : ProtoMsg GF where
  ty := etcdserverpb.LeaseRevokeRequest.ty
  M := w64
  send inp m := iprop(∃ req : etcdserverpb.LeaseRevokeRequest, inp ↦ req ∗ ⌜m = req.ID'⌝)
  recv r m := iprop(structFieldRef etcdserverpb.LeaseRevokeRequest go!"ID" r ↦□ m)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.LeaseRevokeRequest))
  own l := iprop(∃ v : etcdserverpb.LeaseRevokeRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.LeaseRevokeResponse`** on the wire (`leaseRevokeRespMsg`). -/
def pbLeaseRevokeResponse : ProtoMsg GF where
  ty := etcdserverpb.LeaseRevokeResponse.ty
  M := LeaseRevokeRespM
  send := leaseRevokeRespMsg
  recv := leaseRevokeRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.LeaseRevokeResponse))
  own l := iprop(∃ v : etcdserverpb.LeaseRevokeResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **What a unary `LeaseGrant` call returns** to the client (as `putCallOut`). -/
def leaseGrantCallOut (Q : LeaseGrantRespM → IProp GF) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM, leaseGrantRespMsg resp m ∗ Q m) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err))

/-- **What a unary `LeaseRevoke` call returns** to the client (as `putCallOut`). -/
def leaseRevokeCallOut (Q : LeaseRevokeRespM → IProp GF) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseRevokeRespM, leaseRevokeRespMsg resp m ∗ Q m) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err))

/-! ## The objects -/

/-- **The generated stub `lc`** (`*etcdserverpb.leaseClient`) on the connection `conn`. -/
def leaseStubAt (lc conn : Loc) : IProp GF :=
  iprop(structFieldRef etcdserverpb.leaseClient go!"cc" lc ↦□
    (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn :
      GoInterface))

instance leaseStubAt_persistent (lc conn : Loc) : Persistent (leaseStubAt (GF := GF) lc conn) := by
  unfold leaseStubAt; infer_instance

/-- **The `*retryLeaseClient` `rlc`** over a stub on `conn`. -/
def retryLeaseAt (rlc conn : Loc) : IProp GF :=
  iprop(∃ lc : Loc, structFieldRef go_etcd_io.etcd.client.v3.retryLeaseClient go!"lc" rlc ↦□
      (interface.mkOk (go.GoType.PointerType etcdserverpb.leaseClient.ty) #lc : GoInterface) ∗
    leaseStubAt lc conn)

instance retryLeaseAt_persistent (rlc conn : Loc) : Persistent (retryLeaseAt (GF := GF) rlc conn) := by
  unfold retryLeaseAt; infer_instance

/-- **What the unary calls of the `*lessor` `l` read** (persistent): its `remote`, a
`*retryLeaseClient` over a connection to the server at `addr`, and its call options (full, as
`client.go` builds them), fixed since `NewLeaseFromLeaseClient`. -/
def lessorRemoteAt (l : Loc) (addr : GoString) : IProp GF :=
  iprop(∃ (rlc conn : Loc) (sl : GoSlice),
    structFieldRef go_etcd_io.etcd.client.v3.lessor go!"remote" l ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty) #rlc :
        GoInterface) ∗
    retryLeaseAt rlc conn ∗ isEtcdConn conn addr ∗
    structFieldRef go_etcd_io.etcd.client.v3.lessor go!"callOpts" l ↦□ sl ∗ callOptsAt sl)

instance lessorRemoteAt_persistent (l : Loc) (addr : GoString) :
    Persistent (lessorRemoteAt (GF := GF) l addr) := by
  unfold lessorRemoteAt; infer_instance

end defs

/-! ## etcd's specs of the `Lease` service's unary methods -/

section specs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [EM : EtcdModel GF]

/-- **etcd's spec of `LeaseGrant`** (see the file header): any request gets a reply whose lease ID
is not `NoLease` and whose header revision etcd has reached. -/
def etcdLeaseGrantSpec : GrpcSpec (GF := GF) pbLeaseGrantRequest pbLeaseGrantResponse :=
  fun (_ : w64 × w64) (Φ : LeaseGrantRespM → IProp GF) =>
    iprop(∀ m : LeaseGrantRespM, ⌜m.id ≠ W64 0⌝ -∗ etcdReached m.hdr.revision -∗ Φ m)

/-- **etcd's spec of `LeaseRevoke`**: any request gets a reply whose header revision etcd has
reached. -/
def etcdLeaseRevokeSpec : GrpcSpec (GF := GF) pbLeaseRevokeRequest pbLeaseRevokeResponse :=
  fun (_ : w64) (Φ : LeaseRevokeRespM → IProp GF) =>
    iprop(∀ m : LeaseRevokeRespM, etcdReached m.hdr.revision -∗ Φ m)

end specs

end EtcdGrove
end Perennial
