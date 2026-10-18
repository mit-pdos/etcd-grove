/-
**The gRPC Lease service's unary half, down to the server's lessor** (the client lease's stage
(c), its workload-free half, 2026-10-18): `lease.go`'s `LeaseServer.LeaseGrant`/`LeaseRevoke`
and `quota.go`'s `quotaLeaseServer` (`LeaseGrant` checks the quota first, `LeaseRevoke` is the
embedded service's, promoted), over the server's lease methods taken as a contract, as the KV
service's handlers are over `raftKV` (`InvKV.lean`). Lean-first (no Rocq counterpart).

**The contract** (`raftLessor s E S`, persistent; `lessorGrantOk`, `lessorRevokeOk`): the
triples of `*EtcdServer`'s `LeaseGrant(ctx, r)` and `LeaseRevoke(ctx, r)` (the
`etcdserver.Lessor` interface value the `*LeaseServer` holds is the server `s`, `NewLeaseServer`'s
`le: s`), called with the run's resource `S` (given back with every answer), the context of a
gRPC run (`isContext`, `grpcRunCtx`) and the decoded request (its fields read-only, as the gRPC
runtime hands it: `leaseGrantReqIs`, `leaseRevokeReqIs`, `pbLeaseGrantRequest.recv`'s form).
Its answers are fixed, not parameters: what the client's specs (`etcdLeaseGrantSpec`,
`etcdLeaseRevokeSpec`, `client/v3/InvLease.lean`) need and the server's applier gives
(`leaseGrantAns`, `leaseRevokeAns`): an error `togRPCError` can take (`srvErrIs`), or a non-nil
response whose header (`leaseHdrAns`) has its four id fields owned (`hdrW`: the handler's
`fill` writes them) and its revision `r` read-only, not `0` and reached
(`etcdReached (EM := etcdModelOfServer E) r`: the applier's `newHeader()` reads `KV.Rev()`, at
least `1`, the revision of a log the apply thread certified); a grant's response also has its
`ID` read-only and not `NoLease` (`0`), its `TTL` and `Error` read-only.

**Why the lease ID's guarantee is the contract's**: nothing above the call touches the response's
`ID` (`LeaseServer.LeaseGrant` returns the server's response with its header filled), so the
handler cannot give it; it comes from the server: `EtcdServer.LeaseGrant` replaces a request ID
`0` by a fresh positive one before proposing (`for r.ID == NoLease`), and the applier's
`lessor.Grant(id, ttl)` rejects `NoLease` and answers the lease of that ID (`backend.go`:
`resp.ID = int64(l.ID)`).

**What the later server proof must meet** (`raftLessor s E S` of `*EtcdServer`, through
`raftRequest`): the two triples at the run slot `S` it chooses (`client/v3/Results.lean`'s
`etcd_kv_lease_served` takes `S := etcdRunSlot s E γr`, the KV handlers' slot); note that the
decoded request is read-only here, while `EtcdServer.LeaseGrant` writes `r.ID` when it is `0`
(the gRPC wire model's `ProtoMsg.recv` is persistent: `notes/STATUS.md`).

**The objects** (persistent): `leaseServerAt p s A cid mid` (the `*LeaseServer` `p` that
`NewLeaseServer(s)` builds: its header `hdrIs` at the KV parameters `A`, `le` the server `s`),
`quotaLeaseServerAt q ls s` (the `*quotaLeaseServer` `q` over the service value `ls`, its quota
alarmer `quotaAlarmerAt`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClientModel

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-! ## The requests, as the gRPC runtime hands them -/

/-- **The decoded `*pb.LeaseGrantRequest` `r`** of `(TTL, ID)` `m` (read-only;
`pbLeaseGrantRequest.recv`). -/
def leaseGrantReqIs (r : Loc) (m : w64 × w64) : IProp GF :=
  iprop(structFieldRef etcdserverpb.LeaseGrantRequest go!"TTL" r ↦□ m.1 ∗
    structFieldRef etcdserverpb.LeaseGrantRequest go!"ID" r ↦□ m.2)

instance leaseGrantReqIs_persistent (r : Loc) (m : w64 × w64) :
    Persistent (leaseGrantReqIs (GF := GF) r m) := by
  unfold leaseGrantReqIs; infer_instance

/-- **The decoded `*pb.LeaseRevokeRequest` `r`** of `ID` `id` (read-only;
`pbLeaseRevokeRequest.recv`). -/
def leaseRevokeReqIs (r : Loc) (id : w64) : IProp GF :=
  iprop(structFieldRef etcdserverpb.LeaseRevokeRequest go!"ID" r ↦□ id)

instance leaseRevokeReqIs_persistent (r : Loc) (id : w64) :
    Persistent (leaseRevokeReqIs (GF := GF) r id) := by
  unfold leaseRevokeReqIs; infer_instance

/-! ## The server's answers -/

/-- **A lease answer's header**, at the address `hf` of the response's `Header` field (see the
file header): a header whose id fields are owned (`hdrW`) and whose revision is read-only, not
`0` and reached. -/
def leaseHdrAns (E : apply.AEnv GF) (hf : Loc) : IProp GF :=
  iprop(∃ (h : Loc) (r : w64), hf ↦□ h ∗ hdrW h ∗ ⌜r ≠ W64 0⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ r ∗
    etcdReached (EM := etcdModelOfServer E) r)

/-- **A grant's fields** (read-only): the lease ID, not `NoLease`, the TTL, the error string. -/
def leaseGrantFields (resp : Loc) : IProp GF :=
  iprop(∃ (id ttl : w64) (e : GoString),
    structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗ ⌜id ≠ W64 0⌝ ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"TTL" resp ↦□ ttl ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Error" resp ↦□ e)

instance leaseGrantFields_persistent (resp : Loc) :
    Persistent (leaseGrantFields (GF := GF) resp) := by
  unfold leaseGrantFields; infer_instance

/-- **The server's answer to a grant** (see the file header). -/
def leaseGrantAns (E : apply.AEnv GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗
      leaseHdrAns E (structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" resp) ∗
      leaseGrantFields resp) ∨
    srvErrIs err)

/-- **The server's answer to a revoke** (see the file header). -/
def leaseRevokeAns (E : apply.AEnv GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗
      leaseHdrAns E (structFieldRef etcdserverpb.LeaseRevokeResponse go!"Header" resp)) ∨
    srvErrIs err)

/-! ## The contract -/

/-- **The server's `LeaseGrant`** (one conjunct of `raftLessor`). -/
def lessorGrantOk (s : Loc) (E : apply.AEnv GF) (S : IProp GF) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (m : w64 × w64),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ leaseGrantReqIs r m }}
      (App (App (Val (srvM s go!"LeaseGrant")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ leaseGrantAns E resp err }})

/-- **The server's `LeaseRevoke`** (one conjunct of `raftLessor`). -/
def lessorRevokeOk (s : Loc) (E : apply.AEnv GF) (S : IProp GF) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (id : w64),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ leaseRevokeReqIs r id }}
      (App (App (Val (srvM s go!"LeaseRevoke")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ leaseRevokeAns E resp err }})

instance lessorGrantOk_persistent (s : Loc) (E : apply.AEnv GF) (S : IProp GF) :
    Persistent (lessorGrantOk s E S) := by
  unfold lessorGrantOk; infer_instance

instance lessorRevokeOk_persistent (s : Loc) (E : apply.AEnv GF) (S : IProp GF) :
    Persistent (lessorRevokeOk s E S) := by
  unfold lessorRevokeOk; infer_instance

/-- **The server `s` as the Lease service's handlers call it** (persistent; see the file
header): its `LeaseGrant` and `LeaseRevoke`, with the run's resource `S`, answering at the
server's model of the apply environment `E`. -/
def raftLessor (s : Loc) (E : apply.AEnv GF) (S : IProp GF) : IProp GF :=
  iprop(lessorGrantOk s E S ∗ lessorRevokeOk s E S)

instance raftLessor_persistent (s : Loc) (E : apply.AEnv GF) (S : IProp GF) :
    Persistent (raftLessor s E S) := by
  unfold raftLessor; infer_instance

/-! ## The handlers' answers -/

/-- **A lease handler's header**, filled (`hdrFilled`: the cluster `cid`, the member `mid`), its
revision read-only, not `0` and reached. -/
def leaseHdrOut (E : apply.AEnv GF) (cid mid : w64) (hf : Loc) : IProp GF :=
  iprop(∃ (h : Loc) (r : w64), hf ↦□ h ∗ hdrFilled h cid mid ∗ ⌜r ≠ W64 0⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ r ∗
    etcdReached (EM := etcdModelOfServer E) r)

/-- **`LeaseServer.LeaseGrant`'s answer**: the server's response with its header filled, or `nil`
and a non-nil error. -/
def leaseGrantOut (E : apply.AEnv GF) (cid mid : w64) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗
      leaseHdrOut E cid mid (structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" resp) ∗
      leaseGrantFields resp) ∨
    ⌜resp = null ∧ err ≠ GoInterface.nil⌝)

/-- **`LeaseServer.LeaseRevoke`'s answer** (as `leaseGrantOut`). -/
def leaseRevokeOut (E : apply.AEnv GF) (cid mid : w64) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗
      leaseHdrOut E cid mid (structFieldRef etcdserverpb.LeaseRevokeResponse go!"Header" resp)) ∨
    ⌜resp = null ∧ err ≠ GoInterface.nil⌝)

/-! ## The objects -/

/-- **The `*LeaseServer` `p`** that `NewLeaseServer(s)` built (persistent; see the file header):
its header (`hdrIs`, at the KV parameters `A` `newHeader` was given), `le` the server `s`. -/
def leaseServerAt (p s : Loc) (A : KVAns GF) (cid mid : w64) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗
    hdrIs (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer go!"hdr" p)
      s A cid mid ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer go!"le" p ↦□
      (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s : GoInterface))

instance leaseServerAt_persistent (p s : Loc) (A : KVAns GF) (cid mid : w64) :
    Persistent (leaseServerAt p s A cid mid) := by
  unfold leaseServerAt; infer_instance

/-- **The `*quotaLeaseServer` `q`** over the service value `ls` and the server `s` (persistent):
its embedded `LeaseServer` `ls`, its quota alarmer (`quotaAlarmerAt`). -/
def quotaLeaseServerAt (q : Loc) (ls : GoInterfaceOk) (s : Loc) : IProp GF :=
  iprop(⌜q ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer go!"LeaseServer" q ↦□
      GoInterface.ok ls ∗
    quotaAlarmerAt
      (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer go!"qa" q) s)

instance quotaLeaseServerAt_persistent (q : Loc) (ls : GoInterfaceOk) (s : Loc) :
    Persistent (quotaLeaseServerAt (GF := GF) q ls s) := by
  unfold quotaLeaseServerAt; infer_instance

end defs

end v3rpc
end EtcdGrove
end Perennial
