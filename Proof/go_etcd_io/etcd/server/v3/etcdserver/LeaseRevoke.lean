/-
**The server's lease revocation** (the lease-expiry plan's X6, 2026-11-04,
`notes/lease-expiry-plan.md`): the vocabulary of `EtcdServer.LeaseRevoke`'s triple, `LeaseGrant.lean`'s
mirrored. Lean-first (no Rocq counterpart).

A cluster **revokes leases** (`srvRevokesLeases`) when its KV names' lease mode is `revocable` (its
lessor's leases may expire and be revoked: `reqPropOk`'s revocation form, `revokePropOk`) and auth is
off. A revocation the server answers without error was applied by the apply thread's backend, whose
response header is `newHeader`'s after it: a revision the store has reached (`srvRevLb`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseGrant

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

-- `srvRevokesLeases` (the cluster revokes leases): `RevokeCtx.lean` (2026-11-06, revoke-open: the
-- revocation's spec, below this module, names it).

/-- **A decoded `*pb.LeaseRevokeRequest` `r`**: not `null` (the proposal's `LeaseRevoke` field
needs it, `apply.leaseRevokeIs`; Go's type assertion on the response panics on a nil request,
which proposes an empty request), its `ID` read-only. -/
def leaseRevokeReqRO (r : Loc) (id : w64) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.LeaseRevokeRequest go!"ID" r ↦□ id)

instance leaseRevokeReqRO_persistent (r : Loc) (id : w64) :
    Persistent (leaseRevokeReqRO (GF := GF) r id) := by
  unfold leaseRevokeReqRO; infer_instance

/-- **The server's revocation response** `resp` (the apply thread's `LeaseRevoke`, `backend.go`),
as its receiver (the Lease service's handler, `v3rpc.leaseHdrAns`) needs it: its header's four id
fields owned (`txn.respHdrOwn`) and its revision read-only, not `0`, a revision the store has reached
(`srvRevLb`: the log the revocation committed, certified). -/
def leaseRevokedResp (E : apply.AEnv GF) (resp : Loc) : IProp GF :=
  iprop(∃ (h : Loc) (rv : w64),
    structFieldRef etcdserverpb.LeaseRevokeResponse go!"Header" resp ↦□ h ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rv ∗ ⌜rv ≠ W64 0⌝ ∗
    srvRevLb E (sint.Z rv) ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.LeaseRevokeResponse go!"Header" resp))

end defs

end EtcdGrove
end Perennial
