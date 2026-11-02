/-
**The server's lease grant** (the lease-grant plan's D3/D4, 2026-11-02, `notes/lease-grant-plan.md`):
the vocabulary of `EtcdServer.LeaseGrant`'s triple. Lean-first (no Rocq counterpart).

A cluster **grants leases** (`srvGrantsLeases`) when its KV names say so (`KVNames.lg`: its lessor
monotone, `NewServer`'s `NewLessor` call) and auth is off (the grant guard `srvGrantGuard`); the
deployment premise `lease.leasesNoExpiry` (no lease expires: the expiry loop sends nothing) is
`NewServer`'s, for a cluster that grants. There a grant the server answers is in the lessor's history
(`lease.leaseGrantedAt`), so every later `Leases()` lists it (`lease.leaseGrantedAt_listed`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CompactMode

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

/-- **The cluster grants leases** (see the file header): two scope restrictions, the KV names' `lg`
(the cluster's requests may grant leases: its lessor monotone) and auth off (required: the grant
guard `srvGrantGuard` is `False` with auth on, whose layer rests on the lessor finding no lease,
`srvLessorNil`). (The review's S1, 2026-11-02: until then also the deployment premise
`lease.leasesNoExpiry`, which only the apply thread's grant needs: it is `NewServer`'s row
`ρ.rd.kv.lg = true → lease.leasesNoExpiry ∧ runSnapLgOk`, so a result over this spec is conditional
on it through `NewServer`.) -/
def srvGrantsLeases (E : apply.AEnv GF) (ρ : ReqNames) : Prop :=
  ρ.rd.kv.lg = true ∧ E.authOn = false

/-- **A decoded `*pb.LeaseGrantRequest` `r`**: its `TTL` read-only, its `ID` owned
(`LeaseGrant` writes a fresh id there when it is `0`, `v3_server.go:436-439`). -/
def leaseGrantReqOwn (r : Loc) (ttl id : w64) : IProp GF :=
  iprop(structFieldRef etcdserverpb.LeaseGrantRequest go!"TTL" r ↦□ ttl ∗
    structFieldRef etcdserverpb.LeaseGrantRequest go!"ID" r ↦ id)

/-- **The server's grant response** `resp` (the apply thread's `LeaseGrant`, `backend.go`), as its
receiver (the Lease service's handler, `v3rpc.leaseHdrAns`) needs it: its lease `id` (not `0`),
`TTL` and `Error` read-only; its header's four id fields owned (`txn.respHdrOwn`: the gRPC layer's
`header.fill` writes them) and its revision read-only, not `0`, a revision the store has reached
(`srvRevLb`: a certified log longer than it, from which the clients' `etcdReached` follows,
`v3rpc.etcdReached_of_certOk`); and the lease granted at an index `i` of the lessor's history.
(The review's M3, 2026-11-02: until then the applied log itself, its certificate and witness, the
supplier's mechanism.) -/
def leaseGrantedResp (E : apply.AEnv GF) (resp : Loc) : IProp GF :=
  iprop(∃ (id ttl : w64) (e : GoString) (i : Nat) (h : Loc) (rv : w64),
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" resp ↦□ h ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rv ∗ ⌜rv ≠ W64 0⌝ ∗
    srvRevLb E.γ (sint.Z rv) ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" resp) ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗ ⌜id ≠ W64 0⌝ ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"TTL" resp ↦□ ttl ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Error" resp ↦□ e ∗
    lease.leaseGrantedAt E.γ.leases i id)

end defs


end EtcdGrove
end Perennial
