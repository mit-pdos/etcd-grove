/-
**The server's lease grant** (the lease-grant plan's D3/D4, 2026-11-02, `notes/lease-grant-plan.md`):
the vocabulary of `EtcdServer.LeaseGrant`'s triple. Lean-first (no Rocq counterpart).

A cluster **grants leases** (`srvGrantsLeases`) when its KV names say so (`KVNames.lg`: its lessor
monotone, `NewServer`'s `NewLessor` call), auth is off (the grant guard `srvGrantGuard`), and the
deployment premise `lease.leasesNoExpiry` holds (no lease expires during the run: the expiry loop
sends nothing). There a grant the server answers is in the lessor's history
(`lease.leaseGrantedAt`), so every later `Leases()` lists it (`lease.leaseGrantedAt_listed`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead

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

/-- **The cluster grants leases** (see the file header): the KV names' `lg`, auth off, and the
deployment premise `lease.leasesNoExpiry`. -/
def srvGrantsLeases (E : apply.AEnv GF) (ρ : ReqNames) : Prop :=
  ρ.rd.kv.lg = true ∧ E.authOn = false ∧ lease.leasesNoExpiry

/-- **A decoded `*pb.LeaseGrantRequest` `r`**: its `TTL` read-only, its `ID` owned
(`LeaseGrant` writes a fresh id there when it is `0`, `v3_server.go:436-439`). -/
def leaseGrantReqOwn (r : Loc) (ttl id : w64) : IProp GF :=
  iprop(structFieldRef etcdserverpb.LeaseGrantRequest go!"TTL" r ↦□ ttl ∗
    structFieldRef etcdserverpb.LeaseGrantRequest go!"ID" r ↦ id)

/-- **The server's grant response** `resp` (the apply thread's `LeaseGrant`, `backend.go`): its
lease `id` (not `0`), `TTL` and `Error` read-only, its header's id fields owned at the applied log
`log` (`apply.appliedHdr`; a witness the request was applied there, `appliedWit`) and its revision
read-only, not `0`, a revision of that log (`newHeader`'s: the store's current one), and the lease
granted at an index `i` of the lessor's history. -/
def leaseGrantedResp (E : apply.AEnv GF) (ρ : ReqNames) (resp : Loc) : IProp GF :=
  iprop(∃ (log : mvcc.Log) (id ttl : w64) (e : GoString) (i : Nat) (h : Loc) (rv : w64),
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" resp ↦□ h ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rv ∗
    ⌜rv ≠ W64 0 ∧ uint.nat rv < log.length⌝ ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗ ⌜id ≠ W64 0⌝ ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"TTL" resp ↦□ ttl ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Error" resp ↦□ e ∗
    apply.appliedHdr log (structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" resp) ∗
    appliedWit ρ.rd log ∗ lease.leaseGrantedAt E.γ.leases i id)

end defs

end EtcdGrove
end Perennial
