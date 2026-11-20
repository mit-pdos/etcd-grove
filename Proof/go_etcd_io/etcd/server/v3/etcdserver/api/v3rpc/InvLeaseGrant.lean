/-
**The server's `LeaseGrant` as the Lease service's handler calls it, at the lessor's history** (the
lease-grant plan's D4, 2026-11-02, `notes/lease-grant-plan.md`). Lean-first (no Rocq counterpart).

`lessorGrantOkGM` (`LeaseOn.lean`, amendment (F2)) at the success fact that the response's lease
was granted in the lessor's history (the request: its `TTL` read-only, `leaseGrantReqIs`, its `ID`
owned, `leaseGrantReqIdOwn`: `LeaseGrant` writes it, `v3_server.go:436-439`). `lessorGrantOkLM_of_server`
(`ServerLeaseGrant.lean`) derives it from `EtcdServer.LeaseGrant.spec` in a cluster that grants
leases.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseGrant

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The lease live in the lessor's history from some index**: the grant contract's success fact
with no lease mode (the lease-expiry plan's X2, 2026-11-04: what the reply carries in every mode,
`leaseGrantedResp`'s `leaseLiveFrom`); (the lease-expiry plan's S2–S4, Q-S8, 2026-11-05) and the
lease's request, the request `m`'s TTL `m.1` (`lease.leaseReqIs`). (Review r1 F12, 2026-11-05:
until then also the lease's read-only `ttl` field at least `m.1`, E3/R5, which no consumer reads
since `leaseReqIs`.) -/
def grantLiveG (E : apply.AEnv GF) : w64 × w64 → w64 → IProp GF :=
  fun m id => iprop(∃ (i : Nat) (l : Loc), lease.leaseLiveFrom (mvcc.api.mvccLeases E.γ) i id l ∗
    lease.leaseReqIs (mvcc.api.mvccLeases E.γ) id m.1)

instance grantLiveG_persistent (E : apply.AEnv GF) (m : w64 × w64) (id : w64) :
    Persistent (grantLiveG (GF := GF) E m id) := by
  unfold grantLiveG; infer_instance

end defs

section defsM
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The server's `LeaseGrant` at the lessor's history, in the auth mode `on`** (see the file header):
`lessorGrantOkGM on` at the success fact that the response's lease was granted at an index of the
lessor `(mvcc.api.mvccLeases E.γ)`'s history (the hub plan's "no twin triples", 2026-11-03; auth-lease S4,
the C5′ merge, 2026-11-16: until then `lessorGrantOkL`, over the auth-off `lessorGrantOkG`). -/
abbrev lessorGrantOkLM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) : IProp GF :=
  lessorGrantOkGM on s E ρ S (fun _ id => iprop(∃ i : Nat, lease.leaseGrantedAt (mvcc.api.mvccLeases E.γ) i id))

end defsM

end v3rpc
end EtcdGrove
end Perennial
