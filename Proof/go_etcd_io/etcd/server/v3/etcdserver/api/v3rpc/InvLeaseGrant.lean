/-
**The server's `LeaseGrant` as the Lease service's handler calls it, at the lessor's history** (the
lease-grant plan's D4, 2026-11-02, `notes/lease-grant-plan.md`). Lean-first (no Rocq counterpart).

`lessorGrantOkG` (`InvLease.lean`, amendment (F2)) at the success fact that the response's lease
was granted in the lessor's history (the request: its `TTL` read-only, `leaseGrantReqIs`, its `ID`
owned, `leaseGrantReqIdOwn`: `LeaseGrant` writes it, `v3_server.go:436-439`). `lessorGrantOkL_of_server`
(`ServerLeaseGrant.lean`) derives it from `EtcdServer.LeaseGrant.spec` in a cluster that grants
leases.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease
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

/-- **The server's `LeaseGrant` at the lessor's history** (see the file header): `lessorGrantOk`
and, on success, the response's lease granted at an index of the
lessor `E.γ.leases`'s history. `lessorGrantOkG` at that success fact (the hub plan's "no twin
triples", 2026-11-03: until then the same triple written out). -/
abbrev lessorGrantOkL (s : Loc) (E : apply.AEnv GF) (S : IProp GF) : IProp GF :=
  lessorGrantOkG s E S (fun _ id => iprop(∃ i : Nat, lease.leaseGrantedAt E.γ.leases i id))

/-- **The lease live in the lessor's history from some index**: the grant contract's success fact
with no lease mode (the lease-expiry plan's X2, 2026-11-04: what the reply carries in every mode,
`leaseGrantedResp`'s `leaseLiveFrom`); (2026-11-05, the lease-expiry plan's E3/R5: the granted TTL)
and its read-only `ttl` field at least the request `m`'s TTL (`m.1`). -/
def grantLiveG (E : apply.AEnv GF) : w64 × w64 → w64 → IProp GF :=
  fun m id => iprop(∃ (i : Nat) (l : Loc) (t : w64), lease.leaseLiveFrom E.γ.leases i id l ∗
    lease.lsF go!"ttl" l ↦□ t ∗ ⌜sint.Z m.1 ≤ sint.Z t⌝)

instance grantLiveG_persistent (E : apply.AEnv GF) (m : w64 × w64) (id : w64) :
    Persistent (grantLiveG (GF := GF) E m id) := by
  unfold grantLiveG; infer_instance

end defs

end v3rpc
end EtcdGrove
end Perennial
