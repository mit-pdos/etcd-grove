/-
**etcd's KV calls, lease reads and lease grants registered at a served member's address** (the
lease-grant plan's D5, 2026-11-02, `notes/lease-grant-plan.md`). Lean-first (no Rocq counterpart).

`kv_lease_grant_served`: `kv_lease_served`'s ghost step in a cluster that grants leases
(`srvGrantsLeases`: the KV names' `lg` and auth off, two scope restrictions; conditional, through
`NewServer`'s gated row, on the deployment premise `lease.leasesNoExpiry`), with also `LeaseGrant`
and `LeaseLeases` registered at the specs at the lessor's history (`etcdLeaseGrantAt`): a grant's
reply carries its lease's grant (`etcdLeaseGrantSpecL`), and a listing lists every grant the caller
hands in (`etcdLeaseLeasesSpecL`). The Lease service's `LeaseGrant` handler calls the server's
(`v3rpc.lessorGrantOkL_of_server`). Not proved (Draft).

Why one member's lessor (review S5): the contracts name `E.γ.leases`, this member's, not a
cluster-level certificate, because Go's listing is member-local: `LeaseLeases` reads the member's
own lessor without a read index (`v3_server.go:737-749`), so a lagging member need not list a lease
the cluster granted, and a cluster-level contract would be false. With several endpoints the client
would need the contracts at every member, which no granting cluster gives.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.ServedLease
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseGrant

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`LeaseGrant` and `LeaseLeases` registered at the specs at the lessor `E.γ.leases`'s
history** (persistent). Per member, not per cluster: `LeaseLeases` is a member-local read (see
the file header). -/
def etcdLeaseGrantAt (addr : GoString) (E : apply.AEnv GF) : IProp GF :=
  iprop(isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant"
      (etcdLeaseGrantSpecL (EM := v3rpc.etcdModelOfServer E) E.γ.leases) ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpecL E.γ.leases))

instance etcdLeaseGrantAt_persistent (addr : GoString) (E : apply.AEnv GF) :
    Persistent (etcdLeaseGrantAt addr E) := by
  unfold etcdLeaseGrantAt; infer_instance

/-- **etcd's KV calls, lease reads and lease grants registered at the address** (see the file
header): `kv_lease_served`'s premises, in a cluster that grants leases. -/
theorem kv_lease_grant_served (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hP : leasePeersOk) (hρ : ρ.rd = γr) (hG : srvGrantsLeases E ρ) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E ∗ threadTok ∗
        kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> grpcServeTok gs lis ∗ etcdKVAt addr E ρ γr cid mid ∗
        client.etcdLeaseReadAt addr ∗ etcdLeaseGrantAt addr E := by
  sorry

end served

end common
end EtcdGrove
end Perennial
