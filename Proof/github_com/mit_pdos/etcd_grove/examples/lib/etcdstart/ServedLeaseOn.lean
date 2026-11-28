/-
**etcd's Lease service registered at a served member's address, with auth on** (auth-lease S4, item 9,
2026-11-18; decided by etcd-grove-03: the serve step's lease part as an etcdstart lemma beside authkv's
serve steps). Lean-first (no Rocq counterpart).

`lease_served_on`: the ghost step after `grpc.start'` (authkv's `ak_served_kv`, which gives the
persistent server token `grpcServerAt`) that registers the Lease service's four unary methods at their
metadata specs with auth on: `LeaseGrant` and `LeaseRevoke` (`client.etcd_lease_auth_served_on`, in
the revocable lease mode) and `LeaseTimeToLive` and `LeaseLeases` (`client.etcd_lease_read_served`,
at the member's lessor `mvccLeases E.γ`, whose contract `raftLeaseRead` comes from the server, as
`kv_lease_served`'s: `v3rpc.raftLeaseRead_server`, under the deployment premise `leasePeersOk`). Its
inputs are `grpcUpOn`'s Lease service (`grpcLeaseUp`), the member's views with auth on, its lessor's
reader side at the revocable mode (`memberUpOn`'s `srvLeaseRd`), and the run pools.

This module holds the registrations' definition (`etcdLeaseServedOn`, a spec's vocabulary);
`lease_served_on`, over linked results, is in `ServedLeaseOnLinked.lean` (CLAUDE.md, "Import tiers").
-/
module

public import Proof.go_etcd_io.etcd.client.v3.LeaseSpecs
public import Proof.google_golang_org.grpc.InvGrpc
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The Lease service's unary methods registered at their specs with auth on** (persistent): the
grant and the revocation at etcd's metadata specs with auth on, the grant's lease at the member's
lessor `mvccLeases E.γ` (`etcdLeaseGrantSpecOn`, `etcdLeaseRevokeSpecOn`), and the two reads at their
metadata-indexed specs at that lessor (`etcdLeaseTTLSpecMd`, `etcdLeaseLeasesSpecMd`). -/
def etcdLeaseServedOn (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseGrant"
      (client.etcdLeaseGrantSpecOn (srvTLSId s) E ρ (mvcc.api.mvccLeases E.γ)) ∗
    isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseRevoke" (client.etcdLeaseRevokeSpecOn (srvTLSId s) E ρ) ∗
    isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseTimeToLive"
      (client.etcdLeaseTTLSpecMd (srvTLSId s) (leaseTTLRow s (mvcc.api.mvccLeases E.γ)) E (mvcc.api.mvccLeases E.γ)) ∗
    isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseLeases"
      (client.etcdLeaseLeasesSpecMd (srvTLSId s) E (mvcc.api.mvccLeases E.γ)))

instance etcdLeaseServedOn_persistent (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) : Persistent (etcdLeaseServedOn addr s E ρ) := by
  unfold etcdLeaseServedOn; infer_instance

end served

end etcdstart
end EtcdGrove
end Perennial
