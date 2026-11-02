/-
**etcd's KV calls and lease reads registered at a served member's address** (the closed lease
example, 2026-11-02, `notes/lease-ex-plan.md`). Lean-first (no Rocq counterpart).

`kv_lease_served`: `kv_served`'s ghost step, with the Lease service's reads served too
(`client.etcdLeaseReadAt`: `LeaseTimeToLive`, `LeaseLeases` at etcd's specs), from `grpcUp`'s
Lease service (`grpcLeaseUp`) and the member's lessor reader side (`memberUp`'s `srvLeaseRd`). One
`grpc.serve` serves every method: the KV's run slots and the lease reads' (`raftLeaseRead_server`'s
`E.RD ∗ threadTok` and the store's reader) are the same slots, each run holding its goroutine's
thread token (`grpc.serve`, F4).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Served
public import Proof.go_etcd_io.etcd.client.v3.LeaseReadServed

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

/-- **etcd's KV calls and lease reads registered at the address** (see the file header); as
`kv_served`, under `grpcRepliesFit`, with the lessor's reader side and the bounds the lease reads'
server specs take (`threadBound GF ≤ 2 ^ 30 - 1`, `receiptBound GF ≤ 2 ^ 48`). -/
theorem kv_lease_served (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (HT : threadBound GF ≤ 2 ^ 30 - 1)
    (Hrf : grpcRepliesFit) (hρ : ρ.rd = γr) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeaseRd s E ∗
        ([∗list] _x ∈ List.replicate 64 (), srvLeadTimeReader s) ∗
        ([∗list] _x ∈ List.replicate (64 - 2) (), srvLgReader s) ∗
        ([∗list] _x ∈ List.replicate 64 (), E.RD) ∗
        ([∗list] _x ∈ List.replicate 64 (), mvcc.storeReader E.s E.γ) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          srvReadReader s γr) ∗
        ([∗list] _x ∈ List.replicate 64 (), srvBemuReader s) ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> grpcServeTok gs lis ∗ etcdKVAt addr E ρ γr cid mid ∗
        client.etcdLeaseReadAt addr := by
  sorry

end served

end common
end EtcdGrove
end Perennial
