/-
`RunLeaseExpiry(eps)`: the leaseExpiry workload of `etcd_safe` (`examples/etcd/dist/client/lease.go`;
leaseexpiryN's `run` minus its members' serving): a lease of the shortest TTL granted through each member;
then, member by member, its listing polled until it no longer lists the lease granted through it
(`gone`), then listed once more: it panics if that listing has the lease again.

**The triple** (leaseexpiryN's argument, at the cluster view `Γ`): in revocable lease mode
(`Γ.kv.lm = .revocable`), with each endpoint a valid address serving etcd's table `svc` for a member of `Γ`
(`leaseMember`), it does not panic: the lease is live in the member's lessor history from the grant's index
(`Lease_GrantLive_dist`), absent from it at a later index (`gone`), and every later listing is a snapshot at
a still later index (`Lease_LeasesLive_dist`), where it stays absent. It returns a `Result`, `levelTok 0`
kept. (That a lease once gone stays gone is the history's, at the member: the proof takes it as the draft law
`lessorAbsentStays_dist.law`, `notes/etcd-dist-n9b.md` §10.)
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist.view

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev RunLeaseExpiry.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ [π : NetProtoGS] (Γ : DistView) (eps : GoSlice) (addrs : List GoString),
  -- a watch environment for `newClient`'s clients (the lease calls read none of it)
  Nonempty (WEnv GF) →
  threadBound GF ≤ 2 ^ 30 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  Γ.kv.lm = .revocable →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs ∗ [∗list] a ∈ addrs, leaseMember (Gg := hG.goose_globalGS) svc Γ a }}
    (App (Val (@! client.RunLeaseExpiry)) (Val #eps))
  {{ (r : client.Result), RET #r; levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
