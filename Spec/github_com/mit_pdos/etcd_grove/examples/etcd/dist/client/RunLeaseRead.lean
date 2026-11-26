/-
`RunLeaseRead(eps)`: the leaseRead workload of `etcd_safe` (`examples/etcd/dist/client/lease.go`;
leaseN's `run` minus its members' serving): `leaseReadCheck` at every member in turn. The triple: with each
endpoint a valid address serving etcd's table (`leaseMember`), read-only, it does not panic (each member's
listing names no lease twice, each `TimeToLive(7)` is about lease `7`), whatever it returns.
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs


@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.view

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev RunLeaseRead.spec : Prop :=
  ∀ [π : NetProtoGS] (Γ : DistView) (eps : GoSlice) (addrs : List GoString),
  -- a watch environment for `newClient`'s client (the lease calls read none of it)
  Nonempty (WEnv GF) →
  threadBound GF ≤ 2 ^ 30 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs ∗ [∗list] a ∈ addrs, leaseMember (Gg := hG.goose_globalGS) Γ a }}
    (App (Val (@! client.RunLeaseRead)) (Val #eps))
  {{ (r : client.Result), RET #r; levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
