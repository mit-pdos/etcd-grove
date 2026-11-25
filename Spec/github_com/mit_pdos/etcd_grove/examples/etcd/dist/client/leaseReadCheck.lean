/-
`leaseReadCheck(addr)` (leaseN's `check`, copied; `examples/etcd/dist/client/lease.go`): the two lease reads
through a new client of the member at `addr`, at another machine. The triple: with `addr` a valid address
serving etcd's table (`leaseMember`), it does not panic: a listing that answered names no lease twice, and a
`TimeToLive(7)` that answered is about lease `7`.
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

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev leaseReadCheck.spec : Prop :=
  ∀ [π : NetProtoGS] (addr : GoString),
  -- a watch environment for `newClient`'s client (the lease calls read none of it)
  Nonempty (WEnv GF) →
  threadBound GF ≤ 2 ^ 30 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ leaseMember (Gg := hG.goose_globalGS) addr }}
    (App (Val (@! client.leaseReadCheck)) (Val #addr))
  {{ (b : Bool), RET #b; levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
