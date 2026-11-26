/-
`RunLeaseCatchup(eps, ready)`: the leaseCatchup workload of `etcd_safe` (`examples/etcd/dist/client/lease.go`;
leasecatchup's `run` minus its start and its cut): a lease of etcd's `MaxLeaseTTL` granted through the last
member, `ready()`, fillers granted through the first, then the last member's listing polled until it lists
the last filler, when it must list the first lease too.

**The triple** (leasecatchup's argument, at the cluster view `Γ`): in monotone lease mode
(`Γ.kv.lm = .mono`: no lease of the program expires, the deployment's `EtcdEnv.noExpiry` at a deployment with
leaseCatchup), with at least one endpoint, each a valid address serving etcd's table for a member of `Γ`
(`leaseMember`), and `ready` a call that returns, it does not panic: the first lease is granted at the last
member's lessor (`Lease_Grant_dist`), so every listing of that member has it (`Lease_LeasesGranted_dist`),
whatever the fillers did. It returns a `Result`, `levelTok 0` kept.
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
abbrev RunLeaseCatchup.spec : Prop :=
  ∀ [π : NetProtoGS] (Γ : DistView) (eps : GoSlice) (addrs : List GoString) (ready : GoFunc),
  -- a watch environment for `newClient`'s clients (the lease calls read none of it)
  Nonempty (WEnv GF) →
  threadBound GF ≤ 2 ^ 30 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  Γ.kv.lm = .mono →
  addrs ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs ∗ ([∗list] a ∈ addrs, leaseMember (Gg := hG.goose_globalGS) Γ a) ∗
      (∀ Ψ : val → IProp GF, ▷ Ψ #() -∗ WP (App (Val #ready) (Val #())) {{ Ψ }}) }}
    (App (App (Val (@! client.RunLeaseCatchup)) (Val #eps)) (Val #ready))
  {{ (r : client.Result), RET #r; levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
