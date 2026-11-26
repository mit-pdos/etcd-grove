/-
`RunAuth(eps, nodes, ready)`: the auth workload of `etcd_safe` (`examples/etcd/dist/client/auth.go`; authN's run
minus its members' serving): authkv's set-up through `eps[0]` and root's barrier at every member; root's client of
`eps[0]` and u's of `eps[1 mod k]`; the four principals' `auth.Work` at their machines (`remotePrincipals`); then
root's Put of `z/end`, root's watch of every key from revision 1 up to it, checked by `auth.CheckHistory`, and u's
watch of `[a, b)`, whose every event must be a key u may read.

**The triple, over the principal service's share `PS`** (`specWith`; F7 stage S6, `notes/etcd-dist-f7.md`,
"Handoff RA-1"; the share is `remotePrincipals.specWith`'s open piece): auth on (`Γ.auth = true`, the deployment
with the token provider), the members' auth names distinct, each endpoint a valid address serving etcd's table for
a member of `Γ` (`leaseMember`), at least one; the orchestrator's shares from the start (`notes/etcd-dist-f7.md`,
"How the workloads link"): the client half of `etcdKV Γ.kv σ0` at a state with no change (the boot state) and of
`authHistView Γ.kv [srvAuthSt0]`, the KV invariant `kvInvOn γR Γ.kv srvAuthSt0` and the empty requested log's lower
bound; and the principals' share at the members' and the node addresses. It does not panic: the history check from the history
invariant every write keeps, u's check from its watch's range. It returns a `Result`, `levelTok 0` kept.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthRunDefs
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.view etcd_dist.authd

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev RunAuth.specWith
    (PS : ∀ [NetProtoGS] [github_com.mit_pdos.etcd_grove.examples.lib.remote.RemoteGS],
      DistView → ServerRaftNames → List GoString → List GoString → IProp GF) : Prop :=
  ∀ [π : NetProtoGS] [ρ : github_com.mit_pdos.etcd_grove.examples.lib.remote.RemoteGS] [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (Γ : DistView) (eps nodes : GoSlice) (addrs ns : List GoString) (ready : GoFunc) (γR : ServerRaftNames)
    (σ0 : KVState),
  -- a watch environment for the clients
  Nonempty (WEnv GF) →
  threadBound GF ≤ 2 ^ 30 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  addrs ≠ [] →
  Γ.auth = true → γR.raft.log = Γ.kv.rlog →
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) →
  (∀ cs ∈ σ0.changes, cs = []) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs ∗ nodes ↦*□ ns ∗
      ([∗list] a ∈ addrs, leaseMember (Gg := hG.goose_globalGS) Γ a) ∗
      readySpec ready ∗ kvInvOn γR Γ.kv srvAuthSt0 ∗ srvReqLogLb γR [] ∗ etcdKV Γ.kv σ0 ∗
      authHistView Γ.kv [srvAuthSt0] ∗ PS Γ γR addrs ns }}
    (App (App (App (Val (@! client.RunAuth)) (Val #eps)) (Val #nodes)) (Val #ready))
  {{ (r : client.Result), RET #r; levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
