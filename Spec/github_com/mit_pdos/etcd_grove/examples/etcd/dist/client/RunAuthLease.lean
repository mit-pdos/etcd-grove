/-
`RunAuthLease(eps, ready)`: the authLease workload of `etcd_safe` (`examples/etcd/dist/client/authlease.go`;
authlease's `run` minus its members' serving): authkv's set-up through `eps[0]` and barriers; root's lease
`Lz` holding `z/lease` (`eps[0]`); u's lease `Lu` holding `a/lease` and, by a transaction, `a/txn`
(`eps[1 mod k]`); barriers; then authlease's checks 1-5, each principal through its own member (v:
`eps[2 mod k]`), and u's revocation of `Lu`, after which root finds neither `a/lease` nor `a/txn`.

**The triple** (authlease's `run.spec`, at the cluster view `Γ`): auth on (`Γ.auth = true`, the deployment
with the token provider), revocable lease mode, the members' auth and lessor names distinct, each endpoint a
valid address serving etcd's table for a member of `Γ` (`leaseMember`), at least one; the orchestrator's
shares from the start (`notes/etcd-dist-f7.md`, "How the workloads link"): the client half of `etcdKV Γ.kv
σ0` (no `a/x` in it) and of `authHistView Γ.kv [srvAuthSt0]`, the KV invariant `kvInvOn γR Γ.kv srvAuthSt0`
and the empty requested log's lower bound. It does not panic: every check's refusal is derived from the
cluster's auth and lease facts. It returns a `Result`, `levelTok 0` kept.
Lean-first (no Rocq counterpart); F7 stage S5.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseDefs
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
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev RunAuthLease.spec : Prop :=
  ∀ [π : NetProtoGS] [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (Γ : DistView) (eps : GoSlice) (addrs : List GoString) (ready : GoFunc) (γR : ServerRaftNames)
    (σ0 : KVState),
  -- a watch environment for the clients (the workload's calls read none of it)
  Nonempty (WEnv GF) →
  threadBound GF ≤ 2 ^ 30 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  addrs ≠ [] →
  Γ.auth = true → Γ.kv.lm = .revocable → γR.raft.log = Γ.kv.rlog →
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  mvcc.findKey go!"a/x" σ0.kvs = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs ∗ ([∗list] a ∈ addrs, leaseMember (Gg := hG.goose_globalGS) Γ a) ∗
      readySpec ready ∗ kvInvOn γR Γ.kv srvAuthSt0 ∗ srvReqLogLb γR [] ∗ etcdKV Γ.kv σ0 ∗
      authHistView Γ.kv [srvAuthSt0] }}
    (App (App (Val (@! client.RunAuthLease)) (Val #eps)) (Val #ready))
  {{ (r : client.Result), RET #r; levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
