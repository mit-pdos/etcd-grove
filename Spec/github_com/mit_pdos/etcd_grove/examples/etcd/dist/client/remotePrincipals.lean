/- Lean-first (no Rocq counterpart).

`remotePrincipals(nodes)` (`examples/etcd/dist/client/nodes.go`): **the auth workload's principals at their
machines** (F7 stage S6, `notes/etcd-dist-f7.md`, "Handoff RA-1"): each principal of `auth.Principals()` is sent
to its client machine `nodes[c]` (`remote.Report` with `principalCodec`, all at once, `reportAll`), which runs
`auth.Work` through a client of its own (`principalOp`); the result counts the machines that answered.

**The triple, over the principal service's share `PS`** (`specWith`; its instance is `remotePrincipals.spec`, at
`principalsShare`, `PrincipalWire.lean`, as `writersShare` is `remoteWriters`'): from the share at the members'
client addresses `addrs` and the machines' addresses `ns`, and the principals' environment `akDistEnv addrs Γ γR`
(persistent; what each machine is given with its call), `remotePrincipals` returns, the level token threaded. The orchestrator needs nothing of the
answers: the history check rests on `akHistInv`, which every principal's write keeps.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.PrincipalWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev remotePrincipals.specWith
    (PS : ∀ [NetProtoGS] [RemoteGS], DistView → ServerRaftNames → List GoString → List GoString → IProp GF) :
    Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS] (nodes : GoSlice) (ns addrs : List GoString) (Γ : DistView) (γR : ServerRaftNames),
  threadBound GF ≤ 2 ^ 30 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ nodes ↦*□ ns ∗ PS Γ γR addrs ns ∗ akDistEnv addrs Γ γR }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remotePrincipals)) (Val #nodes))
  {{ (n : w64), RET #n; levelTok 0 }}

/-- **The triple at the principal service's share** (`principalsShare`, at the machine's global ghost state). -/
abbrev remotePrincipals.spec : Prop :=
  remotePrincipals.specWith (fun Γ γR addrs ns => principalsShare (Gg := hG.goose_globalGS) Γ γR addrs ns)

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
