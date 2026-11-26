/- Lean-first (no Rocq counterpart).

# `etcd/dist/kvremote`: M1, `etcd_kv_safe_nocrash`, stated

**`etcd_kv_safe_nocrash.spec` is `etcd_robust_nocrash.spec` (`etcd_safe_nocrash`,
`Spec/.../etcd/dist/TopLevelRobustness.lean`) with one more premise, the scope `Hscope : KvOnly d ∧
d.cfg.auth = false`.** Its binders, premises and conclusion are the full statement's, in the same
order, written with the same definitions (`TopLevelDefs.lean`: `BootFacts`, `EtcdEnv`, `ServerStart`,
`ClientStart`, `machines`, `etcdThreads`, `etcdSteps`). `etcd_kv_safe_nocrash_of_full`
(`Proof/.../dist/kvremote/TopLevelRobustness.lean`) proves that the full statement implies this one, so
the two cannot drift apart. It is the weaker variant, so it has the longer name.

**For every deployment of the scope**: `k ≥ 1` members, each running `examples/etcd/dist/server` on a
machine of its own, and per workload (all of kind `kv`) an orchestrator machine (`client.Orchestrator`:
`kvremote.Orch`, porcupine's check of txnlin's model) and its client machines (`client.NodeDeployment`:
`kvremote.Node`, each a clientv3 client of the members' client addresses). No machine crashes. **In every
execution** of Perennial's distributed semantics over `etcdNetExts` with fewer than `etcdSteps` steps,
along which every machine keeps fewer than `etcdThreads` live threads, **no thread of any machine is stuck
or has an unrecovered panic**. The orchestrator panics if its linearizability check fails, so the check
never fails.

**The scope** (`Hscope`) is decidable and is over the Go deployment value:
- `KvOnly d` (`Proof/.../dist/client/KvDefs.lean`): every workload has kind `kv`
  (`deployment.KV`, kind `0`): `∀ w ∈ d.workloads, w.kind = W64 0`;
- `d.cfg.auth = false`: the members run with auth off (`deployment.ServerCfg.Auth`). The interim
  contracts the kv calls rest on (`KV_Put_dist`, `KV_Delete_dist`, `Txn_Commit_dist`, `Serve_dist`)
  are for members with auth off.

No other premise is added. The deployment is still checked by the programs, not by a premise: a
malformed deployment of the scope is covered too, with every machine returning after its check.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Robustness go_etcd_io.raft.v3

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-- **`etcd_kv_safe_nocrash`** (M1; see the file header): `etcd_robust_nocrash.spec` at the deployments
whose workloads are all `kv` and whose members run with auth off. -/
def etcd_kv_safe_nocrash.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel] [net.FieldAssumptions]
    (d : Deployment)
    -- M1's scope (the only premise beyond `etcd_robust_nocrash.spec`'s)
    (Hscope : KvOnly d ∧ d.cfg.auth = false)
    (boot : List LogEntry) (Hbf : BootFacts d boot)
    (Henv : EtcdEnv d)
    (σs σc σn : List state) (g : GlobalState)
    (Hσs : σs.length = d.members.length ∧ ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2)
    (Hσc : σc.length = d.workloads.length ∧ ∀ σ ∈ σc, ClientStart σ)
    (Hσn : σn.length = d.nodeList.length ∧ ∀ σ ∈ σn, ClientStart σ)
    -- `ETCD_VERIFY` off (the deployment's value of the variable enables no check)
    (HEnv : EtcdVerifyOff)
    -- the run's `fips140` GODEBUG setting off (Perennial's environment premise: `crypto/sha1`, which
    -- the programs' check of the deployment computes the member ids with, panics in `fips140=only`)
    (Hfips : crypto.fips140.GodebugFips140Off),
    Robust [] (machines d σs σc σn) g (threads := etcdThreads) (bound := etcdSteps)

end etcd_dist
end EtcdGrove
end Perennial

end
