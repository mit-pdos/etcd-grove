/- DRAFT (K1, 2026-11-28; not built: `notes/` is in no `lean_lib`). Proposed
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/dist/TopLevelRobustness.lean`; the packet is
`notes/k8s-dist-statement-packet.md`. Everything below the line is the file as proposed.
------------------------------------------------------------------------------------------------

Lean-first (no Rocq counterpart).

# `k8s/dist`: Kubernetes' etcd3 store and compactor over a distributed etcd cluster, stated

**`k8s_robust_nocrash.spec`** (`k8s_safe_nocrash`), over the fixed bundle `etcdNetExts`
(`[idIssueExt, fsExt at etcdFsSem, netExt]`). Not proved yet.

**For every deployment** of one etcd cluster and two Kubernetes workloads over it -- `k ≥ 1` members,
each running etcd-dist's `server` on a machine of its own; the **store** workload (an orchestrator and
`Apiservers` API server machines, each Kubernetes' etcd3 storage over its own `kubernetes.Client`); the
**compactor** workload (an orchestrator, a writer machine and API server machines running Kubernetes'
compactor, own and shared) -- with **no machine crashing**, **in every execution** of Perennial's
distributed semantics (any interleaving, every fault the net extension allows: bytes delayed, a
direction cut at any read or write, a dial refused; a partition is such an execution) of fewer than
`etcdSteps` (`2 ^ 48`) steps along which every machine keeps fewer than `etcdThreads` (`2 ^ 28`) live
threads, **no thread of any machine is stuck or has an unrecovered panic**. Both workloads use the
cluster at once: the compactor's writes are foreign revisions in the store's history and its
compactions run while the store serves.

**What panics** (so does not happen):
- the store's orchestrator (`RunStore`): porcupine finds the store's history not linearizable against
  the driver's model with foreign revisions (`SharedModel`, its lazy, eager and full modes in turn, the
  full mode's verdict final); Kubernetes' checker rejects the history, on a run where it applies (no
  failed call, no compacted error, every raw answer carried, no foreign revision: rare on one cluster);
  an etcd "compacted" error on an operation that reads at no old revision (neither `PastRead` nor
  `PinnedRead`: a Get, a write, a List of one page at the latest revision);
- an API server machine of the store: its store cannot be made (`NewStoreOnly`);
- the compactor's orchestrator (`CheckLog`): an API server's compactor revision decreases or runs ahead
  of the cluster's.
A porcupine or checker timeout (`CheckTimeout`) returns: such a run checks nothing.

**The two bounds**: etcd-dist's `etcdThreads` and `etcdSteps` (`TopLevelDefs.lean` of `etcd/dist`): the
same server, the same caps; the k8s programs add no lifetime counter (the store's revisions are the
cluster's, under mvcc's `2 ^ 48`).

**The deployment is not a premise.** Every machine's program receives the whole deployment as a Go
value and checks it first: the members etcd-dist's `deployment.WellFormed` of the cluster, the other
machines `dist.WellFormed` (etcd-dist's, with no auth, no etcd compactor and no etcd workload; the
store's sizes, `1 ≤ Apiservers ≤ Clients + Watchers < 2^31`; at least one compactor round; every client
machine address valid, distinct, and none a member's), returning at once if it fails; `TestWellFormed`
and `TestDist` (`examples/k8s/dist`) show the check passes on random deployments, rejects malformed
ones, and the real path runs.

**The premises** are `etcd_safe_nocrash`'s, at the cluster: start states (`ServerStart`,
`ClientStart`), bootstrap's log (`BootFacts`), the environment and workload premises (`EtcdEnv`),
`ETCD_VERIFY` off, `GODEBUG` `fips140` off; and the instance binders (the translations' `Assumptions`
classes and models). No function contract is a premise.

**What the semantics assumes**: the file extension at `etcdFsSem` (no I/O error, no `flock`/`mmap`
error on any machine). **Trusted**: the translations, the package assumptions bound below, the
extensions, and the axioms of `etc/tcb-collections/k8s-dist.txt` (the `_dist` client axioms, among
them the error arms of `notes/k8s-dist-statement-packet.md` §2, and `RealClock.After`'s contract).
**Trusted gap**: the binaries (`cmd/*`) parse a JSON file the harness writes; the boot programs are the
entry points applied to the deployment's Go value.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.TopLevelDefs
public import Proof.runtime.Start
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env
public import Net.Statement.DistDeploy
public import Proof.log.NewModel
public import GooseLang.Ext.Net.Ghost
public import GooseLang.Ext.Fs.Ghost
public import GooseLang.Ext.IdIssue.Specs
public import Robustness.Statement
public import Perennial.TrustedCode.crypto.fips140

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open Robustness go_etcd_io.raft.v3 etcd_dist

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-- **`k8s_safe_nocrash`** (see the file header): every deployment of an etcd cluster and of the
Kubernetes store and compactor workloads over it, no machine crashing, is robust: no thread of any
machine is stuck or has an unrecovered panic. -/
def k8s_robust_nocrash.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    -- the members: etcd-dist's server, unchanged
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]
    -- etcd-dist's client helpers the k8s programs call (`AwaitCluster`, `Rotate`, `ConnectRetry`, ...)
    [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    -- the k8s programs (K3 fixes the closure's classes this one does not bundle)
    [k8s_sem : github_com.mit_pdos.etcd_grove.examples.k8s.dist.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    -- the deployment (checked by the programs, not a premise)
    (d : Deployment)
    -- bootstrap's log at Go's peers and contexts of the cluster; the environment and workload premises
    (boot : List LogEntry) (Hbf : BootFacts d.cluster boot)
    (Henv : EtcdEnv d.cluster)
    -- the machines' start states: members, orchestrators (store, compactor), client machines
    (σs σo σn : List state) (g : GlobalState)
    (Hσs : σs.length = d.cluster.members.length ∧ ∀ p ∈ d.cluster.members.zip σs, ServerStart p.1 p.2)
    (Hσo : σo.length = orchCount ∧ ∀ σ ∈ σo, ClientStart σ)
    (Hσn : σn.length = d.nodeCount ∧ ∀ σ ∈ σn, ClientStart σ)
    -- `ETCD_VERIFY` off (the deployment's value of the variable enables no check)
    (HEnv : EtcdVerifyOff)
    -- the run's `fips140` GODEBUG setting off (`crypto/sha1`, which every program's check of the
    -- deployment computes the member ids with, panics in `fips140=only`)
    (Hfips : crypto.fips140.GodebugFips140Off),
    Robust [] (machines d σs σo σn) g (threads := etcdThreads) (bound := etcdSteps)

end k8s_dist
end EtcdGrove
end Perennial

end
