/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the distributed etcd theorem, stated (DRAFT)

**Draft for review** (`notes/etcd-dist-plan.md`): not built, not proved, nothing imports it. It is to
replace `etcd_robust`/`etcd_safe` (`examples/etcd/all`: eleven drivers in one process, each on a
cluster of its own) and leaseexpiryN's theorem. Placeholders are marked in `TopLevelDefs.lean`.

**For every well-formed deployment** of one etcd cluster and its clients -- `k ≥ 1` members, each
running `examples/etcd/dist/server` on a machine of its own **that may crash at any step and
restart** (with the same program, from the files the Linux file extension's crash relation keeps:
a power loss, or a kill followed by a sync), and client machines **that never crash**, each running
`examples/etcd/dist/client` with one workload (KV with porcupine, watch, watch cache, compaction,
auth, auth's lease rows, lease reads, lease catch-up, lease expiry, durability) against the members'
client addresses -- on a network with no connection at the start, **in every execution** of
Perennial's distributed semantics (any interleaving, any crash of any member, every fault the net
extension allows: bytes delayed, a direction cut at any read or write, a dial refused; a partition
is such an execution) of fewer than `bound` steps along which every machine keeps fewer than
`threads` threads, **no thread of any machine is stuck or has an unrecovered panic**. Each client
panics if its check fails, so no check fails.

The premises: the deployment is well formed (`Deployment.WellFormed`, decidable: names, `addrOk`
addresses, distinct, the members' ids apart in their low bits, the server configuration in its
supported set, the workloads compatible and within their bounds); the machines start as the programs
expect (`ServerStart`: no listener, the member's data directory and WAL area empty; `ClientStart`; a
network with no connection, `NetStart`); bootstrap's results (`BootFacts`); and, carried over from
`etcd_safe` until discharged, the environment premises (`EtcdEnv`), the programs' prometheus names
(`HNs`) and the trust-boundary contracts (`TrustBoundary`, a placeholder).

What `etcd_safe` had and this does not: no `Hlow` (one member per process; the issue record is per
machine), no per-cluster premises (one cluster per deployment, every deployment covered), no
addresses or data directories claimed in one process (`addrsUnclaimed`, `dataDirsAbsent`: each
machine's files are its own, the network is closed), no schedules (the network's faults), no
in-process stop and restart (real crashes), no one-process resource caveat (per machine: one member's
WAL and backend). The extensions are any list holding the net extension, the Linux file extension
and the request ids' issue record, each with its own semantics (`HasExt`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelDefs
public import Proof.runtime.Start
public import Robustness.Statement

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Robustness

/-- **`etcd_dist_safe`** (see the file header): every well-formed deployment of an etcd cluster on
machines that may crash and restart, and of its checking clients on machines that never crash, is
robust: no thread of any machine is stuck or has an unrecovered panic.

PLACEHOLDER binders: the programs' package `Assumptions` (of `examples/etcd/dist/{server,client}`'s
closures, stage D2) join the instance binders; `threads` and `bound` are `etcd_safe`'s, to be fixed
by the proofs (the bound counts the steps of all machines together). -/
def etcd_dist_safe.spec : Prop :=
  ∀ [GooseExts] [GooseSemantics] [HasExt Net.netExt] [HasExt Fs.fsExt] [HasExt idIssueExt]
    [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    -- the deployment, and its one decidable premise
    (d : Deployment) (Hd : d.WellFormed)
    -- bootstrap's results; the premises not yet discharged
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : BootFacts d ps ctxs boot)
    (Henv : EtcdEnv d) (Htb : TrustBoundary d ps ctxs boot)
    (HNs : (∀ m ∈ d.members, prometheus.namesUnclaimed (serverProg d m) serverNames) ∧
      ∀ w ∈ d.workloads,
        prometheus.namesUnclaimed (clientProg w (d.members.map Member.client)) clientNames)
    -- the machines' start states
    (σs σc : List state) (g : GlobalState)
    (Hσs : σs.length = d.members.length ∧ ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2)
    (Hσc : σc.length = d.workloads.length ∧ ∀ σ ∈ σc, ClientStart σ)
    (Hg : NetStart g),
    Robust (servers d σs) (clients d σc) g (threads := 2 ^ 28) (bound := 2 ^ 40 - 11)

end etcd_dist
end EtcdGrove
end Perennial

end
