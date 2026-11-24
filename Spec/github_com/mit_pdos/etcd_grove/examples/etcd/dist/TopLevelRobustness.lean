/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the distributed etcd theorem, stated (DRAFT)

**Two statements, drafts** (`notes/etcd-dist-plan.md`): `etcd_robust.spec` (`etcd_safe`, with crashes) and
the interim `etcd_robust_nocrash.spec` (`etcd_safe_nocrash`, no machine crashing; Q7), both over the fixed
bundle `etcdNetExts` (`[idIssueExt, fsExt at etcdFsSem, netExt]`). Built, not proved; **neither is
instantiable yet** (the opaque PLACEHOLDERs `TrustBoundary` and the boot programs, below). `etcd_safe` takes the
names `etcd_safe`/`etcd_robust` (2026-11-22, Upamanyu's naming on #24: the distributed theorems take the
plain names) of the single-process theorem it replaces (`examples/etcd/all`: eleven drivers in one
process, each on a cluster of its own; retired with leaseexpiryN's at the net swap, tag
`single-process-final`). Placeholders are marked in `TopLevelDefs.lean`.

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
the single-process `etcd_safe` until discharged, the environment premises (`EtcdEnv`) and the
trust-boundary contracts (`TrustBoundary`, a placeholder). (Until prom-registry, 2026-11-22, also the
programs' prometheus names, `HNs`: each proof now allocates its registration rights itself.)

What the single-process `etcd_safe` had and this does not: no `Hlow` (one member per process; the issue record is per
machine), no per-cluster premises (one cluster per deployment, every deployment covered), no
addresses or data directories claimed in one process (`addrsUnclaimed`, `dataDirsAbsent`: each
machine's files are its own, the network is closed), no schedules (the network's faults), no
in-process stop and restart (real crashes), no one-process resource caveat (per machine: one member's
WAL and backend). The extensions are `etcdNetExts`: the request ids' issue record, the Linux file
extension at `etcdFsSem` and the net extension (fixed: the bridge needs the bundle's ghost state,
`etcdDistGF`'s `GooseGpreS`). `ETCD_VERIFY` is off on every machine (`HEnv`, the single-process
theorems' `verifyEnvOff` per machine) with its token `envVerifyOff` a premise (`HEnvTok`: one process gets
it from the start axiom, a distributed start from no axiom; `putget_safe`'s, the owner's decision
2026-11-23); no proxy premise until phase 7 S5's HTTP client (`notes/putget-dist-plan.md` section 11).

**What the semantics assumes** (not premises: part of the semantics it is stated over; review F2,
F3):
- the file extension at `etcdFsSem` (`examples/lib/etcdstart/FsExts.lean`), not its own semantics:
  no file operation fails with an I/O error and no `flock`/`mmap` error, on every member's machine
  (one member's 64 MB WAL segment and its backend each; the descriptor limit above one member's
  files and sockets); a crash is a power loss, or a kill followed by a sync, unrestricted;
- the request ids' issue record survives a machine's crash and must tell a restarted member's
  generator from the one before the crash (today it keys generators by heap address, which a crash
  makes reusable: the extension is to be keyed by incarnation, stage D4, with its semantics example
  and an axiom review); the idutil model's clock assumption (the wall clock does not step back
  across a restart, `nonissues/etcd-request-id-restart-reuse.md`) now spans machine restarts.

**Trusted gap** (review F15): the binaries (`cmd/{server,client}`) parse a JSON file the harness
writes from the deployment; the parsing is not translated, so the boot programs are `Main` applied
to the configuration's Go value.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelDefs
public import Proof.runtime.Start
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env
public import Net.Statement.DistDeploy
public import Proof.go_etcd_io.etcd.client.v3.DialWithBalancerBody
public import Proof.log.NewModel
public import GooseLang.Ext.Net.Ghost
public import GooseLang.Ext.Fs.Ghost
public import GooseLang.Ext.IdIssue.Specs
public import Robustness.Statement

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Robustness go_etcd_io.raft.v3

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-- **`etcd_safe`** (see the file header): every well-formed deployment of an etcd cluster on
machines that may crash and restart, and of its checking clients on machines that never crash (each
workload an orchestrator machine and its client machines, D8), is robust: no thread of any machine is
stuck or has an unrecovered panic.

PLACEHOLDER binders: the programs' package `Assumptions` (of `examples/etcd/dist/{server,client}`'s
closures, stage D2) join the instance binders; `threads` and `bound` are `etcd_safe_nocrash`'s, to be
fixed by the crash proofs (the bound counts the steps of all machines together). -/
def etcd_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    -- carried over from `etcd_robust` (review F7); each to go when its model is proved
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    -- the deployment, and its one decidable premise
    (d : Deployment) (Hd : d.WellFormed)
    -- bootstrap's results; the premises not yet discharged
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : BootFacts d ps ctxs boot)
    (Henv : EtcdEnv d) (Htb : TrustBoundary d ps ctxs boot)
    -- the machines' start states
    (σs σc σn : List state) (g : GlobalState)
    (Hσs : σs.length = d.members.length ∧ ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2)
    (Hσc : σc.length = d.workloads.length ∧ ∀ σ ∈ σc, ClientStart σ)
    (Hσn : σn.length = d.nodeList.length ∧ ∀ σ ∈ σn, ClientStart σ)
    (Hg : NetStart g)
    -- `ETCD_VERIFY` off on every machine's run, and its token in the logic (`putget_safe`'s)
    (HEnv : ∀ m ∈ machines d σs σc σn, verifyEnvOff m.1)
    (HEnvTok : ⊢ envVerifyOff (GF := etcdDistGF)),
    Robust (servers d σs) (clients d σc ++ nodeMachines d σn) g (threads := 2 ^ 28)
      (bound := 2 ^ 28 - 1)

/-- **`etcd_safe_nocrash`** (the interim milestone, open question Q7): `etcd_safe`'s deployment with no
machine crashing (`Robust []` over every machine: members, orchestrators, client machines). The crash
theorem `etcd_safe` implies it; the weaker variant takes the longer name. Over Perennial's
`goose_dist_adequacy` through the bridge `Net.robust_of_distBootIL`.

**Not instantiable yet**: `TrustBoundary` is an opaque PLACEHOLDER (no deployment can discharge it) until
the k-member boot writes its premises out (each member's `Hprem`, `Hctx`, `Hcec` at `etcdDistGF`, as
`putget_safe`'s); the boot programs are PLACEHOLDERs until stage D2. The bound is `putget_safe`'s
`2 ^ 28 - 1` until perennial#690 (`goose_dist_adequacy_below`) raises both. -/
def etcd_robust_nocrash.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (Hd : d.WellFormed)
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : BootFacts d ps ctxs boot)
    (Henv : EtcdEnv d) (Htb : TrustBoundary d ps ctxs boot)
    (σs σc σn : List state) (g : GlobalState)
    (Hσs : σs.length = d.members.length ∧ ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2)
    (Hσc : σc.length = d.workloads.length ∧ ∀ σ ∈ σc, ClientStart σ)
    (Hσn : σn.length = d.nodeList.length ∧ ∀ σ ∈ σn, ClientStart σ)
    (Hg : NetStart g)
    (HEnv : ∀ m ∈ machines d σs σc σn, verifyEnvOff m.1)
    (HEnvTok : ⊢ envVerifyOff (GF := etcdDistGF)),
    Robust [] (machines d σs σc σn) g (threads := 2 ^ 28) (bound := 2 ^ 28 - 1)

end etcd_dist
end EtcdGrove
end Perennial

end
