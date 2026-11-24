/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the distributed etcd theorem, stated (DRAFT)

**Two statements, drafts** (`notes/etcd-dist-plan.md` §11-§13): `etcd_robust.spec` (`etcd_safe`, with
crashes) and the interim `etcd_robust_nocrash.spec` (`etcd_safe_nocrash`, no machine crashing; Q7), both
over the fixed bundle `etcdNetExts` (`[idIssueExt, fsExt at etcdFsSem, netExt]`). Built, not proved; **not
instantiable yet**: the boot programs are opaque PLACEHOLDERs until stage D2 translates
`examples/etcd/dist/{server,client}`. `etcd_safe` takes the plain name (2026-11-22, the naming on #24) of
the single-process theorem it replaces (`examples/etcd/all`, now `etcd_safe_single_process`).

**For every deployment** of one etcd cluster and its clients -- `k ≥ 1` members, each running
`examples/etcd/dist/server` on a machine of its own **that may crash at any step and restart** (with the
same program, from the files the Linux file extension's crash relation keeps: a power loss, or a kill
followed by a sync), and, per workload, an orchestrator machine and its client machines **that never
crash** (`examples/etcd/dist/client`: KV with porcupine, watch, watch cache, compaction, auth, auth's
lease rows, lease reads, lease catch-up, lease expiry, durability) against the members' client
addresses -- **in every execution** of Perennial's distributed semantics (any interleaving, any crash of
any member, every fault the net extension allows: bytes delayed, a direction cut at any read or write, a
dial refused; a partition is such an execution) of fewer than `bound` steps along which every machine
keeps fewer than `threads` threads, **no thread of any machine is stuck or has an unrecovered panic**.
Each client panics if its check fails, so no check fails.

**The deployment is not a premise.** Every machine's program receives the whole deployment and checks
it first (Go's `deployment.WellFormed`, mirrored by Lean's `Deployment.WellFormed`: names, `addrOk` addresses,
distinct, the members' ids apart in their low bits, the server configuration in its supported set, the
workloads compatible and within their bounds), returning at once if it fails; `TestWellFormed` and
`TestDist` show the check passes on random deployments and the real path runs.

**The premises**, classified:
- *start states* (deployment facts): `ServerStart` (the member's files as on disk, `FsInit`, its data
  directory and WAL area empty) and `ClientStart` (`FsInit`). The rest of the start (fresh processes, no
  listener, no connection) is `Robust`'s own (`extsInitLocal`/`extsInitGlobal`). `FsInit` goes into the
  semantics if `fsSemWithS` gets the file extension's `initLocal` (stage D4a, a trusted change);
- *bootstrap's results*, `BootFacts` (pure, carried from every etcd theorem): the peers, contexts and
  bootstrap log the members compute. To be retired when they are Lean functions of the deployment and
  `bootstrap` has its spec (premises-to-axioms item A/K, #34);
- *environment and workload*, `EtcdEnv` (carried from the single-process theorems: `authRecordsFit`,
  `backendUnderQuota`, `grpcRepliesFit`, `diskOk`, `leasePeersOk`, conditional `leasesNoExpiry`; its
  `peerRequests` field is `True`, a PLACEHOLDER until phase 7 S5);
- *`ETCD_VERIFY` off*, `HEnv` on every machine (approved 2026-11-23) and its token `HEnvTok` (the
  single-process start gives it by its start axiom; premises-to-axioms item G, an adequacy decision).
- *`GODEBUG` `fips140` off*, `Hfips` (Perennial's `GodebugFips140Off`, approved: `crypto/sha1` panics in
  `fips140=only` mode; every program's check of the deployment computes the member ids with it).
- the instance binders: the Goose translations' `Assumptions` classes and models, as the single-process
  theorems' (and, after D2, the `dist` packages' own).

**Not in the statement** (2026-11-24): no Iris premise of a function contract (`Hprem`, `Hctx`, `Hcec`,
the draft's `TrustBoundary`): each is a per-function axiom in the function's own file, or a theorem
(premises-to-axioms plan); no `WellFormed` (the programs check it); no `NetStart` (in `Robust`); no
prometheus names (prom-registry).

What the single-process `etcd_safe` had and this does not: no `Hlow` (one member per process), no
per-cluster premises, no addresses or data directories claimed in one process (`addrsUnclaimed`,
`dataDirsAbsent`), no schedules (the network's faults replace `cluster3`'s partitioner and the
`third_party/bridge` relay, and with them `bridge.New`'s axioms), no in-process stop and restart (real
crashes), no one-process resource caveat.

**What the semantics assumes** (not premises: part of the semantics it is stated over; review F2, F3):
- the file extension at `etcdFsSem` (`examples/lib/etcdstart/FsExts.lean`): no file operation fails with
  an I/O error and no `flock`/`mmap` error, on every member's machine; a crash is a power loss, or a kill
  followed by a sync, unrestricted;
- the request ids' issue record survives a machine's crash and must tell a restarted member's generator
  from the one before the crash: today it keys generators by heap address and has no crash
  interpretation, so the crash statement is **not provable over today's extension**; stage D4b keys it by
  incarnation (a trusted change with its semantics example and an axiom review). The idutil model's clock
  assumption (the wall clock does not step back across a restart,
  `nonissues/etcd-request-id-restart-reuse.md`) then spans machine restarts.

**Trusted gap** (review F15): the binaries (`cmd/{server,client}`) parse a JSON file the harness writes
from the deployment; the parsing is not translated, so the boot programs are the `Main`s applied to the
deployment's Go value.
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
public import Perennial.TrustedCode.crypto.fips140

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Robustness go_etcd_io.raft.v3

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-- **`etcd_safe`** (see the file header): every deployment of an etcd cluster on machines that may
crash and restart, and of its checking clients on machines that never crash (each workload an
orchestrator machine and its client machines, D8), is robust: no thread of any machine is stuck or has
an unrecovered panic.

The bound is
`etcd_safe_nocrash`'s until the crash proof fixes its own (kvnet's crash theorem has `2 ^ 61`). -/
def etcd_robust.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    -- carried over from the single-process theorems (review F7); each to go when its model is proved
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    -- the deployment (checked by the programs, not a premise)
    (d : Deployment)
    -- bootstrap's results; the environment and workload premises not yet discharged
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : BootFacts d ps ctxs boot)
    (Henv : EtcdEnv d)
    -- the machines' start states: members, orchestrators, client machines
    (σs σc σn : List state) (g : GlobalState)
    (Hσs : σs.length = d.members.length ∧ ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2)
    (Hσc : σc.length = d.workloads.length ∧ ∀ σ ∈ σc, ClientStart σ)
    (Hσn : σn.length = d.nodeList.length ∧ ∀ σ ∈ σn, ClientStart σ)
    -- `ETCD_VERIFY` off on every machine's run, and its token in the logic (`putget_safe`'s)
    (HEnv : ∀ m ∈ machines d σs σc σn, verifyEnvOff m.1)
    (HEnvTok : ⊢ envVerifyOff (GF := etcdDistGF))
    -- the run's `fips140` GODEBUG setting off (Perennial's environment premise: `crypto/sha1`, which
    -- the programs' check of the deployment computes the member ids with, panics in `fips140=only`)
    (Hfips : crypto.fips140.GodebugFips140Off),
    Robust (servers d σs) (clients d σc ++ nodeMachines d σn) g (threads := 2 ^ 28)
      (bound := 2 ^ 28 - 1)

/-- **`etcd_safe_nocrash`** (the interim milestone, open question Q7): `etcd_safe`'s deployment with no
machine crashing (`Robust []` over every machine: members, orchestrators, client machines). The crash
theorem `etcd_safe` implies it; the weaker variant takes the longer name. Over Perennial's
`goose_dist_adequacy` through the bridge `Net.robust_of_distBootIL`. The bound is `putget_safe`'s. -/
def etcd_robust_nocrash.spec : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (d : Deployment)
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : BootFacts d ps ctxs boot)
    (Henv : EtcdEnv d)
    (σs σc σn : List state) (g : GlobalState)
    (Hσs : σs.length = d.members.length ∧ ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2)
    (Hσc : σc.length = d.workloads.length ∧ ∀ σ ∈ σc, ClientStart σ)
    (Hσn : σn.length = d.nodeList.length ∧ ∀ σ ∈ σn, ClientStart σ)
    (HEnv : ∀ m ∈ machines d σs σc σn, verifyEnvOff m.1)
    (HEnvTok : ⊢ envVerifyOff (GF := etcdDistGF))
    -- the run's `fips140` GODEBUG setting off (Perennial's environment premise: `crypto/sha1`, which
    -- the programs' check of the deployment computes the member ids with, panics in `fips140=only`)
    (Hfips : crypto.fips140.GodebugFips140Off),
    Robust [] (machines d σs σc σn) g (threads := 2 ^ 28) (bound := 2 ^ 28 - 1)

end etcd_dist
end EtcdGrove
end Perennial

end
