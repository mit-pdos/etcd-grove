# `etcd_dist_safe`: etcd as a distributed deployment (plan, DRAFT for review)

2026-11-21. Branch `etcd-dist`. A draft for the user and upamanyus (etcd-grove#24): a plan, the
statement and its definitions, no proofs. Files:

- the statement: `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TopLevelRobustness.lean`
  (`etcd_dist_safe.spec`);
- its definitions: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TopLevelDefs.lean`
  (`Deployment`, `WellFormed`, `Workload`, `Compatible`, `ServerCfg.Supported`, the start states,
  `EtcdEnv`; placeholders marked `PLACEHOLDER`);
- the Go sketches: `examples/etcd/dist/{server,client}/` and `cmd/{server,client}/` (build tag
  `etcddist_sketch`, so no build sees them; the client calls driver functions that do not exist yet).

Neither Lean file is built (they import the server's proof cone, and the draft has placeholders for
what is not translated yet).

## 1. The statement

**Paper sentence** (two lines):

> For every well-formed deployment of an etcd cluster, with each member on a machine that may crash
> and restart at any step and each client on a machine running a self-checking workload, over a
> network that may delay, cut or refuse any connection, no machine ever panics, so no client's
> linearizability, watch, auth or lease check fails.

**In prose.** Quantify over a deployment `d`: one cluster of `k ≥ 1` members (names, peer and
client addresses, the token), its server configuration `d.cfg`, and a list of workloads, one per
client machine. Under `d.WellFormed` (decidable), the machines' start states (each member's machine:
no listener, files as on disk, its data directory and WAL area empty; each client's: no listener;
the network: no connection), bootstrap's results, and the premises carried over from `etcd_safe`
until they are discharged (§5), the deployment is `Robust`:

    Robust (servers d σs) (clients d σc) g (threads := 2^28) (bound := 2^40 - 11)

`servers d σs` are the members' machines, each running `server.Main(cfg_m)`, in `Robust`'s
`crashing` list: a crash at any step, then the same boot program from what the file extension's
crash relation keeps. `clients d σc` are the client machines, each running `client.Main(w, eps)`, in
`stable`: never crash, so a client keeps its history. `threads`/`bound` are `etcd_safe`'s, to be fixed by
the proofs (the bound counts every machine's steps together).

The extensions are any list holding the net extension, the Linux file extension and the request
ids' issue record (`[HasExt Net.netExt] [HasExt Fs.fsExt] [HasExt idIssueExt]`), as `kvnetRobust`.

## 2. Machines and programs

**The server** (`examples/etcd/dist/server`): `Main(c Config)` with `Config = {Name, Peer, Client,
Cluster []Peer, Token, CompactorMode, Retention, SnapCount, CatchUp, Auth}`. It is etcdstart's
`newServerMode` + `NewMember` + `Serve` with the configuration a parameter: build the member
(`etcdserver.NewServer`), serve its raft handler on its peer listener with `http.Server.Serve`, start
it, serve `v3rpc.Server` on its client listener with `grpc.Server.Serve`, then sleep forever. The
same `Main` is the boot program after a crash: `NewServer` finds the WAL (bootstrap's `haveWAL`) and
restarts the member; the initial cluster and token are then ignored by etcd. It first clears the
proxy variables and `ETCD_VERIFY` (`clearProxyEnv`: §4 and Q10). The binary (`cmd/server`) reads the
`Config` as JSON; the Lean boot program is `Main` applied to the `Config`'s Go value (the parsing is
not translated).

**The models' limits** (upamanyus, etcd-grove#24, at `715d5e6753`; a program outside them panics with
`NotModelled`): grpc with insecure credentials only, no TLS, no compression, `grpc.Server.Serve` on the
program's own listener (no `ServeHTTP`; a cmux split works), service config round robin or none,
resolvers passthrough/dns with IP literals/`resolver/manual`, no binary logging or channelz, keepalive
accepted and inert; **no stats handler** until S1 (but `v3rpc.Server` installs `otelgrpc`'s: U2);
net/http's server is Go's real one, served with `http.Server.Serve`; its client (`RoundTrip`, chunked
bodies) only at S5, so the member-to-member path lands last; addresses `addrOk`, one listener each.
The sketches follow these (`etcdstart.NewClients` sets keepalive, which is harmless and relied on
for nothing).

**The clients** (`examples/etcd/dist/client`): `Main(w Workload, eps []string)`, one workload per
machine, each today's driver without its start (no `StartMembers`, bridges, partitioner, `CutPeer`,
`HardStop`): each driver is split into its start and a `Run(eps, …)` (stage D1). Workloads that pick
a member use `eps[i mod k]`. Every checker follows the model's rules (etcd-grove#24): any non-OK
gRPC error is an unknown outcome, never "not applied"; a server stream's clean end is never taken as
complete (`etcdstart.Collect` already reads until a revision, not until the channel ends); nothing
relies on keepalive. Each workload writes only under its own key prefix (kv's List ranges inside
it), and clears the proxy variables as the server does. The server serves clients only after
`<-s.ReadyNotify()` (review F4: after a power loss the backend may lag the WAL until the replay).

| Workload | From | Check (panics if it fails) | Writes keys / needs sole writer / alone |
|---|---|---|---|
| `kv clients ops` | txnlinfaultsN / partition `Check` | porcupine, txnlin's model | yes / **yes** / no |
| `watch writers ops` | partition `MainWatch` | `etcdstart.Check`: exactly the writes, gap-free revisions | yes / **yes** / no |
| `cache writers ops` | cache | the same, through the watch cache, plus progress and Get | yes / **yes** / no |
| `compact` | compactwatch | latest reads never compacted, old reads exact or `ErrCompacted` | yes / no / no (not under the periodic compactor) |
| `putget` | compacted | Get after Put returns it | yes / no / no |
| `auth` | authN | principals' rights at every member | yes / yes / **yes** (enables auth) |
| `authLease` | authlease | lease rows of auth | yes / yes / **yes** |
| `leaseRead` | leaseN | listings without duplicates, TimeToLive about the lease asked | no / no / no |
| `leaseCatchup` | leasecatchup | the member that granted lists the lease once caught up | no / no / no |
| `leaseExpiry` | leaseexpiryN | a lease gone from a listing is never listed again | no / no / no |
| `durable puts` | restartN / restart1 | acknowledged Puts present at version 1, other keys only attempted ones; ≤ 256 Puts | yes / no / no |

**Clients on separate machines (the user, 2026-11-21).** Every client is its own process, as in dsverify-lab's
distributed setup (the user's design: dsverify-lab `notes/clients-separate-nodes.md`,
`harness/lean/Harness/Remote.lean`, `Harness/Remote/`). A workload with several clients (kv, watch, the
lease workloads) is an **orchestrator** machine running `remote.RunRemote` plus one machine per client
running `remote.ServeClient`. The orchestrator issues each client's operations as remote calls, records the
history and runs the check (porcupine for kv). The generic lemma `remoteDistSafe` is proved there. Why this
form: a proof cannot exploit clients that share a process (a prophecy cannot cross machines; the note's §2).
The harness pieces are ours (etcd-grove#24, 2026-11-21 22:22Z: phase 6 has not started and moved them to this
claim). Most need no port: porcupine is verified here (`Proof/github_com/anishathalye/porcupine/`, no axiom), so
dsverify's porcupine axiom is replaced by that proof; the driver and recorder are `examples/lib/lintest`
(proved: `Run` never returns `Illegal` when `apply` is logically atomic), and `examples/raft/kvnet/kvcheck` (#22)
is the closest existing `ServeClient`-like node. So the port is the orchestration (`RunRemote`, `ServeClient`)
over `lintest`/`kvcheck` and the net extension, in a neutral home, `examples/lib/remote`, which phase 6's kits
will reuse.
The workload table's "one machine per workload" (§2) becomes "one orchestrator plus k_c client machines per
workload"; single-client workloads (putget, compact, durable) stay one machine.

## 3. The configuration set

`ServerCfg = {compactor : off | revision r | periodic p, snapCount, catchUp, auth : Bool}`, the same at
every member; `Supported`: `r ≥ 1`, `p ≥ 10 ns`, `snapCount, catchUp ≥ 1`, all within Go's integers.
That covers what the eleven drivers use (compactwatch's revision/1, compacted's and cache's periodic
10 ms, snapshots 1/1 or none, auth on or off) and everything between. `auth` is the token provider
(`AuthToken: "simple"`, TTL 300); enabling auth is a client's act (the `auth`/`authLease` workloads),
not the server's. The other `ServerConfig` fields stay the examples' fixed values (Q9).

## 4. The deployment predicate (`Deployment.WellFormed`, decidable)

1. a member; names distinct and `nameOk` (ASCII letters, digits, `-`: one data directory each);
2. every address the net extension's `addrOk` (canonical `a.b.c.d:p`, first octet 1-223, port outside
   32768-60999), the `2k` peer and client addresses distinct (one listener per address);
3. the member ids' 16 low bits distinct and nonzero (`BootCore`'s `lowNodup`/`lowNz`: request ids carry
   them, and a member applies other members' entries), and their 15 low bits distinct when a workload
   grants leases (`leaseIdsApart`);
4. a nonempty token; `cfg.Supported`;
5. the workloads `Compatible` (at most one of each kind; `auth`/`authLease` alone; a workload that
   reads revisions as its own beside none that writes keys; never `leaseExpiry` beside a workload
   that needs no lease to expire) and within their bounds; `cfg.auth` if a workload needs the token
   provider; `compact` not under the periodic compactor; no token provider beside `leaseExpiry`
   (the revocable lease mode with auth needs `leasesNoExpiry`).

**Decidability.** Every conjunct is decidable (`instance : Decidable d.WellFormed`). Evaluating it
by `decide` needs `memberId` (etcd's SHA-1 of the peer URL and token) to be a Lean definition: a
placeholder `opaque` now (Q5). **The proxy** (#24): with non-loopback addresses Go's
`ProxyFromEnvironment` would send rafthttp's requests to a proxy. Recommended: the server clears
`HTTP_PROXY`/`HTTPS_PROXY`/`NO_PROXY` (and the lower-case forms, and `ETCD_VERIFY`) before anything
reads them (`clearProxyEnv`), which puts the fact in the program, where it is verified, and retires
`verifyEnvOff` with it. It needs specs of `os.Unsetenv`/`os.Getenv` over a machine-local environment
(Perennial). The alternative is a fork change, rafthttp's transport with `Proxy: nil`, which leaves
`ETCD_VERIFY` a premise.

## 5. What is still not decidable (carried from `etcd_safe`)

| Premise | Now | Path to remove it |
|---|---|---|
| `BootFacts d ps ctxs boot` | parameters with facts | a function of `d`, once `memberId` and the boot log's encoding are Lean definitions |
| `EtcdEnv`: `authRecordsFit`, `backendUnderQuota`, `grpcRepliesFit` | opaque workload premises | decidable bounds on the workloads (sizes, op counts), proved from the clients' code: each needs its own argument (`grpcRepliesFit` from the client's request shapes; quota from bytes written, hard without compaction) |
| `EtcdEnv.disk` (`storage.diskOk`) | opaque | proved over the file extension (as the WAL's were, wal-link L3) |
| `EtcdEnv.leasePeers` (`leasePeersOk`) | opaque | **true by construction** here (every peer address is a member's raft handler): proved once rafthttp's server side is over the net/http model (phase 7 S5) |
| `EtcdEnv.noExpiry` | `needsNoExpiry → leasesNoExpiry` | as today (MaxLeaseTTL), or proved without it (research) |
| `HNs` (prometheus names) | per program, axiomatized Prop | D19d's registry extension |
| `HEnv` (`verifyEnvOff`, and no proxy variables) | per program | the programs clear them (`clearProxyEnv`) with specs of the environment (Q10) |
| `EtcdEnv.peerRequests` | PLACEHOLDER (`addrsUnclaimed`'s part (b): etcd's names-only peer requests reach only the raft mux) | those clients translated over the net extension (phase 7 S5) |
| the semantics' assumptions (not premises) | `etcdFsSem`: no I/O, `flock` or `mmap` error, per machine; the issue record across crashes | — (disclosed in the statement's header) |
| `TrustBoundary` (today's `Hprem`, `Hctx`, `Hcec`) | PLACEHOLDER | Iris premises at the proof's ghost state have no place here: each becomes a reviewed axiom or a theorem (bootstrap over the real code; context's facts in Perennial, item 8) |

## 6. Where today's results go

| Today | In `etcd_dist_safe` | Changes | Loses | Gains |
|---|---|---|---|---|
| `etcd_safe` KV: txnlinfaultsN (`k₁ ≤ 1000`, schedule) | `kv` | partitions are the network's; clients dial members directly | `CutPeer`/`MendPeer` and the bridge's paths (test-only code) | every partition and fault, at any `k` the predicate admits, with crashes |
| partition `MainWatch` | `watch` (exclusive) | as above | — | crashes |
| compactwatch, compacted, cache | `compact`, `putget`, `cache` (exclusive) | the compactor is `cfg.compactor` | — | any compactor setting in the supported set, multiple members |
| authN, authlease (`k ≤ 300`) | `auth`, `authLease` (exclusive; `cfg.auth`) | — | — | no 300 bound |
| leaseN, leasecatchup | `leaseRead`, `leaseCatchup` | leasecatchup's cut is the network's (a catch-up by snapshot is one execution) | the guarantee the run takes that path (only the harness makes it likely) | any `k` |
| restartN, restart1 | `durable` + crashes | a real crash (power loss, or kill and sync) instead of `HardStop` in one process; Puts through gRPC, not the server's own API | the graceful stop's path (`HardStop`, `raftSwap`); the exact revision check (other clients write) | crash at any step of any member, any number of times |
| leaseexpiryN (own theorem, N1) | `leaseExpiry`, folded in | the `leasesNoExpiry` premise is conditional on the workloads, and `Compatible` keeps it apart from `authLease`/`leaseCatchup` | — | one theorem (recommended; Q2) |
| `Hlow` | **gone** | one member per process; the issue record is per machine | — | no cross-cluster token search |
| `addrsUnclaimed`, `dataDirsAbsent`, `HWal` over 2,210 dirs | gone / per machine | closed deployment over the net extension; each machine's files its own | — | no world assumption about other processes |
| one-process caveat (141 GB, millions of fds) | per machine: one member | — | — | — |
| `k8s_safe` | later, the same shape: members on `server` machines, API servers and the compactor's checkers as further machine kinds | `Deployment` gains machine kinds | — | the members' crashes |
| raft rows (kv, kvdurable, kvreconf) | `kvnetRobust`'s shape (replicas crash, one checking client) | kvnet is raft's distributed row | — | — |
| `RaftTla`, `RaftWitness`, `RaftNoAx`, WAL tester | stay single-process | — | — | — |

## 7. What the proof needs, and what exists

1. **The transport over the net extension** (upamanyus's phase 7, `notes/phase7-plan.md`): gRPC unary
   and streams (S2, S3) for clientv3 ↔ v3rpc; the deployment's addresses from `addrOk` instead of
   `addrsUnclaimed`/`netAddrFree` (S4); rafthttp's server side over Go's real `http.Server` and its client
   side (`Transport.RoundTrip`, chunked bodies: S5, last). **Blocking the server program as written**:
   `v3rpc.Server` installs `otelgrpc.NewServerHandler`, which the grpc model refuses until S1 decides
   (the server cannot avoid it without bypassing `v3rpc.Server`).
2. **Crash and restart**: Perennial's distributed adequacy with some machines crashing and others
   stable (`notes/robustness.md`, "Next": a Perennial change, not started); the `[net, fs, idIssue]`
   bundle's crash interpretation (`kvnet_dist_crash_adequacy` has `[net, fs]`); generations that start
   in the file extension's shared mode (branch `wal-safe`'s blocker (1), option (b)); the WAL's boot
   after a crash (`walFoRes`, blocker (2)); the server's restart from its files (C6: `NewServer` and
   `NewServerR` as one spec chosen by `haveWAL`, over `ReadAll`, `walCrashKeeps`); the backend after a
   power loss (bbolt over the file extension: `osfs/bboltfs` is the start; the server's backend is a
   trust boundary today). **The issue record after a crash is wrong as it stands** (review F3): it keeps
   generators by heap address and survives the crash, and a crash makes the heap arbitrary, so a
   restarted member's generator at the old one's address may reissue the old incarnation's ids and
   the model would admit what `nonissues/etcd-request-id-restart-reuse.md` describes. To be keyed by
   incarnation (an epoch the crash relation increments), a trusted-semantics change with its example
   and an axiom review (D4). The idutil model's clock assumption now spans machine restarts.
3. **clientv3 over real gRPC**: clientv3's specs today are over the axiomatized `Invoke`/`NewStream`;
   they are re-proved over the models with the same statements where possible (phase 7's protocol
   facts list), with the extra errors the model gives (REFUSED_STREAM, any code on a cut, idleness).
4. **The cluster's invariants across machines**: today `etcd_adequate_members_below` allocates the
   cluster's ghost state in one process. Distributed: allocated once in the global ghost state (as
   `KitBridge`'s `Hstart`), each member's local state rebuilt after a crash from its files and the
   global invariants (the raft log's durability invariant, the restart plan's `InvRestart`); the
   clients' specs over the cluster's API (`srvApi`) unchanged.
5. **The workloads**: the drivers' workload triples (`partition.Check`, `auth.Work`, ...) carry over;
   each driver's `Run` half is its `Main` triple minus the start's resources.
6. **Assembly**: a bridge as `KitBridge` for crashing and stable machines; `Link`s of the two programs;
   `etc/gen-init.py` entries; a TCB collection.

## 8. Open questions

**Decided (the user, 2026-11-21: "go with your recommendations"):** Q1 a key prefix per workload, at most one
of each kind, the auth workloads alone, a revision-reading check only beside the lease workloads; Q2 fold
leaseexpiryN in, `noExpiry` conditional; Q3 the `durable` workload under real crashes; Q4 the coverage given
up accepted; Q5 a trusted Lean SHA-1 tested against Go first, Perennial's `crypto/sha1` proof later; Q6 the
carried premises accepted for the first version; Q7 the interim theorem without crashes is the first
milestone; Q8 etcd's full peer handler; Q9 no further `ServerConfig` fields in the first version; Q10 the
server clears the proxy variables itself. Open: the name (`etcd_dist_safe` vs. the files' `_robust`
convention) and U1-U5 (upamanyus, etcd-grove#24).

For the user:

- **Q1 Composition of workloads.** Recommended (after review F1): a key prefix per workload; at most
  one of each kind; the auth workloads alone; a check that reads revisions as its own (kv, watch,
  cache) beside the lease workloads only. Alternatives: checks relative to their prefix (porcupine
  over revisions does not allow it simply), or one workload per deployment.
- **Q2 leaseexpiryN.** Recommended: fold in, `noExpiry` conditional on the workloads and `Compatible`
  excluding the mix. Alternative: keep `etcd_leaseexpiryN_safe` as its own row.
- **Q3 restartN/restart1.** Recommended: the `durable` workload (cheap) under real crashes; the
  revision check is dropped (other clients write). The `kv` workload under crashes covers the same
  property more strongly.
- **Q4 Coverage given up**: `HardStop` and `raftSwap` (graceful in-process restart), `CutPeer`/`MendPeer`,
  the bridge, the server's own `Put`/`Range` API. Accept?
- **Q5 Member ids**: a Lean SHA-1 (trusted, tested against Go) so that `WellFormed` is evaluated by
  `decide`, or Perennial's `crypto/sha1` with its proof? Until then `memberId` is opaque.
- **Q6** Accept `EtcdEnv`/`HNs`/`BootFacts` as premises for the first version (§5)?
- **Q7 An interim theorem without crashes** (`Robust [] (servers ++ clients)`, over the existing
  `goose_dist_adequacy`, as the kits): it needs neither the mixed adequacy nor the restart work, and the
  final statement implies it. Recommended as the first milestone.
- **Q8 The peer handler**: the raft handler only (as the examples; keeps `leasePeersOk` true, but a
  follower's `TimeToLive` then reports a live lease absent, 404) or etcd's full peer handler (`/leases`
  served, as a real deployment; `leasePeersOk` then has to be proved of etcd's lease handler).
- **Q9** Which other `ServerConfig` fields to quantify (`TickMs`, `ElectionTicks`, quota, request limits).
- **Q10 The proxy**: the server clears the environment (recommended) or a fork change `Proxy: nil`.

For upamanyus:

- **U1** Is S4's deployment shape this one (members `crashing`, clients `stable`, `addrOk` addresses,
  `NetStart`)? Anything in `WellFormed` the transport needs beyond `addrOk` and distinctness?
- **U2** The stats handler: `v3rpc.Server` installs `otelgrpc.NewServerHandler`, so the server needs
  S1's "the model calls the handler" (the program cannot omit it).
- **U3** No cmux: the server serves gRPC alone on the client address (etcd's embed splits with cmux).
  Fine for the model, or should the program use cmux as a real deployment does?
- **U4** The mixed crashing/stable adequacy in Perennial: who, and in which form (boot programs for a
  prefix of the nodes, as `DistCrashNsteps` already has).
- **U5** `idIssueExt` in the bundle with the net and file extensions; its record across a crash.

**upamanyus's answers (etcd-grove#24, 2026-11-21 22:19Z):**
- **U1:** yes, S4's shape.
  - Keep the exact address spellings: clients dial exactly the `a.b.c.d:p` their member listens on.
  - Reuse `Net/Statement/KitDeploy.lean`'s `NetStart`/`ServerStart` definitions rather than restating them, so `KitBridge` applies.
  - A restarted member's `Listen` on the same address is allowed: net v3.4's `crash_init` drops listeners and cuts connections.
- **U2:** S1 makes the gRPC model call the stats handler, with differential tests. `grpcStatsHandlerOk` becomes proved of otelgrpc's handler.
- **U3:** no cmux; keep plain `grpc.Server.Serve`.
- **U4:** the mixed adequacy already exists in Perennial at `d648cfe22`: `goose_dist_mixed_crash_adequacy` (`GooseLang/DistAdequacy.lean:852`) and `_init` (`InitAdequacy.lean:196`).
  - Missing: our bridge to `Robust crashing stable`. `robust_of_kitBoot` covers the all-stable case only.
  - kvnet's claim #22 is building the crashing bridge for `[netExt, fsExt]` (`GooseLang/Ext/NetFs/Adequacy.lean`). **D3 extends that; coordinate on #22.**
- **U5:** nothing from the transport side; the extensions need only commute with the net extension's per-machine crash semantics.
- **Extra:** rafthttp's client uses `http.ProxyFromEnvironment`, and S5 treats a non-nil proxy as `NotModelled`, so Q10's `clearProxyEnv` is what it needs. The environment as machine-local state is an `os` model question: entry for `notes/perennial-changes.md`.
- **Order:** `v3rpc.Server` with one keepalive option (S1), then `Serve` (S2); the raft handler's `http.Server.Serve` is S5's server side.

## 9. Staged path (rough sizes)

| Stage | Work | Size | Depends on |
|---|---|---|---|
| D0 | this draft; reviews; decisions Q1-Q10 | — | — |
| D1 Go | split each driver into start + `Run(eps, …)`; the two mains; a harness test with `examples/lib/robust` (namespaces, kills, power losses, partitions) over random deployments; audit every check against #24's error rules | 1-2 sessions | — |
| D2 translation | goose projects for `server` and `client`; `Init`/`PkgTable`; the main tree's `net` becomes the part's | days | phase 7 S0, S4 |
| D3 mixed adequacy | the bridge from Perennial's `goose_dist_mixed_crash_adequacy` (exists) to `Robust crashing stable`, extending #22's `[netExt, fsExt]` bridge | smaller than ~1k lines | #22 |
| D4 bundle | `[net, fs at etcdFsSem, idIssue]` adequacy and crash interpretation; the issue record keyed by incarnation; shared-mode generations | ~1k lines | wal-safe (b) |
| D5 transport | phase 7 S1-S5 | 60-110k lines (option B's estimate) | upamanyus |
| D6 server | one `NewServer` spec for both starts; `walFoRes`; C6; the backend after a crash; `TrustBoundary` discharged | weeks | D4 |
| D7 cluster | global/local ghost split, the restart invariant | weeks | D6 |
| D8 clients | port dsverify's `Remote` orchestration (`RunRemote`, `ServeClient`, `remoteDistSafe`) onto the net extension in `examples/lib/remote`, over `lintest`/`kvcheck` and the verified porcupine; each workload's client operations as `Remote` calls | ~2k lines + the port | D1 |
| D9 assembly | the theorem; `WellFormed` consumed; retire `etcd_safe`, leaseexpiryN's | ~2k lines | all |

**Interim milestone (Q7)**: D1, D2, D5 (S1-S5), D7 without crashes, D8, D9 over `goose_dist_adequacy`:
the same deployment with no member crashing. Then D3, D4, D6 add the crashes.

## 10. Spec review

An independent `spec-reviewer` agent reviewed the first draft (`de96cea820`) with the Go and the
model limits of #24. Its verdict: the shape is right; three findings made the statement false in
the model. Dispositions (fixed = in this commit):

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F1 | blocker | `Compatible` let `kv` run beside `putget`/`compact`/`durable`: their writes move the revision txnlin's model checks and land in kv's ranges (`linkvtxn.go:428,708-713`), so porcupine says Illegal in a fault-free run; `compact` and `durable` keys collide (`compactkv.go:66`, `restartN.go:87-97`) | **fixed**: per-workload key prefixes (client sketch); `writesKeys`/`needsSoleWriter`/`alone` replace `exclusive`; watch and cache may now run beside the lease workloads |
| F2 | blocker | `[HasExt Fs.fsExt]` picks the file extension's own semantics, with I/O errors; every etcd proof is over `etcdFsSem` | **fixed**: the binder is at `etcdFsSem`; the header discloses its assumptions per machine |
| F3 | blocker | the issue record keyed by `Loc` across real crashes admits id reuse | **accepted, D4**: key it by incarnation (trusted change, its example, axiom review); disclosed in the header |
| F4 | high | the server serves clients before replaying its WAL; after a power loss auth/lease checks can fail legitimately | **fixed** in the sketch (`<-s.ReadyNotify()`); whether the proofs can give it that meaning: D6 |
| F5 | high | `compact`'s `latest ≥ crev + 1` fails under the periodic compactor | **fixed**: `WellFormed` excludes it |
| F6 | high | Lean errors: `HasExt` needs `GooseInterp`; `LogEntry` not opened; the `Supported` instance; `token ≠ ""` | **fixed** (unbuilt: may still not elaborate; start predicates over `ElemExt`) |
| F7 | medium | `rpctypes`/`cache` `Assumptions`, `DialWithBalancerBody`, `log.NewModel` dropped silently | **fixed**: carried as binders |
| F8 | medium | `addrsUnclaimed` (b) and `verifyEnvOff` dropped before their replacements; clients read the proxy too | **fixed**: `EtcdEnv.peerRequests` placeholder, `HEnv` premise kept, clients clear the proxy |
| F9 | medium | `BootFacts` over an opaque `memberId`: `WellFormed` not `decide`-able | **open**: Q5 (target: `bootOf d`, `BootFacts` proved from `WellFormed`) |
| F10 | medium | auth's token provider with expiring leases needs `leasesNoExpiry` (`LeaseApi.lean:69-70`) | **fixed**: excluded in `WellFormed` (to recheck what "auth on" means in `lease.bootCfg`) |
| F11 | medium | client machines' packages reach `fileutil`'s initializer, which probes the file system | **fixed**: `ClientStart` adds `FsInit` (or split the packages, D1) |
| F12 | low-medium | the durable check "exact" contradicts unknown outcomes; `n < 2^31` vs restartN's 256 keys; version 1 relies on at-most-once delivery | **fixed** (check and bound); at-most-once: D8 |
| F13 | low | `workloads ≠ []` unneeded; "one of each kind" stricter than needed | **fixed** (dropped `≠ []`); one of each kind kept for now (Q1) |
| F14 | low | cache, compact, putget proved only on one member without faults; the cache's resumption at another member unchecked | **open**: D8 risk |
| F15 | low | name: `_robust` is the convention for `TopLevelRobustness`; `cmd/` JSON parsing is a trusted gap | gap **disclosed**; name kept as the coordinator asked (`etcd_dist_safe`), the user's call |

The review also notes that F3 and F4 make two recorded nonissues reachable under real crashes
(`nonissues/etcd-request-id-restart-reuse.md`, `nonissues/etcd-watch-lagging-member-auth-off.md`):
their "Proof" sections are to be updated when the statement lands. No new Go bug was found.
