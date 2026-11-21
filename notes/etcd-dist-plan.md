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

**The clients** (`examples/etcd/dist/client`): `Main(w Workload, eps []string)`, one workload per
machine, each today's driver without its start (no `StartMembers`, bridges, partitioner, `CutPeer`,
`HardStop`): each driver is split into its start and a `Run(eps, …)` (stage D1). Workloads that pick
a member use `eps[i mod k]`. Every checker follows the model's rules (etcd-grove#24): any non-OK
gRPC error is an unknown outcome, never "not applied"; a server stream's clean end is never taken as
complete (`etcdstart.Collect` already reads until a revision, not until the channel ends); nothing
relies on keepalive.

| Workload | From | Check (panics if it fails) | Exclusive? |
|---|---|---|---|
| `kv clients ops` | txnlinfaultsN / partition `Check` | porcupine, txnlin's model | no |
| `watch writers ops` | partition `MainWatch` | `etcdstart.Check`: exactly the writes, gap-free revisions | **yes** (gap-free) |
| `cache writers ops` | cache | the same, through the watch cache, plus progress and Get | **yes** |
| `compact` | compactwatch | latest reads never compacted, old reads exact or `ErrCompacted` | no |
| `putget` | compacted | Get after Put returns it | no |
| `auth` | authN | principals' rights at every member | **yes** (enables auth) |
| `authLease` | authlease | lease rows of auth | **yes** |
| `leaseRead` | leaseN | listings without duplicates, TimeToLive about the lease asked | no |
| `leaseCatchup` | leasecatchup | the member that granted lists the lease once caught up | no |
| `leaseExpiry` | leaseexpiryN | a lease gone from a listing is never listed again | no |
| `durable puts` | restartN / restart1 | every acknowledged Put present at version 1 (no revision check) | no |

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
5. a client; the workloads `Compatible` (at most one of each kind; an exclusive one alone; never
   `leaseExpiry` beside a workload that needs no lease to expire) and within their bounds; `cfg.auth`
   if a workload needs the token provider.

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
   trust boundary today). The issue record after a crash: its docstring says crashes keep it and that a
   generator allocated after one may get a stopped one's address (sound, but `Next`'s proof would need
   the record keyed otherwise); the idutil model's clock assumption now spans machine restarts.
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

For the user:

- **Q1 Composition of workloads.** Recommended: at most one of each kind, exclusive kinds alone
  (`Compatible`). Alternatives: a key prefix per workload and checks relative to it (Go changes to the
  watch checks' gap-freedom and auth's ranges), or one workload per deployment.
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

## 9. Staged path (rough sizes)

| Stage | Work | Size | Depends on |
|---|---|---|---|
| D0 | this draft; reviews; decisions Q1-Q10 | — | — |
| D1 Go | split each driver into start + `Run(eps, …)`; the two mains; a harness test with `examples/lib/robust` (namespaces, kills, power losses, partitions) over random deployments; audit every check against #24's error rules | 1-2 sessions | — |
| D2 translation | goose projects for `server` and `client`; `Init`/`PkgTable`; the main tree's `net` becomes the part's | days | phase 7 S0, S4 |
| D3 mixed adequacy | Perennial: crashing + stable machines; a bridge as `KitBridge` | ~1k lines | — |
| D4 bundle | `[net, fs, idIssue]` adequacy and crash interpretation; shared-mode generations | ~1k lines | wal-safe (b) |
| D5 transport | phase 7 S1-S5 | 60-110k lines (option B's estimate) | upamanyus |
| D6 server | one `NewServer` spec for both starts; `walFoRes`; C6; the backend after a crash; `TrustBoundary` discharged | weeks | D4 |
| D7 cluster | global/local ghost split, the restart invariant | weeks | D6 |
| D8 clients | each workload's `Run` triple from today's | ~2k lines | D1 |
| D9 assembly | the theorem; `WellFormed` consumed; retire `etcd_safe`, leaseexpiryN's | ~2k lines | all |

**Interim milestone (Q7)**: D1, D2, D5 (S1-S5), D7 without crashes, D8, D9 over `goose_dist_adequacy`:
the same deployment with no member crashing. Then D3, D4, D6 add the crashes.

## 10. Spec review

(Below: the `spec-reviewer` agent's findings on the draft and the dispositions.)
