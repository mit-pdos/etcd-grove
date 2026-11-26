# `etcd_safe`: etcd as a distributed deployment (plan, DRAFT for review)

2026-11-21. Branch `etcd-dist`. A draft for the user and upamanyus (etcd-grove#24): a plan, the
statement and its definitions, no proofs. Files:

- the statement: `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TopLevelRobustness.lean`
  (`etcd_robust.spec`);
- its definitions: `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TopLevelDefs.lean`
  (`Deployment`, `WellFormed`, `Workload`, `Compatible`, `ServerCfg.Supported`, the start states,
  `EtcdEnv`; placeholders marked `PLACEHOLDER`);
- the Go programs: `examples/etcd/dist/{server,client,env}/` and `cmd/{server,client}/`, and the
  deployment test in `examples/etcd/dist` (`dist_test.go`) (stage D1, done: §2, "Stage D1").

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
the network: no connection), bootstrap's results, and the premises carried over from the single-process `etcd_safe`
until they are discharged (§5), the deployment is `Robust`:

    Robust (servers d σs) (clients d σc) g (threads := 2^28) (bound := 2^40 - 11)

`servers d σs` are the members' machines, each running `server.Main(cfg_m)`, in `Robust`'s
`crashing` list: a crash at any step, then the same boot program from what the file extension's
crash relation keeps. `clients d σc` are the client machines, each running `client.Main(w, eps)`, in
`stable`: never crash, so a client keeps its history. `threads`/`bound` are the single-process `etcd_safe`'s, to be fixed by
the proofs (the bound counts every machine's steps together).

The extensions are any list holding the net extension, the Linux file extension and the request
ids' issue record (`[HasExt Net.netExt] [HasExt Fs.fsExt] [HasExt idIssueExt]`), as `kvraftRobust`.

## 2. Machines and programs

**The server** (`examples/etcd/dist/server`): `Main(c Config)` with `Config = {Name, Peer, Client,
Cluster []Peer, Token, CompactorMode, Retention, SnapCount, CatchUp, Auth}`. It is etcdstart's
`newServerMode` + `NewMember` + `Serve` with the configuration a parameter: build the member
(`etcdserver.NewServer`), serve its raft handler on its peer listener with `http.Server.Serve`, start
it, serve `v3rpc.Server` on its client listener with `grpc.Server.Serve`, then sleep forever. The
same `Main` is the boot program after a crash: `NewServer` finds the WAL (bootstrap's `haveWAL`) and
restarts the member; the initial cluster and token are then ignored by etcd. (Until 2026-11-23 it first cleared the
proxy variables and `ETCD_VERIFY`, `env.ClearProxy`; dropped, Q10's update.) The binary (`cmd/server`) reads the
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
(proved: `Run` never returns `Illegal` when `apply` is logically atomic), and `examples/raft/kvraft/kvcheck` (#22)
is the closest existing `ServeClient`-like node. So the port is the orchestration (`RunRemote`, `ServeClient`)
over `lintest`/`kvcheck` and the net extension, in a neutral home, `examples/lib/remote`, which phase 6's kits
will reuse.
The workload table's "one machine per workload" (§2) becomes "one orchestrator plus k_c client machines per
workload"; single-client workloads (putget, compact, durable) stay one machine.

### Stage D1 (Go), done 2026-11-21

No existing driver's Go changed (`examples/etcd/*`, `examples/lib/etcdstart`, `lintest`, ...): the
split is in new packages, which call the drivers' exported helpers where they take clients and copy
the rest. No Goose project and no `etc/goose.py` run (D2). The build tag is gone: everything below
builds, vets and tests (`go vet ./etcd/dist/...`, `go test ./etcd/dist/...`, go1.27.3).

- **`examples/etcd/dist/server`**: `Main(Config)` (and `MainLogger`, the same with a logger, for the
  harness's diagnosis). One member; `etcdhttp.NewPeerHandler` (etcd's full peer handler, Q8) served by
  `http.Server{...}.Serve` on its own peer listener; `s.Start()`; `<-s.ReadyNotify()`; then
  `v3rpc.Server` (insecure, keepalive enforcement 5 s as `etcdstart.Serve`) by plain
  `grpc.Server.Serve` on its own client listener (no cmux, U3); `env.ClearProxy()` first (Q10). The
  addresses are the `Config`'s strings verbatim in `Listen`, `PeerURLs`, `ClientURLs` and the
  clients' endpoints (U1); `Main` returns without serving if its own name and peer address are not an
  entry of `Cluster`. Data directory and WAL area: `etcdstart.DataBase/<Name>.etcd` and
  `etcdstart.WALBase/<Name>.etcd` (the Lean `Member`'s); `Config` has no directory field.
- **`examples/etcd/dist/env`**: `ClearProxy` (the six proxy variables and `ETCD_VERIFY`), the server's
  and the clients' one copy.
- **`examples/etcd/dist/client`**: one package, a file per workload family (`kv.go`, `watch.go` with
  cache, `compact.go` with putget, `durable.go`, `auth.go`, `authlease.go`, `lease.go`); `Main(w,
  eps) Result` dispatches on `w.Kind` (the Lean constructors' order) and returns `checked` or why the
  workload ended without a check; a failed check is a panic. `Args` is `cmd/client`'s JSON.
  Prefixes: watch `wk/`, cache `ck/`, compact `cw/`, putget `pg/`, durable `du/`; **two exceptions**:
  kv keeps txnlin's keys (`k0`-`k2`, List over `[k, l)`) and auth/authLease keep package auth's
  (`a/…`, `c/…`, `z/…`), since both are fixed inside the reused packages; both run as the only key
  writer (kv) or alone (auth), and no other prefix starts with `k`, `a`, `c/` or `z`.
- **`cmd/server`, `cmd/client`**: JSON config in, `server.Main`/`client.Main` (the client prints its
  result). `DIST_LOG` makes the server log to standard error.
- **`examples/etcd/dist`** (`deploy.go`, `run.go`, `dist_test.go`): the deployment test (`TestDist`, `TestWellFormed`; see "The
  harness" below).
- **`examples/lib/robust`** (shared with kvraft's driver, additive): the **bridge variant** of the
  namespace mode and `RerunInUserns`. This machine's root has no `CAP_NET_ADMIN`, a read-only
  `/proc/sys` (no `ip_forward` in the router), no iptables and no device mapper; inside a user
  namespace of its own (`unshare -Urnm`) it has veths, bridges and tc. There `NewNetwork` makes a
  bridge instead of a router (machines on one /16; a block is a tc flower drop on the sender's port;
  link faults netem as before); a `Reset` block drops (tc cannot send a reset: `CanReset`, and the
  nemesis then never picks one). `TestNetworkFaults` passes in it.
- **What is generic lives in `examples/lib/robust`** (moved there 2026-11-22, the user's decision;
  before, `dist/run.go` held it and `examples/k8s/dist` copied parts): `robust.Run` (`run.go`)
  starts each machine's process with its log (`logs/<name>.log`); the members are `Restartable`s of
  a `Group` (`NewGroup`, `Group.Add`: a directory of its own, or a disk's mount in the power modes;
  `Group.Start`), crashed one at a time by the group's crasher and restarted on the same directory;
  `RunClients(nodes, orchs, machines)` starts the client machines' processes and the orchestrators
  (`robust.Client`, each orchestrator's set-up marked by its `Ready` file), starts the faults
  (`RunFaults`: a crasher per group, one network nemesis over `machines`) once every set-up is done
  or `SetupWait` passed, and waits for the orchestrators, the deadline or a failure; `Fail`, `Err`,
  `Failed`, `Stats`, `NetStats`, `Stop`. `Config`, `Command` and the crash modes (`CrashKill`,
  `CrashPower`, `CrashMixed`) are `robust`'s. `util.go`: `NewNetworkOrLocal` (was `dist.NewNet`),
  `Symlink` (was `link`), `RerunTest` (`TestDist`'s re-run in a user namespace or by sudo), `Tail`.
  `robust` is the test side only: no machine's program (`dist/{server,client,cmd,kvremote,enc,env}`,
  `examples/k8s/dist`'s non-test files) imports it, since D2 translates those programs. The helpers
  the programs share are `dist/client`'s (`await.go`): `AwaitAccept` (was `awaitNodes`), `Rotate`
  (was `rotate`), `CallAll` (the body of `reportAll`, now a one-line wrapper over it). What stays in
  `examples/etcd/dist`: the member program and the workloads (`server`, `client`, `RunProcess`),
  `Deployment`, `RandomDeployment`, `WellFormed`, the member configurations, ids and addresses
  (`MemberAddrs`, `MemberMachines`), and `Cluster`: a deployment's members in a run (`Start(d, run,
  net, ms)`: their directories, the links from the data directory and WAL area, their
  configurations) and its workloads' machines (`Cluster.Run`, over `RunClients`); `Cluster.Stop`
  removes the links, the run's `Stop` kills the members and removes their disks. `client.AwaitCluster`,
  `client.ConnectRetry`, `AwaitAccept`, `Rotate` and `CallAll` are exported, for `examples/k8s/dist`'s
  machine programs.

**Copies** (driver code that could not be reused unchanged, and why):

| Copy (in `dist/client`) | From | Why not reused |
|---|---|---|
| `kvClient` | `lintest.runClient` | unexported; and `lintest.Run`'s `apply` gets no client id, so client *i*'s operations could not go through client *i*'s own clientv3 client (the Remote seam) |
| `RunWatch` | `partition.MainWatch` | one function with its start and partitioner; its `writer` picks a random client per Put (here each writer has its own: `etcdstart.Writer`, reused) |
| `RunCache`, `cacheCollect`, `awaitProgress`, `checkProgress`, `lastVal`, `hasKey`, `checkGet` | `cache.Main` and its helpers | `Main` starts its member; the helpers are unexported |
| `RunCompact`, `checkCompactRev` | `compactwatch.Main`, `checkCompactRev` | inline in `Main` with its start; unexported |
| `RunPutGet` | `compacted.Main` | inline in `Main` |
| `RunDurable` | `restartN`'s `check` | rewritten: restartN's Puts and Range go through a member's own API in-process, with `HardStop`; its exact revision check cannot hold beside other writers (Q3) |
| `RunAuth`, `newUserClient`, `barrier` | `authN.run`, its helpers | `run` serves its members' gRPC first (`etcdstart.Serve` of `srvs`); helpers unexported (`auth.SetUp`, `Work`, `CheckHistory`, `LastIn`, `Permitted`, `Principals` reused) |
| `RunAuthLease`, `reqCtx`, `refused`, `barriers`, `grantPut`, `noAuth`, `foreign`, `absent` | `authlease.run`, its helpers | as authN |
| `RunLeaseRead`, `leaseReadCheck` | `leaseN.run`, `check` | `run` serves its members; `check` unexported |
| `RunLeaseCatchup`, `leaseGrant`, `leaseList`, `listed` | `leasecatchup.run` and helpers | `run` starts the cluster and cuts with `PeerStep`; helpers unexported |
| `RunLeaseExpiry`, `gone` | `leaseexpiryN.run`, `gone` | `run` serves its members; unexported |
| harness `addrOk` | `kvraft.AddrOk` | kvraft is a Go module of its own |
| `server.serverConfig` | `etcdstart.newServerMode`, `StartMemberAuth` | unexported, and the snapshot and token-provider settings are fixed there |

Changes from the drivers made in the copies (none weakens a check): a step's error that ended the
driver's run (compact's and putget's Put or latest Get, leaseRead's per-member reads, leaseExpiry's
grant or listing) skips that round or member instead, since under the harness's faults errors are
common; every watch read and every poll is bounded in time (`readTimeout`, 2 min; more polls for
leaseCatchup), so that a client machine's program ends (a liveness bound: a cancelled watch is an
end without a check); compact and putget run 20 and 50 rounds of distinct keys. Every workload first waits (bounded) until a
linearizable read through the cluster returns (`awaitCluster`): the members may still be electing,
and auth's set-up cannot be retried after an unknown outcome (without the wait, every auth run ended
in its set-up).

**The error rules, audited** (etcd-grove#24: any non-OK gRPC error is an unknown outcome, never
"not applied"; a server stream's clean end is never complete; keepalive relied on for nothing):

| Workload | Errors | Streams |
|---|---|---|
| kv | an error output is `Err`: txnlin's model keeps a failed write pending, to take effect at any later time or never; a failed read constrains nothing | none |
| watch, cache | only Puts that returned are `oks`; every watched event must be a Put *attempted* (`tried` includes the failed ones) | `Collect`/`cacheCollect`/`awaitProgress`: a closed channel or an error/cancel/compaction response returns false, an end without a check; read until a revision, never until the channel ends |
| compact | a failed Put skips its round; a failed Compact is ignored; the old-revision Get checks only if it returned; the watch checks only values it saw | `Collect` and `CompactRev` as above (a closed channel: no check) |
| putget | a failed Put skips the round (its key is never written again) | none |
| durable | a failed Put is unknown: its key may be present (with its value, version 1) or not; only acknowledged keys must be present | none |
| auth | a refusal is any error (`auth.Work`'s `refused`); whether a refused write was applied is checked from root's history watch of what was applied | `Collect` as above; the refused watch's channel is drained, only events checked |
| authLease | a refusal is any error; each "not applied" is checked by root's later read (`absent`, `z/lease`'s lease) | none |
| leaseRead | reads only; an error checks nothing | none |
| leaseCatchup | only grants that returned are compared (`g1`, the last filler) | none |
| leaseExpiry | a failed grant's lease is never looked at; a failed listing proves nothing | none |

Keepalive: `etcdstart.NewClients` sets it (harmless); no check depends on it.

**The seams for Remote** (dsverify's orchestrator plus one machine per client; `Remote` is ported into
`examples/lib/remote`; used by D8, "Stage D8 (Go)" below). Each multi-client workload separates the client nodes' code,
each over its own `*clientv3.Client`, from the orchestration:

- kv: client node *i* is `kvApply(cli_i)` (one txnlin operation, `txnlin.Apply`: ServeClient's
  handler); the orchestrator is `kvClient(i, ops, apply_i, clock)` per client (generation by
  `txnlin.Gen(i)`, call/return stamps, the history) and `RunKV`'s merge and porcupine check, where
  `apply_i` becomes the remote call. The clock (`lintest.CounterClock`) is the orchestrator's.
- watch, cache: writer *i* is `etcdstart.Writer(cli_i, w, tried, lo, hi)` (its Puts and its log of
  successes, which the remote version returns to the orchestrator instead of appending to the shared
  `Writes`); the watcher (or the cache) and the check stay on the orchestrator (`RunWatch`,
  `RunCache` after `writers`).
- auth: principal *who*'s node is `auth.Work(cli_who, who)` (its checks are local: refusals and its
  own replies); set-up, barriers, the history check and u's watch are the orchestrator's.
- leaseRead, leaseExpiry: per member, `leaseReadCheck(eps[i])` / grant-then-`gone` over `clis[i]`
  (independent per member: one node each if wanted); leaseCatchup's two clients (`c3`, `c1`) and
  authLease's principals are sequential steps of one orchestration, kept in one function.
- compact, putget, durable: one client each, one machine.

**The test** (`examples/etcd/dist`, `TestDist`, `DIST_RUN=1`): random well-formed
deployments of three members (`RandomDeployment`; `WellFormed` is the Lean predicate's Go mirror,
member ids from etcd's own `membership.NewClusterFromURLsMap`, the token searched until the low 16
(15) bits are apart): a random `ServerCfg` (compactor off/revision 1, 10, 1000/periodic 10 ms, 1 s,
snapshots 1-10000 with catch-up 1-2^48, the token provider when needed or at random) and a random
compatible mix (one of kv/watch/cache, or some of compact/putget/durable, each with lease workloads
at random; or auth or authLease alone). Every member and every workload is a process of the test
binary (`RunProcess`, as `cmd/server`/`cmd/client`) on a machine of its own; members at
`10.77.k.1:2380` (peer) and `:2379` (client). A member's files are a directory of the run's
(on a dm-flakey disk of its own where available), linked from its data directory and WAL area
(symbolic links: the paths are fixed by `server.Main`). Faults: a random member killed (SIGKILL) about
every 4 s, its files synced (or its disk's power lost, where the device mapper exists), restarted
within 1 s with the same program; on namespaces, `robust.NetNemesis` over all machines (partitions
both ways or one way, isolations, delay/loss/duplication/reordering), a fault about every second,
held about 2 s. A run fails on a panic, a member exiting on its own, or a client not done by the
deadline. `-short`: one deployment with small sizes; otherwise `DIST_ROUNDS` (default 4).

**Faults after the set-ups (the user, 2026-11-22).** By default the faults (kills, partitions, link
faults) start only once every workload's set-up is done. `client.MainReady(w, eps, ready)` calls
`ready` once its set-up is done (`Main` is `MainReady` with a no-op): watch and cache once their
watch is open, auth after `auth.SetUp`, the barriers and its principals' clients, authLease after
its leases and second barriers, leaseCatchup after its first grant; the others at once, after the
cluster's first read. `ready` is an observer only: no workload's steps or checks changed. The harness
(`RunProcess`) marks it with a file `<args>.json.ready` beside the client's arguments
(`cmd/client` prints `<kind>: set-up done`), and holds its faults until every workload has marked
it or ended, at most `SetupWait` (3 min; then it starts anyway and reports how many set-ups were
done: "faults from …, n set-ups done then"). A set-up that fails without faults ends its workload
without a check, as before, and its result line says so. `DIST_FAULTS=start` keeps the old mode
(faults from the start, set-ups under faults too). `DIST_WANT=auth,authLease` keeps only random
deployments with a workload of those kinds.
Root: a root with `CAP_NET_ADMIN` runs namespaces directly; a container's root reruns the test in a
user namespace (bridge variant, kills only); a non-root reruns by `sudo -n`, or falls back to the
local mode (one loopback address, kills only).

**Results (2026-11-21, this machine: a container's root, so the bridge variant, kills with sync, no
power losses, no resets).** Two full runs passed, 12 and 16 random deployments (the second after
`awaitCluster`): no panic, no member exiting on its own, every client done. The second: 118 kills,
69 partitions (17 one way, 29 isolating a machine), 37 link faults, in 316 s; checks ran in 28 of
33 workloads (kv 3/3, watch 2/2, cache 2/2, compact 4/4, putget 1/1, durable 3/3, leaseRead 6/6,
leaseCatchup 4/5, leaseExpiry 1/1, auth 1/6: the others ended in a barrier, root's last Put or its
history watch under the faults). authLease ran only in the first run (four times), always ending in
its set-up (before `awaitCluster`). Not exercised here: power losses (no device mapper), resets.
No check failed, and no bug in etcd was found.

**Results with the faults after the set-ups (2026-11-22, same machine, same limits).** The crasher
now kills a random member the moment the faults start (then about every 2 s), so that a workload
done within seconds still meets a crash. Three runs, all passed (no panic, no member exiting on its
own, every client done): 14 deployments aimed at auth/authLease (`DIST_WANT`), 24 unaimed, 16 aimed
at watch/compact/putget/durable; 54 deployments, 377 kills, 204 partitions, 110 link faults. Per
workload: runs, checks reached, and checks reached in a run with faults that lasted at least 2 s
after the faults started (the rest finished their checks within about a second of the first fault):

| Workload | Runs | Checked | Checked under faults (≥ 2 s) |
|---|---|---|---|
| kv | 6 | 6 | 4 |
| watch | 8 | 7 | 4 |
| cache | 4 | 4 | 4 |
| compact | 12 | 12 | 5 |
| putget | 10 | 10 | 4 |
| durable | 9 | 9 | 6 |
| auth | 11 | 4 | 4 |
| authLease | 9 | 8 | 8 |
| leaseRead | 18 | 18 | 9 |
| leaseCatchup | 11 | 11 | 4 |
| leaseExpiry | 11 | 11 | 11 |

Every set-up finished before its faults (no `SetupWait` ran out). auth's 7 runs without a check
ended after its set-up, under the faults, at root's last Put or root's history watch (an unknown
outcome or a watch end: no check is possible then); authLease's one at u's revocation; watch's one
had its watch end under the 10 ms periodic compactor. The old mode (`DIST_FAULTS=start`, 8
deployments aimed at auth/authLease, 62 kills, 28 partitions): auth checked 1 of 4, authLease 1 of
4, the rest ending in a barrier or the set-up, as before. No check failed; no bug found.

### Stage D8 (Go), 2026-11-22

The multi-client workloads run each client on a machine of its own, over `examples/lib/remote`
(on `lean` at `0c1d684587`, with `counter_remote_robust`), following the seams above. The
orchestrator machine is the workload's machine of D1 (`client.MainReady(w, eps, nodes, ready)`);
each client machine runs `client.NodeMain(w, c, nodes[c], eps)` (`examples/etcd/dist/client/nodes.go`),
which never returns. `client.NodeCount(w)`: kv's `Clients`, watch's and cache's writers, auth's four
principals; the single-client workloads (compact, putget, durable, the lease workloads, authLease)
keep one machine. `client.Args` gains `Nodes`, `IsNode`, `Node`.

- **kv** (`examples/etcd/dist/kvremote`, the counter instance's shape): the orchestrator is
  `kvremote.Orch` = `remote.Run(txnlin.Model(), nodes, Codec(), txnlin.Gen, ops, Attempt, 2 min)`
  (porcupine's timeout: Unknown is an end, not a failure); client machine *c* is `kvremote.Node`:
  `remote.ServeClient` whose `op` is **`txnlin.Call`, txnlin's `call` without prophecies** (new,
  exported, with `IsWrite`: `remote-port-plan.md` §3/§7's design, `Do` makes the prophecy), through a clientv3
  client of `rotate(eps, c)` made (retried) at the machine's start. A write gets one attempt and is
  otherwise `Output{Err: true}`, a read up to `ReadTries` (the user's: clients do not retry but
  reads). `Attempt` is `RequestTimeout + 5 s`, longer than a call. The codec is every field of
  txnlin's `Input`/`Output` in order through `examples/etcd/dist/enc` (8-byte integers, one-byte
  bools, length-prefixed strings; a decoder refuses short, extended and bad-bool encodings).
  `kvClient`/`kvApply` (D1's copy of `lintest.runClient`) are gone: `perclient.Run` replaces them.
- **watch, cache**: writer *c* is one call to its machine, **`remote.Report`** (new in
  `examples/lib/remote`: one attempt, no model, no prophecy, no retry; the answer and true, or
  false), whose input is the writer's Puts (`tried[c*nops, (c+1)*nops)`, generated by the
  orchestrator) and whose output is `etcdstart.Writer`'s log of those that returned (`[]PutRec`).
  The orchestrator calls every writer at once (`reportAll`, in `dist/client`: a goroutine per
  writer; kept out of `remote` so that `remote` imports no `sync` and its proofs and package
  tables are unchanged). **A writer that does not answer** (its call cut, or past its
  `nops * RequestTimeout + 30 s`) counts as all of its Puts tried and none succeeded: every event
  of its Puts is attempted (`tried` is the orchestrator's), none is required, so `etcdstart.Check`
  stays sound; the machine may still be writing while the orchestrator reads its watch, which the
  check allows (events up to `MaxRev(oks)` only, each attempted).
- **auth**: principal *c* (`auth.Principals()[c]`) is one `remote.Report` call: its machine connects
  the principal's client (`principalClient`: D1's choices of member and user), runs `auth.Work`
  (its own checks: a failed one is a panic of that machine, which fails the run) and answers
  whether it ran. The orchestrator keeps the set-up, the barriers, root's last Put, the history
  checks and u's watch. A principal without an answer changes nothing in the checks (they read
  what was applied). One change of order: the principals' clients are now made after `ready`
  (under the faults), not in the set-up.
- **The harness**: per workload, `NodeCount(w)` more machines (`client-i-kind-node-c`, at
  `IP:2390`, in the nemesis's list), their processes started before the orchestrator's and killed
  after it ends; one that exits on its own (a panic) fails the run. The orchestrators wait
  (`awaitNodes`, a dial loop) for their client machines; kv now has a set-up (that wait).
  `DIST_OPS=n` sets the kv clients' and writers' operations.

**Results (2026-11-22, this machine: container root, bridge variant, kills with sync, no power
losses, no resets).** Every run passed (no panic on any machine, no member exiting on its own,
every orchestrator done):

| Run | Deployments | Checked | Faults |
|---|---|---|---|
| `-short`, kv | 1 | kv 1/1 | 1 kill |
| kv, 4 x 200 ops | 3 | kv 3/3 (each within ~4 s of the first fault) | 6 kills, 2 partitions |
| kv, 4 x 1500 ops (`DIST_OPS`) | 3 | kv 2/3 (one porcupine timeout: Unknown), under 2-3 min of faults | 122 kills, 69 partitions, 35 link faults |
| watch/cache/auth, 30 ops | 4 | auth 1/2, cache 1/1, watch 1/1 | 33 kills, 16 partitions, 12 link faults |
| watch/cache/auth, 200 ops | 6 | auth 2/4, watch 1/1, cache 1/1 | 91 kills, 50 partitions, 22 link faults |
| watch/cache, 4 x 1000 Puts (`DIST_OPS`; all three drew watch) | 3 | watch 3/3, under 20-30 s of faults | 33 kills, 20 partitions, 9 link faults |
| unaimed | 6 | kv 2/2, compact 1/1, auth 1/2, authLease 0/1 (root's read under the faults), leaseRead 4/4, leaseExpiry 2/2 | 67 kills, 34 partitions, 18 link faults |

In all, 26 deployments, 353 kills, 191 partitions, 96 link faults.
auth's runs without a check ended at root's last Put or root's history watch under the faults, as
in D1. No check failed; no bug found.

**Lean (D8, started).** `txnlin.Call.spec` (`call.spec` with the input and output boxed) and
`IsWrite.spec`, proved over `call`/`isWrite` and linked (`etc/link-lean-first-linkvtxn.txt`: `wp_Call`,
`wp_IsWrite`). The kv instance on `remote` itself cannot be written yet:
1. **`net` clash**: `kvremote` imports txnlin, clientv3 and grpc, whose translations import the main
   tree's names-only `net`; `remote` and its instances live in the part `Net/`, whose `net` declares
   the same names. So `kvremote` cannot be translated into `Net/` (nor `Net/` import txnlin) until D2
   makes the main tree's `net` the part's (with phase 7's transport for clientv3).
2. **One store state**: `remote`'s `RBase.sysState` is one state for the whole system, timeless
   (the user's decision), while `call.spec`'s update is per member (`[∧list] sv ∈ ms, callUpd
   sv.γr.kv i Q`, each member's KV names). The kv instance needs the cluster's one KV state (D7's
   global ghost state), shown timeless, with each member's `etcdKV` agreeing with it.
3. Then, as the counter: `PendDec` for txnlin's model (its `isModel` against `pM` exists:
   `Proof/.../txnlin/PendModel.lean`), `codecOk` of the codec, `opMaybe` of `Call` (from `Call.spec`:
   a write's update fired at most once, a read's persistent read update: `opMaybe`'s read form, done
   2026-11-22, below), the nodes' WPs.
   `Report` needs a spec (a report's postcondition, no model) for watch, cache and auth: **done
   2026-11-22**, below ("`Report`, proved").

**Handoff (2026-11-22, end of the D8 Go session).** Branch `etcd-dist` (pushed), worktree
`/shared/etcd-grove-etcddist`; `lean` merged at `c89f800b38`. Built here (`manifest-d64.json`): the
regenerated translations (`GeneratedProof...txnlin`, `Net.GeneratedProof...lib.remote`) and
`txnlin.Call`/`IsWrite`'s proofs; **not** built here: txnlin's `Link.lean` (regenerated by
`etc/gen-link.py --linkvtxn`; its cone is the whole client proof) and remote's `Link` (unchanged; `Report`
has no proof yet, so `etc/verified-code.py` counts it unverified). The txnlin change rebuilds 828
modules (`etc/importers.py --count`). Next, in order: `Report.spec` and its proof in `Net/` (one
`attempt`, a report's postcondition handed through the slot as `Do`'s, with no model); then the kv
instance once D2 and D7 allow (the three points above); the watch, cache and auth instances over
`Report` after it. **`opMaybe`'s read form, done (2026-11-22, option A, the user's decision; ledger 2026-11-22,
"`remote.opMaybe`'s read form").** The far side now gets `slotUpd R i Φ`: a write's one-shot `lin`, a
read's `□ lin` (fired zero or more times). `remote.Do` has a second prophecy, resolved with the answered
reply's length and bytes (prophecy-only Go: `NewProph`, and `ResolveU64` calls in a loop over the reply's
bytes); `Do.spec`'s choice takes those bytes `bs` and, if an answer comes, returns a slot update and a way
from `Φb o` of an output whose bytes are `bs` (and a credit) to `Φ o`. `pend_choice` gives a read a read
commit invariant (`readN`, beside `pendCtx` at `pendCtxN`, both in `pendN`) that commits lintest's update
at the first firing whose output's bytes are `bs`. `Run.spec`/`Check.spec` take one new premise: distinct
outputs have distinct bytes (`cR_encOut_inj` for the counter). `counter_remote_robust`'s statement is
unchanged and it builds (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`). `txnlin.Call`
meets the read form in shape (its read update is `callUpd`'s persistent read update), but the statement
`opMaybe … Call` cannot be written in `Net/` until D2 (its import closure reaches the main tree's `net`)
and D7 (one store state). Other open decisions: (b) whether a
writer without an answer should rather be retried as reads are (it is a write: no, by the user's
rule; kept as "all tried, none succeeded").

**`Report`, proved (2026-11-22, branch `remote-report`).** `remote`'s slot library is generic over a
**service** `RSvc GF I O` (`Net/Proof/.../lib/remote/Defs.lean`): the wire (`RWire`: `iv`, `ov`,
`encIn`, `encOut`), the answers that are not outputs (`unkAns i v`) and the update a slot hands to
the far side (`upd i Φ`). A store is one (`RBase.svc`: `unkAns i v := v = unk i`, `upd := slotUpd R`;
`remoteAddr R a` is `svcAddr R.svc a`), and so is **a report** (`reportSvc W P Q`: the far side's loop
on `i`, given `P i` by the dialer (what the orchestrator established before the call: auth's set-up,
a writer's Puts being in `tried`), answers an output `o` with `Q i o`, its postcondition, persistent
or transferable; `upd i Φ := P i ∗ ∀ o, Q i o -∗ Φ o`; `unkAns := False`). The codec splits: `wireOk S cd` (`EncIn`,
`DecIn`, `EncOut`, `DecOut`: all `Report` and the serving side use; a report's codec leaves
`IsRead`/`Unknown`/`IsUnknown` nil) under a store's `codecOk` (`codecOk_wireOk`). The serving side's
counterpart: `svcOp S tok op` (given `S.upd i Φ`, `op` answers an output with `Φ` of it or an
answer `unkAns i v`), met by a store's `opMaybe` (`opMaybe_svcOp`) and by a report's loop
`reportOp W P Q tok op` (`{tok sys ∗ P i} op(sys, iv i) {v. tok sys ∗ ∃ o, v = ov o ∗ Q i o}`,
`reportOp_svcOp`). `attempt`, `serveConn`, `Serve`, `ServeClient` and `listen` are now stated over
`S : RSvc` (wire and update generic, same proofs); `Do`, `Run`, `Check` over a store, unchanged.
`Report.spec`:

    ∀ (S : RSvc GF I O) a i Φ cd d,
    {{ isPkgInit remote ∗ mapCtx (I := I) ∗ svcAddr S a ∗ wireOk S cd ∗ S.upd i Φ }}
      Report a (S.iv i) cd d
    {{ (v : GoInterface) (ok : Bool), RET (v, ok);
        ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ((∃ o, ⌜v = S.ov o⌝ ∗ Φ o) ∨ ⌜S.unkAns i v⌝)) }}

For a report, `Φ := Q i` and the caller hands `P i ∗ ∀ o, Q i o -∗ Q i o`: `true` comes only with an
output `o` and `Q i o` (the last disjunct is `False`); `false` carries nothing, as the orchestrator
treats it ("all tried, none succeeded"), and the update stays in the slot (the far side may still
run). Linked in `remote`'s `Link` (`wp_Report`); `counter_remote_robust`'s statement unchanged,
building with Lean's three axioms. `remote_start` now sets the addresses' protocols for any service;
`remote_robust` keeps a store's. **Left for the watch, cache and auth instances**: their `Q` (a
writer's log: each logged Put returned, as a persistent fact of the cluster's KV state; auth: that
`Work` ran), their codecs' `wireOk`, the far side's `reportOp` from `etcdstart.Writer`/`auth.Work`'s
specs, a `remote_robust` over a report service (one slot map per deployment holds one input type
`I`: a deployment that mixes `Do` and `Report` calls of different input types needs one
`RemoteGS` per type, or a sum type), all behind D2 (`net`) as kv's instance is.
**Open, from the spec review (2026-11-22)**: (A) the wire is pure values (`iv`/`ov : _ → GoInterface`,
`wireOk`'s decoders return `x = iv i`/`x = v`, encoders take `{{ True }}`), which fits the counter,
txnlin and auth (string in, bool out) but not the writers' `[]KV`/`[]PutRec` slices: a decoded slice
is fresh (and `DecOut` of an empty log gives `nil` where `writerOp` returned `[]PutRec{}`), and the
orchestrator must own the reply's elements. The fix is ownership-carrying representations
(`inRep i x`, `outRep o v`) through `RWire`, `wireOk`, `svcOp`, `attempt`, `Report`, and `Do`/`Pend`
(`⌜x = iv i⌝` for the pure instances): a redesign of the slot library, needed before the watch and
cache instances. (C) `mapCtx (I := I)` in `Report`'s/`Do`'s/`attempt`'s precondition is the slot
library's bookkeeping, one type per `RemoteGS`: fold it into `svcAddr`, or key the map by
`GoInterface`. (Minor) `RWire.encIn_len`/`encOut_len` bound every encoding below `2^63`, which an
unbounded `I` meets only by a subtype; frames are already at most `MaxLen` where the bound is used.

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

## 5. What is still not decidable (carried from the single-process `etcd_safe`)

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

| Today | In the distributed `etcd_safe` | Changes | Loses | Gains |
|---|---|---|---|---|
| single-process `etcd_safe` KV: txnlinfaultsN (`k₁ ≤ 1000`, schedule) | `kv` | partitions are the network's; clients dial members directly | `CutPeer`/`MendPeer` and the bridge's paths (test-only code) | every partition and fault, at any `k` the predicate admits, with crashes |
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
| raft rows (kv, kvdurable, kvreconf) | `kvraftRobust`'s shape (replicas crash, one checking client) | kvraft is raft's distributed row | — | — |
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
   bundle's crash interpretation (`kvraft_dist_crash_adequacy` has `[net, fs]`); generations that start
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
   `DistBridge`'s `Hstart`), each member's local state rebuilt after a crash from its files and the
   global invariants (the raft log's durability invariant, the restart plan's `InvRestart`); the
   clients' specs over the cluster's API (`srvApi`) unchanged.
5. **The workloads**: the drivers' workload triples (`partition.Check`, `auth.Work`, ...) carry over;
   each driver's `Run` half is its `Main` triple minus the start's resources.
6. **Assembly**: a bridge as `DistBridge` for crashing and stable machines; `Link`s of the two programs;
   `etc/gen-init.py` entries; a TCB collection.

## 8. Open questions

**Decided (the user, 2026-11-21: "go with your recommendations"):** Q1 a key prefix per workload, at most one
of each kind, the auth workloads alone, a revision-reading check only beside the lease workloads; Q2 fold
leaseexpiryN in, `noExpiry` conditional; Q3 the `durable` workload under real crashes; Q4 the coverage given
up accepted; Q5 a trusted Lean SHA-1 tested against Go first, Perennial's `crypto/sha1` proof later; Q6 the
carried premises accepted for the first version; Q7 the interim theorem without crashes is the first
milestone; Q8 etcd's full peer handler; Q9 no further `ServerConfig` fields in the first version; Q10 the
server clears the proxy variables itself (**superseded 2026-11-23**, the owner's option (A): `env.ClearProxy` dropped,
since `os.Unsetenv` has no spec; `verifyEnvOff` per machine and its token `envVerifyOff` are premises of the
statement, as in one process; a proxy premise comes with S5: `notes/putget-dist-plan.md` section 11). Open: the name (decided 2026-11-22: `etcd_safe`, the distributed theorems take the plain names; vs. the files' `_robust`
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
  - Reuse `Net/Statement/DistDeploy.lean`'s `NetStart`/`ServerStart` definitions rather than restating them, so `DistBridge` applies.
  - A restarted member's `Listen` on the same address is allowed: net v3.4's `crash_init` drops listeners and cuts connections.
- **U2:** S1 makes the gRPC model call the stats handler, with differential tests. `grpcStatsHandlerOk` becomes proved of otelgrpc's handler.
- **U3:** no cmux; keep plain `grpc.Server.Serve`.
- **U4:** the mixed adequacy already exists in Perennial at `d648cfe22`: `goose_dist_mixed_crash_adequacy` (`GooseLang/DistAdequacy.lean:852`) and `_init` (`InitAdequacy.lean:196`).
  - Missing: our bridge to `Robust crashing stable`. `robust_of_distBoot` covers the all-stable case only.
  - kvraft's claim #22 is building the crashing bridge for `[netExt, fsExt]` (`GooseLang/Ext/NetFs/Adequacy.lean`). **D3 extends that; coordinate on #22.**
- **U5:** nothing from the transport side; the extensions need only commute with the net extension's per-machine crash semantics.
- **Extra:** rafthttp's client uses `http.ProxyFromEnvironment`, and S5 treats a non-nil proxy as `NotModelled`, so Q10's `clearProxyEnv` is what it needs. The environment as machine-local state is an `os` model question: entry for `notes/perennial-changes.md`.
- **Order:** `v3rpc.Server` with one keepalive option (S1), then `Serve` (S2); the raft handler's `http.Server.Serve` is S5's server side.

## 9. Staged path (rough sizes)

| Stage | Work | Size | Depends on |
|---|---|---|---|
| D0 | this draft; reviews; decisions Q1-Q10 | — | — |
| D1 Go (**done** 2026-11-21, §2 "Stage D1") | each driver's workload without its start, in new packages (the drivers unchanged: helpers reused, the rest copied, the copies listed in §2); the two mains; a harness test with `examples/lib/robust` (namespaces, kills, power losses, partitions) over random deployments; audit every check against #24's error rules | 1-2 sessions | — |
| D2 translation | goose projects for `server` and `client`; `Init`/`PkgTable`; the main tree's `net` becomes the part's (planned: "D2's `net` half" below) | days | phase 7 S0, S4 |
| D3 mixed adequacy | the bridge from Perennial's `goose_dist_mixed_crash_adequacy` (exists) to `Robust crashing stable`, extending #22's `[netExt, fsExt]` bridge | smaller than ~1k lines | #22 |
| D4 bundle | `[net, fs at etcdFsSem, idIssue]` adequacy and crash interpretation; the issue record keyed by incarnation; shared-mode generations | ~1k lines | wal-safe (b) |
| D5 transport | phase 7 S1-S5 | 60-110k lines (option B's estimate) | upamanyus |
| D6 server | one `NewServer` spec for both starts; `walFoRes`; C6; the backend after a crash; `TrustBoundary` discharged | weeks | D4 |
| D7 cluster | global/local ghost split (design: "D7" below; the no-crash part first), the restart invariant | weeks | D6 (the restart invariant only) |
| D8 clients (**Go done** 2026-11-22, §2 "Stage D8"; `remote` ported: `counter_remote_robust`) | (seams: §2, "Stage D1") port dsverify's `Remote` orchestration (`RunRemote`, `ServeClient`, `remoteDistSafe`) onto the net extension in `examples/lib/remote`, over `lintest`/`kvcheck` and the verified porcupine; each workload's client operations as `Remote` calls. Left: the Lean kv instance (blocked on D2's `net` and D7's one KV state; `opMaybe`'s read form done 2026-11-22), watch/cache/auth instances (over `Report`, proved 2026-11-22: §2, "`Report`, proved") | ~2k lines + the port | D1; Lean: D2, D7 |
| D9 assembly | the theorem; `WellFormed` consumed; (the single-process `etcd_safe` and leaseexpiryN's already retired at the net swap) | ~2k lines | all |

**Interim milestone (Q7)**: D1, D2, D5 (S1-S5), D7 without crashes, D8, D9 over `goose_dist_adequacy`:
the same deployment with no member crashing. Then D3, D4, D6 add the crashes.
Its first step (2026-11-23): `putget_safe`, one member machine and one client machine
(`notes/putget-dist-plan.md`, branch `putget-dist`): stated and building; the client machine's proof waits for S2
(the plan's section 4: what the client's `Invoke` needs across machines).


### D7: the cluster's ghost state split into global and per-member parts (design, 2026-11-23)

Branch `d7-split` (off `lean` `4b2724dfe6`). For the interim `etcd_safe` (Q7: `k` members each on a machine,
client machines, **no crash**, over `goose_dist_adequacy` through `Net.robust_of_distBootI`). Starts from the
audit (`/shared/tmp/coord-03/d7-audit.md`, 2026-11-22: classes G global ghost, S split, T transport, P
per-process); disagreements with it are marked **(audit)**.

**The constraint.** The bridge's start update (`robust_of_distBootI`'s `Hstart`) runs at the global ghost
state only (`[GooseGlobalGS .hasLC GF]`): there is no `HeapGS` yet, each machine gets its own local ghost
state `L` only in its `nodeWp`, and a `GooseLocalGS` cannot be made up at the start (its extensions' local
ghost states are arbitrary types). So whatever the start allocates must be stated over the global ghost state,
and whatever needs a heap (a WP, a points-to, a premise of `etcdstart.premises`) is built in a member's boot.
A predicate defined in a `[hG : HeapGS]` section whose body reads only `hG.goose_globalGS` is global in
content but not in Lean: the start cannot name it. Two ways to name it at the start: **re-section** its
definition over the global classes (`[AllG GF] [ReceiptGS GF] [InvGS GF]`, as raft's `api` sections are;
at a heap the instances resolve to `hG.goose_globalGS`'s, so every existing use reads the same term), or a
global twin equal by `rfl` (kvraft's `kvFactsG`/`kvFacts_eq`, `KvRaft/.../kvraft/TopStart.lean`). Twins cascade
(a twin's body needs its callees' twins), so **D7 re-sections** in place, as the audit's "retype only".

**Where the single-process proof already splits.** `allocN` (`etcdstart/AllocN.lean`) is the cluster's part
then a per-member fold: (1) `newServerNames_allocL` (each member's store names `idx id`, certificate map
`cok id`, revisions' map `rev id`, storage registry `reg id`), (2) `srvClusterBoot_alloc` (raft's cluster
with its bootstrap log, the KV invariant, the request ids' claims, the proposal mint, the read contexts, the
client's `etcdKV`, and per voter its slice), (3) `netNames_alloc` + `netHttp_reserveL` (rafthttp's network and
each peer address's HTTP protocol), then (4) `memberBoots_of` = `memberBoot_of` per member, which takes the
cluster's persistent facts and the member's slice and allocates the member's request names `ρ`
(`srvMemberBoot_alloc`). D7 cuts exactly there: **(1)-(3) are the global start, (4) is each member's boot.**

**1. Allocated once, at the deployment's start** (the start update of the etcd theorem's `Hstart`, by a lemma
`etcdClusterStart` over the global ghost state; inputs: `BootCore ps ctxs boot`, the members' ids, the
addresses' `addrUnset`; no heap):

| What | From | Today's section | D7 |
|---|---|---|---|
| raft's cluster `γ` with its bootstrap log: `isClusterU`, `clusterInv`, `rdPool` (with its time receipts), the budget, `isCommittedLogLb γ boot`; per voter `raftState γ.cl id init`, `nodeVacant γ.cl id` | `cluster_alloc_boot_impl_tr` | heap, **only because of `bootMarshal`** | a global `cluster_alloc_bootG` without `bootMarshal`, giving per voter `nodeBootG` (below) |
| `srvRaftLogInv`, `kvInv`, `idClusterInv`, `(0) ↪[issued]□ none`, `srvPropMint`, `srvRdCtxInv`, and per member `(pfx,0) ↪[cnt]`, `idKeyFactAt fs (pfx,0) (idx id).slog`, `idWaitTokAt wn (pfx,0)`, the snapshot directory's `ghostMapAuth γd` | `srvClusterBoot_alloc` (`kvInv_alloc_boot`, `idCluster_alloc`, ...) | heap | re-sectioned (their bodies read only global ghost state: checked for `kvInv`, `srvRaftLogInv`, `srvFloorFacts`) |
| each member's store names `idx id`, `cok id`, `rev id` with their fresh resources (`newServerStoreFreshA`, the two empty maps) | `newServerNames_allocL` | heap | re-sectioned; **must be global**: the claims' invariant names every member's `(idx id).slog` (`xsOf`) and every member's boot needs the claimers' facts of all members (`ΦsOf ids idx`), so they are chosen before `srvClusterBoot_alloc` |
| the client's `etcdKV γk (kvModelSt …)` (lease mode `none`) | `srvClusterBoot_alloc` | **already global** (`InvRequest.lean:297`) | to the share of the machine running the KV check (below) |
| rafthttp's `NetNames` (`streamRegInv`, deposits): `netNames_alloc` | `rafthttp/Net.lean:509` | heap | re-sectioned (T: persistent protocols and ghost deposits, audit GOOD) |
| each peer address's protocol (`http.reserve` from `httpProtoFree`, `raftProto (netRh γn)`) | `netHttp_reserveL` | the closed-world net/http model | **S5's** per-address registration, set from `addrUnset peer_i` as S2's `grpc_addr_set` sets a client address; until S5 there is no cross-machine raft transport, so a `k > 1` theorem waits for it anyway |
| per member `i`: `γE_i`, the publication invariant at `Pub_i`, its client address set to `etcdSvc γE_i mid_i` | S2 (`S2Draft`: `envPub_alloc`, `envPubInv_alloc`, `grpc_addr_set`) | — | `putget_start` for `k` members (order of work, (a)) |

`(0) ↪[issued]□`, ghost map elements, `ghostMapAuth`, `etcdKV`, `raftStateU`, `nodeVacantU`, `isClusterU`
are already over the global classes.

**2. A member's share and its boot.** The start hands member `i` (id `id_i`): the **cluster's persistent
facts** `clusterFacts γ γk issued cnt wn fs` (the six persistent conjuncts `memberBoot_of` takes) and its
**slice** `memberSliceG id_i` (its claims entry, key fact, `nodeBootG`, `raftState`, `nodeVacant`, snapshot
directory, wait token, store names' fresh resources, `cok`, `rev`), the pure facts `memberBoots_of` needs
(`ΦsOf`, `xsOf` at its prefix, `kvPfxOk γk`, `¬ clusterNoSnap`), its S2 share (`memberShare`), and, as today,
nothing of the other members. Its boot (heap, its own `HeapGS ⟨G, L⟩`):

1. `bootMarshal ps ctxs boot` at its own heap from `etcdstart.premises` (the statement's `Hprem` holds at
   every heap), and `nodeBootG γ.cl N ps ctxs id ∗ bootMarshal … ⊢ nodeBoot γ.cl N ps ctxs id` (a raft API
   law), turning `memberSliceG` into today's slice;
2. its storage registry `ghostMapAuth (reg) 1 ∅` allocated locally (it names heap `Loc`s of this machine's
   `MemoryStorage`; nothing global mentions it: `srvClusterBoot_alloc` only copies it into `SrvRaft.reg`, which
   `memberGOk` lets differ per member);
3. `memberBoot_of` unchanged: `ρ` (request names: `srvMemberBoot_alloc`) allocated locally, giving
   `memberBoot { γ with reg } ctxs ρ (env₀ …) (ΦsOf ids idx) id cmp lm`, then the single-process member proof
   (`newServer` / `StartServer`, `Serve`) as `putget.Member` does.

So **`memberBoot`, `MemberG`, `memberGOk`, `ReqNames` and `AEnv` stay heap-level and unsplit (audit S1-S4)**:
each is built and used inside one member. The audit's "split memberBoot" is not needed: only its inputs are
split, and they already arrive in two parts (`memberBoot_of`'s persistent arguments and its slice).

**3. How a member's server state is tied to the cluster without one heap.** Through names only: the member's
`ρ.rd.raft = ⟨{γ with reg}, [], 0⟩`, `ρ.rd.kv` `kvSame` the cluster's `γk` (`memberBoot_of`'s pure post),
and the cluster's invariants (`kvInv`, `srvRaftLogInv`, `idClusterInv`, raft's `clusterInv`) as global
persistent facts every member holds. Nothing in them names a `Loc` or a WP. Raft's node of member `i` reaches
the others' through rafthttp (S5), whose deposits are global ghost state (T).

**4. How clients reach the cluster's one KV state** (D8's kv instance). Two parts:
- **the state**: `etcdKV γk (kvModelSt γk boot)` is allocated once, in the start, and goes to the share of the
  one machine that checks KV linearizability (the `kv` workload's orchestrator, which allocates `linkvInv`
  /`putGetInv` from it at its own heap, as the single-process drivers do from `alloc*`'s `etcdKV`). With
  several workloads (Q1, a key prefix each) `etcdKV` is still one element: splitting it by prefix is D8/D9's,
  not D7's; the interim theorem with one KV-reading workload needs no split.
- **the members' services**: member `i` publishes its view `ν_i` at `γE_i` with `Pub_i ν_i`, where the start
  fixes `Pub_i ν := ⌜viewAgrees γ γk ν⌝` (its read names' raft names the cluster's `γ` up to `reg`, its KV
  names `kvSame γk`, its prefix `idPfxOf id_i`): exactly `memberGOk`'s facts, which `memberBoot_of`'s post
  gives the member. A client's `kvRegsPub_at` then gives `client.kvRegsAt ⟨a_i, etcdEnvOf ν_i, …⟩` whose names
  agree with `γk`, which is what `linkvInv`'s users take today from `memberGOk` (`memberAt`/`clusterAt` of
  `cluster3`, audit S8: these become "the views published at `γE_1 … γE_k` agree with `γk`").

**5. What the single-process lemmas become** (step 3: factored, not duplicated):
- `newServerNames_allocL`, `srvClusterBoot_alloc`, `netNames_alloc`: re-sectioned global; `allocN`/`alloc3`/
  `alloc1` (and their `On` variants) call them unchanged (a global lemma applies at a heap).
- `allocN` = `clusterAllocN` (new: (1)-(2) at the global classes, returning `clusterFacts` and the slices) then
  `memberBoots_of`; the distributed start uses `clusterAllocN` + the S2 start; each member's boot uses
  `memberBoot_of`. `memberBoots_of` stays (single process only).
- `cluster_alloc_boot_impl_tr` = `cluster_alloc_bootG` + framing `bootMarshal` into each `nodeBootG`.
- `memberStartRes_split`, `StartMembers*` (one thread starts all), `cluster3`'s records, `Partitioner`/
  `PeerStep` (audit S6-S9): single-process only; the distributed members start themselves, partitions are the
  network's (§6), so they are not ported.
- `etcd_adequate_members_below` (branch `single-process-restore`): unchanged; it keeps allocating in one process
  through the same factored lemmas.

**6. Out of scope here, and where it plugs in.** Crashes: a member's slice is handed to its first boot; with
crashes it goes into a per-member crash invariant at the start (`srvDiskImage`, `InvRestart`), from which every
boot (first or restarted, `haveWAL`) takes what its files justify (D6's one `NewServer` spec). `raftState`/
`nodeVacant`, the snapshot directory's auth and `ρ`'s maps are the parts a restart must rebuild from files
(audit "restart hard points"); the global facts of §1 survive unchanged (`kvInv_restartNames`). The issue
record (`idIssueExt`) keyed by incarnation is D4's. The start resources that are not ghost state
(`dataDirFresh`, `nameFree`, `envVerifyOff`, `addrClaim`) are `notes/putget-dist-plan.md` §7's, per member.

**Disagreements with the audit.**
- **`nodeBootU` is not G**: it holds `bootMarshal` (`InvApiBoot.lean:63`), a persistent WP of
  `proto.Marshal` at the holder's heap. Its split is a raft API change: `nodeBootG` (the rest, global) and the
  law `nodeBootG ∗ bootMarshal ⊢ nodeBoot` (heap); `cluster_alloc_bootG` gives `nodeBootG`. kvraft never met
  this: its cluster has no bootstrap log (`cluster_alloc_nb`, already global).
- **The server's G items are heap-sectioned in Lean** (`srvRaftLogInv`, `kvInv`, `idClusterInv`,
  `srvPropMint`, `srvRdCtxInv`, `idKeyFactAt`, `idWaitTokAt`, `newServerStoreFreshA`, `netNames`, and their
  allocation lemmas): "retype only" is a re-sectioning of about ten definitions and their alloc lemmas, but its
  rebuild cone is large (`NewServerAlloc.lean` reaches 935 modules; raft's `InvNodeRule.lean` 2639).
- **`memberBoot`, `MemberG`, `ReqNames`, `AEnv` need no split** (§2): built in the member's boot.
- **The per-member store names `idx` are global** (§1), not node-local; the storage registry `reg` is local.
- **`rdPool`'s receipts are global**: `⧗`/`ReceiptGS` are part of `GooseGlobalGS`, and the pool is allocated
  in the start; the bound counts all machines' steps (§1), so one pool is right.
- `isGrpcRpcAt` (T): agreed, S2's redefinition (`grpcAddrAt`, `kvRegsPub`); `cid` in the view (#24 05:09Z).

**Order of work.** (a) the S2 start for `k` members over `S2Draft` (cheap, global, no rebuild of the tree);
(b) `clusterAllocN`/`memberBoot_of` factoring of `allocN` (etcdstart only, 31 modules); (c) raft's `nodeBootG`,
`cluster_alloc_bootG` and the law (raft API; interfaces, the `RaftTla`/`RaftNoAx`/`KvRaft` copies regenerated;
a 2639-module rebuild); (d) the server re-sectioning (935 modules) and `clusterAllocN` at the global classes;
(e) `etcdClusterStart` = (d) + (a), and a `k`-member boot skeleton `EtcdBootsS2` as putget's `BootsS2`. (c)
and (d) are mechanical but rebuild most of the tree: to schedule with the coordinator (build slots).
(d) is checked by the heap-free gate (`etc/heapfree-check.py`, phase 7 S2's): `clusterFacts`, `memberSliceG`
and the start's other outputs become roots, so no `HeapGS` is reachable from what the start hands out. The auth-on
allocation (`allocNOnM`, `srvClusterBootOn_alloc`, `kvInvOn`) has the same cut (`clusterFactsOn`), after the
auth-off one. **(c) and (d) held** (the coordinator, 2026-11-23: they touch files other sessions are editing;
sequenced on #28).

**Done (2026-11-23, branch `d7-split`; no axiom, no `sorry`, no statement of an existing result changed).**
- (a) `Proof/.../examples/etcd/dist/ClusterStart.lean`: `cluster_svc_start` (and `cluster_svc_start_list`), proved
  from `S2Draft`'s fields: for members `ms` (client address, member id) and a `Pub` per member id, from the
  protocol registry and every member address's `addrUnset`, the slot map once and per member `γE`, the publication
  invariant and its address set to `etcdSvc γE id`; returns each member's `memberSvcShare` and the clients'
  persistent `clientSvcFacts` (every member's `kvRegsPub` and publication invariant). `putget_start` is its
  one-member case (not yet rewritten as its corollary: it lives in the putget skeleton, `putgetGF`).
  (2026-11-24, `notes/putget-dist-plan.md` §12) Restated over the interim vocabulary (`S2Interim.lean`):
  per member `envPub_start` and `etcdAddr_set`; `memberSvcShare` holds `etcdAddrAt`, `clientSvcFacts` each
  member's `etcdAddrAt` and publication invariant; no slot map (inside `etcdAddrAt`'s interpretation), so
  `cluster_svc_start_list` is gone.
- (b) `etcdstart/AllocN.lean`: `clusterFacts` (persistent: `memberBoot_of`'s six persistent arguments),
  `memberSlice` (a member's exclusive part, today with `nodeBoot`), `memberBoot_of_slice` (a member's boot step),
  `clusterAllocN` (the cluster's part: `newServerNames_allocL` + `srvClusterBoot_alloc`, returning the facts, the
  slices over `ids` and the client's `etcdKV`), `memberBoots_of` restated over the slices; `allocN` is now
  `clusterAllocN` then `memberBoots_of` then the network, its statement unchanged (every driver unchanged).
  Still at a heap: `clusterAllocN` moves to the global classes with (c) and (d), its statement then the global
  start's. The auth-on `allocNOnM` is not cut yet (same shape, `clusterFactsOn`).

**(d), the re-sectioning (branch `d7-resection`, 2026-11-23).** Moved to global sections (over
`[GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]`, as `KVStoreApi`'s `defs`), statements unchanged, roots of the heap-free
gate (`etc/heapfree-roots.txt`): `SrvRaftLog` (`srvPropTk`, `srvQInv`, `srvReadAu`, `srvLogCore`, `srvPendRead`,
`srvLogRegs`, `srvLogInv`, `srvSnapsReg`, `srvClusterOk` (its unused `letI := srvStor` dropped), `srvRaftLogInv`,
`srvRdCtxInv`, `srvRdCtxInv_alloc`); `InvRequest` (`idRegdAt`, `entryClaim`, `kvWork`, `kvGrantIds`,
`kvGrantIds_nil`, `kvInv`, `floorAt`, `srvFloorFacts`); `InvProposer` (`srvPropMint`); `KVStoreApi`
(`newServerStoreFreshA`); `BuildAlloc` (`buildGhostVarHalves`, `entryClaims_conf`, `kvInv_alloc_boot`,
`srvPropMint_alloc`); `NewServerAlloc` (`newServerNames_alloc`); idutil (`idUnclaimed`, `idClaim`, `idClaimAny`,
`idNoZero`, `idKeyFactAt`, `idShare`, `idWaitTokAt`, `idWaitTok`, `idWaitIs`); `wait` (`waitRegd`); rafthttp
(`netSlot`, `netNames_alloc`, `streamRegInv`). **Not heap-free, left at a heap:** `idClusterInv` (below; a negative
test of the gate), hence `idCluster_alloc`, `srvClusterBoot_alloc`, `clusterFacts`, `clusterAllocN`; and `nodeBoot`
(step (c)). rafthttp's payload `srvNet γ` (message bundles on the receiver's heap) is S5's.

**(c), raft's `nodeBootG` (branch `d7-nodeboot`, 2026-11-23).** `InvApiBoot`: `ApiImpl.nodeBootUG` (`nodeBootU` but
`bootMarshal`), `cluster_alloc_boot_implG_tr` (the allocation over `[AllG] [ReceiptGS] [InvGS]`, its post also giving
`γ.raft.reBoot = toEntries boot 0`), `nodeBootU_of_G` (`nodeBootUG ∗ bootMarshal ⊣⊢ nodeBootU`), and
`cluster_alloc_boot_impl_tr` now its corollary (statement unchanged). The node API (`InvNodeRule`, sealed):
`nodeBootG γ N vs ctxs id bl` (`@[no_expose]`, persistent), `cluster_alloc_bootG` (`cluster_alloc_ns`'s boot case over
the global classes, each voter's `nodeBootG` at `toEntries boot 0`), and the law `nodeBoot_of_G : nodeBootG … bl ∗
bootMarshal vs ctxs bl ⊢ nodeBoot …` at a heap. Additive: no statement changed; `RaftTla`/`RaftNoAx`/`KvRaft` copies
regenerated; heap-free roots, `nodeBoot` a negative test. `srvClusterBoot_alloc` can now take the raft part from
`cluster_alloc_bootG`; it stays at a heap until the idutil split.

#### The idutil split (design, 2026-11-23; accepted on #28, implemented on `d7-idsplit`)

**The defect.** `idClusterInv issued cnt wn fs Φs` (`idutil/Defs.lean`), the cluster's claims, holds for every key
`k` with a generator `g` (`C !! k = some (L, some g)`) `idKeyGenFacts k e`: `g`'s `prefix` field
(`structFieldRef Generator "prefix" g ↦□ k.1`, a points-to on the heap of the machine running `g`) and, for each id
of `L`, `idIssueFragD id g` (the issue record of `idIssueExt`, the **local** ghost state of that machine,
`GooseLocalGS`); and `idClusterOk`'s clause "distinct keys' generators distinct" compares the `Loc`s of all keys.
In one process this is sound; across machines one global invariant cannot hold points-to and local-extension facts
of several heaps, and two machines' `Loc`s may be equal. So the cluster's claims cannot be allocated by the
distributed start as they are.

**What the generator facts are for** (the proofs that open them): (U1) `NewGenerator`: the new generator `g` is
fresh (it owns `g.prefix` whole), so no key's `↦□` names it: the distinctness clause is kept; (U2)
`Generator.Next`: an id `id` just issued by `g` (the record's fresh `idIssueFrag id g`) is not in the issued map
already: if a key `k'` had it, its generator `g'` holds `idIssueFragD id g'`, so `g' = g` (`idIssueFragD_agree`),
so `k' = k` (distinctness), and `k`'s own count rules it out. **Both arguments are per prefix**: an id's key has the
id's prefix (`idClusterOk`'s second clause: `idPfx id = k.1`), so (U2) only meets keys `k'` with `k'.1 = k.1`, and
(U1) needs distinctness only among them. And a prefix is one member's (the member id's 16 low bits, distinct:
`BootCore.lowNodup`), so all keys of a prefix (the member's incarnations) live on **one machine**.

**The split.**
- **Global** (heap-free; allocated by the distributed start; same name and parameters):
  `idClusterInv issued cnt wn fs Φs` keeps the issued map `I`, the keys' entries `C : GMap IdKey IdKeyEntry` (the
  `Option Loc` kept as data: compared only between keys of one prefix, so of one machine), the registries `R`, the
  facts `Fm`, `idClusterOk` with the generator clauses restricted to keys of one prefix, and the claimers' facts;
  **without `idKeyGenFacts`**. Each key's entry is split in two halves (`ghostMapElem` at `1/2`): one in the key's
  generator (`idGen`'s invariant, as today the whole), one in its prefix's invariant (below).
- **Per prefix, on the member's heap**: `idPfxInv γi.gen p` (persistent, new, heap-level): an invariant holding, for
  every key `(p, inc)` with a generator, the other half of its entry and its `idKeyGenFacts`. Its ghost name is
  published once per prefix in a new global map `gen` (`p ↪[gen]□ γpg`, a new field `IdNames.gen` and a new
  parameter of `idCluster_alloc`'s output), so that every incarnation of the member finds the same one. (U1) and
  (U2) open it instead of the cluster's invariant; nothing else does.
- **Allocation**: the distributed start allocates `idClusterInv` and, per member, the token `p ↪[gen] none` in the
  member's slice; the member's boot allocates `idPfxInv` at its own heap and sets the token. The single process does
  the same per member (`memberBoot_of`).

**Statements that change** (definitions' bodies aside):
- `idutil`: `IdNames` gains `gen`; `idClusterInv`'s body (type unchanged); `idClusterOk`'s generator clauses
  (per prefix); new `idPfxInv`, `idPfxInv_alloc`; `idCluster_alloc`'s post (the `gen` map's tokens per prefix);
  `idGen`'s body (the entry's half, `idPfxInv`); `NewGenerator.spec` (pre: `idPfxInv γi.gen γi.pfx`).
  `Generator.Next.spec` unchanged (over `idGen`).
- server: `NewServer.spec` and `NewServerR.spec` (pre: `idPfxInv`, passed to `NewGenerator`);
  `srvClusterBoot_alloc`/`On` (the per-member token in their per-member output); `memberBoot`/`memberBootOn`
  (`idPfxInv ρ.ids.gen ρ.ids.pfx`); `memberBoot_of`/`memberSlice` (the token), `alloc1`/`alloc3`/`allocN`/`On` and
  the restart's `Restart.lean` (its four uses) follow; `InvRequest`/`Results` (one use each).
- **No top-level theorem's statement changes**: checked on `lean` (`FETCH_HEAD` 2026-11-23) that no
  `TopLevelRobustness` or `TopLevelDefs` (single-process `etcd/all`, `k8s/all`, `leaseexpiryN`, `mvccfull`, the dist
  ones) names `idClusterInv`, `idGen`, `idShare`, `memberBoot`, `NewGenerator` or `idKeyGenFacts` (`etcd/all`'s one
  match is prose naming `idIssueExt`), and that `etcdstart.premises` and `bootstrapContract` do not; they reach the
  changed definitions only through proofs. To recheck by `#print axioms`-free statement diff when implemented
  (`etc/gen-interface.py` on the closed results' modules).

**F3/D4 (the issue record after a crash).** The split puts the record's facts where the record lives: `idPfxInv` is
on the machine whose extension state holds `idIssueFrag`. With crashes, `idPfxInv` must survive a crash of its
machine (its keys' facts are about ids already issued); that is the issue record's crash semantics, D4's: keyed by
incarnation (`idIssueFrag id (epoch, g)`), the record survives and a restarted generator at an old address cannot be
confused with the old one, so (U2)'s `g' = g` then compares `(epoch, g)` pairs. Today's `Restart.lean` (single
process, `HardStop`, no crash) keeps the heap, so nothing changes for it. The global part has no crash concern.

Ledger: `notes/specs-only/ledger.md`, 2026-11-23, "idutil's cluster claims hold every machine's generator facts".

**Implemented (`d7-idsplit`, 2026-11-23).** As designed, refined: each prefix's two names (its ids' map `γip`, its
generators' map `γgp`) are allocated by `idCluster_alloc` and recorded persistently in the new map `IdNames.gen`
(`p ↪[gen]□ (γip, γgp)`; `idPfxTok gen p` the fresh pair, `idPfxInv_alloc` the member's step); the global
invariant's `idKeyGenFacts gen k e` keeps heap-free records (`g ↪[γgp]□ k`, `id ↪[γip]□ g`), `idPfxInv gen p` their
heap halves; `idClusterInv` gains the parameter `gen`. `NewGenerator`/`Next` re-proved over both invariants;
`srvClusterBoot_allocG` (no `bootMarshal`, `nodeBootG`, `idPfxTok`s) with `srvClusterBoot_alloc` its corollary;
etcdstart's `clusterFacts`, `memberSlice` (`nodeBootG`, `idPfxTok`) and `clusterAllocN` heap-free;
`memberBoot_of_slice` (the member's boot: `bootMarshal`, `idPfxInv_alloc`, `memberBoot_of`). So the distributed
start's cluster allocation is `clusterAllocN` (plus the S2 start, `cluster_svc_start`); what is left for D7's no-crash
part is the `k`-member boot skeleton, which waits for S5 (the peers' transport) and D2 (the server program).

### D9: the interim statement and its skeleton (2026-11-23, coordinator-E; branch `dist-d9-skel/2026-11-23`)

- **Two statements** in `Spec/.../examples/etcd/dist/TopLevelRobustness.lean`, both over the fixed bundle
  `etcdNetExts` (an unprovable quantification over any extension list dropped: the bridge needs the bundle's
  `GooseGpreS`, `etcdDistGF`): `etcd_robust.spec` (`etcd_safe`, crashes) and **`etcd_robust_nocrash.spec`**
  (`etcd_safe_nocrash`, no machine crashing, Q7; the weaker variant takes the longer name). Both take
  `putget_safe`'s `HEnv`/`HEnvTok` and the bound `2 ^ 28 - 1` (until perennial#690). **Not instantiable**
  until the k-member boot replaces the opaque `TrustBoundary` and D2 the opaque programs.
- **D8's machines in the deployment** (`TopLevelDefs.lean`): `Workload.nodeCount` (Go's `NodeCount`),
  `Deployment.nodes` (each workload's client machines' addresses), `nodeList`, `nodeProg`
  (`client.NodeMain`), `clientProg w eps nodes` (`client.MainReady`), `machines` (members, orchestrators,
  client machines); `WellFormed` gains the node counts and covers the node addresses (`addrs`). The Go
  mirror (`examples/etcd/dist/deployment`'s `WellFormed`) checks them since 2026-11-24 (§11.2).
- **The skeleton** (`Proof/.../examples/etcd/dist/TopLevelRobustness.lean`): `etcd_safe_nocrash_of_boot`
  (from `EtcdBootNC`, by `robust_of_distBootIL`). Next: the reduction from S2's names (`S2Holds GF`, now
  generic in `putget/S2Draft.lean`, at `etcdDistGF`), S5's (`S5Holds`, `dist/S5Draft.lean`: `httpAddrAt`,
  `http_addr_set`; its fields to be agreed with proving session 2) and D7's `etcdClusterStart`, once the
  interim S2 interface fixes the member's and client's shares.

### D2's `net` half: the net swap (plan, 2026-11-22; not started, decisions below)

**Decided (the user, 2026-11-22, relayed by the coordinator).** (1) **Retire** the single-process `etcd_robust`/`etcd_safe`,
`k8s_robust`/`k8s_safe` and leaseexpiryN's closed theorem at the swap, not adapt them: option (i) and steps
3-4 below are superseded. The coordinator tags the last `lean` commit where they are proved
`single-process-final` (for the paper). **Names** (Upamanyu, #24, 2026-11-22): the distributed theorems take
the plain names, weaker variants the longer ones: this plan's `etcd_dist_safe` is now `etcd_safe` (its
statement `etcd_robust.spec`), the retired single-process theorem's names. Removed: their `TopLevelRobustness` (Spec and Proof), `Results`, `Adequacy`, `TopLevelDefs`,
`Disjoint`, `PkgTable` and their collections (`etcd-all`, `k8s-all`, `leaseexpiryN`); kept: every
per-function proof (`Main`, `MainLinked`, `Init`, `InitLinked`, the drivers' proofs), the generic machinery,
the Go drivers and their tests. (2) **Design D** for the address predicates; `net.Listen` a theorem from
Net's spec. (3) **The start axiom's address part removed** if nothing left uses it (checked: only the
retired theorems, through etcdstart's `etcd_adequate*`/`AdequacyMembers`, which go with them; `mvccfull`
and `mvccrand` pass `As = []`), as one removal-only change with `prom-registry`'s names part (below,
"The combined start statement"). (4) Start now; merge `lean` when #30's `step-bounds-backend` lands.

**The combined start statement** (this branch's address part and `prom-registry`'s names part; removal only,
nothing added). Before (`lean`): `startRights Ns As Ds := ([∗list] n ∈ Ns, prometheus.nameFree n) ∗
([∗list] a ∈ As, netAddrFree a) ∗ ([∗list] a ∈ As, httpProtoFree a) ∗ ([∗list] d ∈ Ds, dataDirFresh d) ∗
envVerifyOff`, and `goose_adequacy_start … (Ns As Ds) (hNs : Ns.Nodup) (hAs : As.Nodup) (hDs : Ds.Nodup)
(hAsLit : ∀ a ∈ As, netAddrLit a = true) (hNsFree : prometheus.namesUnclaimed e Ns) (hAsFree :
addrsUnclaimed e As) (hDsFree : dataDirsAbsent e Ds) (hEnv : verifyEnvOff e) (Hwp : … -∗ startRights Ns As Ds
={⊤}=∗ WP e …) …`. After both:

```lean
def startRights {GF : BundledGFunctors} [GooseExts] (Ds : List GoString) : IProp GF :=
  iprop(([∗list] d ∈ Ds, dataDirFresh d) ∗ envVerifyOff)

axiom goose_adequacy_start [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ds : List GoString) (hDs : Ds.Nodup) (hDsFree : dataDirsAbsent e Ds) (hEnv : verifyEnvOff e)
    (Hwp : ∀ [hG : HeapGS .hasLC GF], receiptBound GF = N → threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗ extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok -∗ startRights (GF := GF) Ds ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1) : …   -- conclusion unchanged
```

and `goose_adequacy_start_all` the same way (without `hNsIds`). Gone with the address part: `addrUnclaimed`
(axiom), `addrsUnclaimed`, the `netAddrFree`/`httpProtoFree` hand-out, `hAsLit`. `netAddrLit` stays (a
definition the drivers' `Dir` lemmas prove of their addresses). `httpProtoFree` stays an axiomatized
predicate of net/http's (`http.reserve`, S5) with no source; `addrClaim` (design D) likewise, until
`etcd_safe`'s deployment premise gives it.

**Conflicts with `prom-registry`** (`/shared/etcd-grove-promreg`, at `8af09c0669`): both edit
`Proof/runtime/Start.lean` (the two removals: whichever lands second takes the other's text above),
etcdstart's `Adequacy.lean` (its `etcd_adequate*` take `Ns`; here they go), `mvccfull`/`mvccrand`'s `Adequacy`
call sites of `goose_adequacy_start` (each drops its own arguments), the retired programs' `PkgTable`s and
`etc/tcb-collections/{etcd-all,k8s-all,leaseexpiryN}.txt` (`prom-registry` edits them, this branch deletes
them: take the deletion), `etc/tcb-baseline.txt`, `etc/tcb-collections/mvccfull.txt`, `etc/goose.py` and
`etc/gen-init.py` (independent hunks). Its planned step-2 edits to etcd/all's, k8s/all's and leaseexpiryN's
closed proofs (§5 of `notes/prom-registry-start-change.md`) are moot after the retirement.

**Done on `net-swap` (2026-11-22, `df4369bae2`; built against a plain Perennial `74471ecd8` worktree,
`/shared/perennial-74471ecd8`, manifest `/shared/tmp/manifest-744.json`).**
- Translation: `net=Net` in the 35 main-tree projects (with `net/{http,url,textproto,http/httptrace}=` kept
  main-tree); `Code/net.{toml,lean}`, `GeneratedProof/net.lean` deleted; 30 translations regenerated (their
  import line only). gen-init: the main tree's `Proof/net/Init.lean` over Net's translation (its fact
  `Net/Proof/net/Base.lean`'s `isInit`; `cache/v3/Base.lean`'s `True` instance for `net` removed);
  `net.opaqueInitsOk` gone. gen-specs-pkginit: `SpecPlan.Spec.PkgInit.net` over `Net.GeneratedProof.net`.
- Design D, with one change: the predicates carry `HasExt netExt` **inside** (`∃ _ : HasExt netExt, …`, a
  proposition, so proof-irrelevant), so that no section needs a `[HasExt Net.netExt]` binder: no sweep, and
  **no edit to upamanyus's grpc, v3rpc or net/http files** (their statements over `netListenerAt` keep their
  signatures). `netListenerAt` ties `l` to a `*TCPListener` pointer but not that pointer to the extension's
  listener id (`isListener` would need `net.Assumptions` at every use); S2 may strengthen it.
- `EtcdGrove.net.Listen.wp_proof` a theorem from Net's `net.Listen.wp_proof` (an `=` callee in
  `etc/link-lean-first-{common,cluster3}.txt`, `gen-link`'s `EXTRA_IMPORTS`).
  Net's `Listen` spec takes Net's hand-stated field facts (`net.FieldAssumptions`, trusted, as
  `os.file.FieldAssumptions`): a semantic premise (`gen-link`'s `SEM_PREMISES`) of every linked result that
  reaches `net.Listen` (etcdstart's and cluster3's `Link`s, the Links of auth, cache, k8s/etcd3, partition,
  txnlin, watch) and of the drivers' hand-written `MainLinked`/`Results` triples (31 theorems).
- Built against Perennial `9c3b81f30` (`lean`'s pin at the last merge, `/shared/tmp/manifest-9c3b.json`); earlier
  commits of the branch against a plain `74471ecd8` worktree (`/shared/perennial-74471ecd8`,
  `/shared/tmp/manifest-744.json`).
- Retirement and the start axiom's address part: as decided above. Not done: step 5 (Net's own copies of
  the main tree's initializers), which kvremote needs next.

Branch `net-swap`. Agreed on #24 (upamanyus, 2026-11-22 15:52Z): ours, after `phase7-dial` (on `lean`,
`bbc60799b2`); `net/http` stays with phase 7 (S5). His constraints: project `etcd`'s `-lean-root net=`
becomes `net=Net` (as `models-net`), so grpc's translation sees the real `net.Conn`/`net.Listener`;
`netAddrFree`, `netListenerAt`, `httpProtoFree` and `net.Listen.wp_proof` become the net extension's
`Listen` spec plus our deployment premise; any edit to a grpc or v3rpc file of his is listed (below).
Measured at `lean` `fda4209706`, from the import lines (`etc/importers.py`) and `etc/goose.py`.

**The swap.** The main tree stops translating `net` (project `etcd` lists and owns it, names only:
`Code/net.{toml,lean}`, `GeneratedProof/net.lean`) and imports the part's (`Net/Code/net.lean`, its
trusted `Net/TrustedCode/net.lean` over `netExt`, `Net/GeneratedProof/net.lean`, `Net/ManualProof/net.lean`).
Net's translation declares every name the main tree's does (the 43 it lacks are the type-instance names of
the types it translates or defines in its trusted code: `Conn.underlying`, `TCPConn`, ...), and covers what translated main-tree code uses: the types `Conn`, `Listener`,
`Addr` (grpc, its `credentials`, `peer`, `stats`), `net.Listen` (etcdstart, cluster3, auth3, restart,
restartN), `net.Dial` and the listener's and connection's methods (third_party/bridge). goose's lean roots
are longest-prefix, and `net=` covers `net/http`, `net/url`, `net/textproto`, `net/http/httptrace`, which stay
the main tree's: each of the **35 main-tree projects** with `net=` (etcd, common, cluster3, the etcd and k8s
examples, bridge, etcd-all, k8s-all, ...) gets those four explicitly and `net=Net`.

**What breaks.**
- **Translations**: 11 `Code/` modules import `Code.net` directly (grpc, grpc/credentials, grpc/peer,
  grpc/stats, rafthttp, etcdstart, cluster3, auth3, restart, restartN, bridge), 22 `GeneratedProof/`
  modules `GeneratedProof.net`; all 65 projects regenerated (`etc/goose.py`), then `etc/gen-init.py`,
  `gen-specs-pkginit`, `gen-raft-tla`, `copy-part`.
- **Package init**: the main tree's `Proof/net/Init.lean` (gen-init; `net.opaqueInitsOk` over the four
  blanks goose cannot skip) is regenerated over Net's translation (gen-init's `NET_SPECIAL['net']`: Net's
  trusted initializers, which do nothing but allocate `errClosed`); it cannot be `Net/Proof/net/Init.lean`,
  which imports Net's copies of `os`'s, `syscall`'s, `internal/poll`'s ... `Init` and of `PkgInitExt`, under
  the main tree's names. Every closed program's `PkgTable` is regenerated.
- **Specs and proofs**: 73 files mention `netAddrFree`/`netListenerAt`/`httpProtoFree` (14 `netListenerAt`),
  17 use `net.Listen`'s spec (etcdstart, cluster3, auth3, restart, restartN and their `Link`/`MainLinked`),
  29 `etcdFsExts`, 9 `Dir*.lean` prove `netAddrLit` of their programs' addresses. Upamanyu's: the
  grpc server's `grpc.start` and `InvGrpcRun`, v3rpc's `etcd_noRefusal`/`etcd_noOtherRefusal`, net/http's
  `register` and the `ListenerClose` drafts consume `netListenerAt` (edits below).
- **The four bridge axioms** (`bridge.New`, `Blackhole`, `Unblackhole`, `DropConnections`) are over
  translated code that will call the net extension (`net.Dial`, `Accept`, `Conn.Read`/`Write`): their
  soundness argument changes (the clients' grpc connections are not the extension's, so the bridge's
  `Accept` never returns in the model); to be re-reviewed (the `axiom` skill). #18 lists `bridge`: prove it
  after the swap, over Net's proved `Dial`/`Accept`/`Conn` specs, or it is redone.
- **SpecPlan**: `SpecPlan.Spec.PkgInit.net` (generated) and `SpecPlan/Spec/net/http/Api.lean` (imports
  `GeneratedProof.net`, by hand).
- **The trust base**: in `etc/tcb-baseline.txt`, `net.Listen.wp_proof`, `netAddrFree`, `netListenerAt`,
  `httpProtoFree`, `goose_adequacy_start`, `addrUnclaimed`, `Perennial.net.opaqueInitsOk`. Collections:
  `etcd-all`, `k8s-all`, `leaseexpiryN` hold all seven; `mvccfull` five (not `net.Listen`/`netListenerAt`:
  its program listens nowhere, the start axiom's statement names them); `client` and `cache-client` only
  `netListenerAt` (the vocabulary of their exported results). **Closed theorems that depend on them**:
  `etcd_robust` (etcd/all), `k8s_robust` (k8s/all) and leaseexpiryN's, which listen; `mvccfull`'s and
  `mvccrand`'s through `goose_adequacy_start` and `net`'s initializer only.
- **Parts**: RaftNoAx (13 modules), RaftTla (12), RaftWitness (12) and WalTester (4) reach `Code.net`
  through main-tree modules (cache's `Base`, etcdstart's `Adequacy`/`TopLevelDefs`/`DurableExt`, the WAL's
  `Init`/`Link`); afterwards they reach Net's `net` and `GooseLang/Ext/Net` instead: no clash (none declares
  `net`'s names), no axiom added. KvRaft keeps its own `net` (`net=KvRaft`) and never reaches the main tree's.
  `Net/` stops being closed to the main tree: `CLAUDE.md`'s layout and `Net/Code/net.toml`'s header say so.
- **Left after the swap, for kvremote**: (1) Net's own `net/http`, `net/textproto`, `net/rpc` (project
  `models-net`) still declare the main tree's names-only `Code/net/{http,textproto}`'s names until S5.
  clientv3's translation reaches neither, but txnlin's `Defs` reaches the main tree's (rafthttp, through
  the server): a `Net/` module importing txnlin must not reach models-net's modules (remote's closure
  reaches none today). (2) Net's copies of the main tree's initializers (gen-init's `NET_MAIN`: `os`,
  `syscall`, `internal/poll`, `io/fs`, `internal/syscall/unix`, porcupine, lintest and its two instances,
  and `PkgInitExt`) clash with the main tree's in a closure holding both remote's and clientv3's: they are
  retired, `Net/` importing the main tree's (step 5); `etc/copy-part.py --check` then checks that KvRaft,
  which copies `Net/`, still gets only its own.

**The main tree: what each closed statement becomes.** Keeping `net.Listen.wp_proof` an axiom is not an
option: its body is now the trusted `Listen.impl`, `ExternalOp netExt.name "Listen"`, stuck in a program
without the net extension, so a WP for it under `NotStuck` would be false. The programs that listen must
run over the net extension.

- **(i), recommended: single-process, the net extension present.** The three listening programs stay one
  process (`Robust [] [(e, σ)] g`), over a new bundle `etcdNetExts := ⟨[idIssueExt, Fs.fsExt,
  Net.netExt]⟩` (semantics `(idIssue_semantics, etcdFsSem, Net.net_semantics)`, interpretation
  `(idIssue_interp, Fs.fs_interp, Net.net_interp)`, `HasExt netExt`; `net_init_compat` is on `lean`). The
  start resources give `netLisTok a` for every valid address; `net.Listen` is Net's proved spec.
  - **Predicates, design D (recommended)**: `netAddrFree a := addrClaim a ∗ netLisTok a` and
    `netListenerAt l a := addrClaim a ∗ ∃ lv, isListener l lv ∗ netLis lv a true ∗ netLisAt lv a` (Net's
    `Listen` post), definitions over `[HasExt netExt]`; `addrClaim a` the one axiomatized token left
    (exclusive, consumed once by `Listen`: `grpcAddrIs_agree`'s "one server per address" rests on it):
    `addrsUnclaimed`'s part (b), what the program's own connections to `a` carry, which the grpc and
    net/http transport axioms need until S2/S5 prove them over the extension. Main tree's
    `EtcdGrove.net.Listen.spec` keeps its shape (`netAddrFree` in, `netListenerAt` out, plus `addrOk a`)
    and becomes a theorem from Net's `net.Listen.wp_proof`. Cost: `[HasExt Net.netExt]` on every section
    that mentions the predicates or a spec over them (the 73 files and the linking modules above them);
    S2 finds the real listener inside `netListenerAt`.
  - **Design A (alternative)**: `netListenerAt l a := addrClaim a` keeps its signature (no `HasExt`, no
    edit to upamanyus's files); Net's listener resources are dropped at `Listen`, and `netLisTok a` is
    threaded beside `netAddrFree` to it (the same files carry it). S2 then redefines `netListenerAt` and
    redoes the sweep.
  - **Statement changes** (the user's decision): `etcd_robust.spec`, `k8s_robust.spec` and leaseexpiryN's
    robust spec: (1) the `attribute [local instance]` line: `etcdFsExts …` → `etcdNetExts …` (the
    semantics gains the net extension; `Robust`'s `extsInitGlobal`/`extsInitLocal` now include "no
    connection, no listener"); (2) the header: `addrsUnclaimed`'s part (a) (no other process binds or
    dials the addresses) is now the semantics' closed network, as in every `Net/` theorem; (3) `HAs` stays,
    `addrUnclaimed` narrowed to part (b). No new premise: `addrOk` of every address is proved from the
    programs' address arithmetic (ports below 32768: the largest is authN's `30000 + 300`, txnlinfaultsN's
    bridges' `28000 + 1000`). `mvccfull`/`mvccrand`: none (they stay on `etcdFsExts`; their trust base
    trades `net.opaqueInitsOk` for Net's trusted initializers). Exported results of `client/v3` and the
    cache: their vocabulary's `netListenerAt` gains `[HasExt Net.netExt]` (design D; interface diffs).
    `etcd_safe`'s draft is already over the net extension.
  - **The trusted start model** (Upamanyu's sign-off): `goose_adequacy_start`'s `startRights` hands out
    `addrClaim a` instead of `netAddrFree a` (the `netLisTok`s come from `extsGlobalStart`, never from the
    axiom: S3e's rule); `hAsLit` becomes `netAddrLit a && addrOk a` (`netAddrLit`, loopback, stays: the
    names-only `http.Transport` still reads `ProxyFromEnvironment` until S5); its satisfiability argument
    no longer reads `Listen` as a diverging names-only function. `prom-registry`'s route (b) also restates
    `goose_adequacy_start` (the names out): one before/after for both.
  - **Trust base**: −3 (`net.Listen.wp_proof`, `netListenerAt`, `net.opaqueInitsOk`); `netAddrFree` →
    `addrClaim`; `httpProtoFree` unchanged (S5's `reserve`); `goose_adequacy_start`, `addrUnclaimed`
    restated. Trusted code added to the etcd collections: `Net/TrustedCode/net.lean` and the net
    extension's semantics (`GooseLang/Ext/Net/Impl.lean`).
- **(ii), considered and not recommended.** (a) Keep the main tree's names-only `net` and put kvremote in a
  part that copies what it imports (KvRaft's way): the copy is every module reaching `Code.net`, 9,900. (b)
  Retire the three listening theorems until `etcd_safe` replaces them (D5 alone is 60-110k lines). (c)
  Go to one machine per member now (`goose_dist_adequacy`): that is D9's interim theorem; it needs D7 and
  phase 7's transport, which D2 is meant to unblock.

**Edits to upamanyus's files (design D; none to the grpc model or its configuration).**
1. `Proof/google_golang_org/grpc/InvGrpcServer.lean`: `[HasExt Net.netExt]` in the section of the axiom
   `grpc.start` (l. 417: its statement gains the instance argument, nothing else); the header's lines 7 and
   38 (`net.Listen` no longer an axiom).
2. `Proof/google_golang_org/grpc/InvGrpcRun.lean` (l. 176, over `netListenerAt`): the same binder.
3. `Proof/google_golang_org/grpc/InvGrpc.lean`: `grpcAddrIs_agree`'s docstring (one `Listen` per address:
   `addrClaim`, consumed by `Listen`).
4. `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NoRefusal.lean`: `etcd_noRefusal`,
   `etcd_noOtherRefusal` (axioms over `netListenerAt`): the binder.
5. `Proof/net/http/Axioms.lean`: `register` (over `netListenerAt`): the binder; `Boundary.lean`'s header
   (lines 13, 26-32); `ListenerClose.lean`'s drafts: `Close` giving back `netAddrFree a` cannot hold (Net's
   `Listen` takes `netLisTok` for good): give back `addrClaim a`, a re-`Listen` taking `netLisTok` again.
6. `Code/google_golang_org/grpc.lean` and its `GeneratedProof`: regenerated (they import `Net.Code.net`).

**Build cost.** `etc/importers.py --count Code/net.lean`: **9,900 modules, 1.47M lines** (Proof 4,685, Spec
3,035, SpecPlan 1,946, GeneratedProof 104, Code 81, the parts 41): the main tree's whole proof. `InvNet`:
2,441; `Spec/net/Listen`: 72; `Proof/runtime/Start`: 75; `etcdstart/FsExts`: 31. Three full rebuilds
(steps 1, 2, 4), through the build slots.

**Conflicts with work in flight** (GitHub refs, 2026-11-22 ~20:30Z; overlap with the files above):
- #30 `step-bounds-backend`: the three statements' Spec and Proof `TopLevelRobustness`, `Adequacy`,
  `Results` (etcd/all, leaseexpiryN, k8s/all): **land after it**.
- ours `prom-registry`: `etc/goose.py`, `etc/gen-init.py`, the closed programs' `PkgTable`s (generated:
  rerun), and `goose_adequacy_start` (route (b)): land it first, or one start-model change for Upamanyu.
- #24 phase 7: the files of the list above; S2 restates `grpc.start`/`acceptRun` and redefines
  `netListenerAt` over the model's transport after this. `net/http`'s S5 untouched but for the binders.
- #18 (proving session 2): `bridge` (above) and v3rpc's `NoRefusal` (the binder).
- #22 `kvnet-proof`: no file in common; `net_init_compat` and the NetFs adequacy it built are reused.
  `crc32-hooks2`: `etc/goose.py`, `etc/gen-init.py` (textual).

**Order of steps and estimate** (after the decisions, and after #30's branch lands):
1. **Translation** (1 session, a full rebuild): `etc/goose.py` (`net=Net` and the four `net/*=` in the 35
   projects; `net` out of project `etcd`'s packages and `owned`), `Code/net.{toml,lean}` and
   `GeneratedProof/net.lean` deleted, every project regenerated; gen-init (`net`'s main-tree `Init` over
   Net's translation, `PkgTable`s), gen-specs-pkginit, gen-raft-tla, copy-part; SpecPlan's import. Proofs
   change only where they named a names-only instance; `goose --check`, tier, api checks.
2. **Predicates and `Listen`** (1-2 sessions, a full rebuild): `InvNet` (`addrClaim`, the two
   definitions), `Spec/net/Listen` restated and `Proof/net/Listen` a proof from Net's (passed by the
   `Link`s), the `[HasExt Net.netExt]` sweep (the 73 files and their linking modules; upamanyus's six).
3. **Bundle and start** (1 session): `etcdNetExts` beside `etcdFsExts`; etcdstart's `Adequacy`/
   `AdequacyMembers` split `netLisTok` of the addresses from the start resources; `Start.lean` restated
   (after sign-off); `addrOk` lemmas in the nine `Dir*.lean`.
4. **Statements** (1 session, a full rebuild): the three `TopLevelRobustness` (Spec and Proof), `Results`;
   `etc/tcb-baseline.txt` and the six collections; interfaces regenerated; the bridge axioms reviewed.
5. **`Net/` opened to the main tree** (0.5 session): Net's initializer copies retired for the main
   tree's; `CLAUDE.md` and `Net/Code/net.toml`'s header; then D8's kvremote (project in `Net/`, roots
   `net=Net` with the four `net/*=`).

About 4-5 sessions; the Go programs do not change.

**Decisions needed.** The user: (1) option (i) for `etcd_robust`, `k8s_robust` and leaseexpiryN's statement
(the net extension in their semantics; part (a) of `addrsUnclaimed` into the semantics); (2) design D or
A; (3) the order against #30 and `prom-registry`. Upamanyu: (4) `goose_adequacy_start` and
`addrUnclaimed` restated (`addrClaim` for `netAddrFree`, `addrOk` in `hAsLit`, the satisfiability
argument), with `prom-registry`'s change if it goes first; (5) the edits to his six files (design D);
(6) `Net/`'s `net` imported by the main tree.

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
| F15 | low | name: `_robust` is the convention for `TopLevelRobustness`; `cmd/` JSON parsing is a trusted gap | gap **disclosed**; name kept as the coordinator asked (`etcd_safe`), the user's call |

The review also notes that F3 and F4 make two recorded nonissues reachable under real crashes
(`nonissues/etcd-request-id-restart-reuse.md`, `nonissues/etcd-watch-lagging-member-auth-off.md`):
their "Proof" sections are to be updated when the statement lands. No new Go bug was found.

## 11. Stage table and critical path (2026-11-24, `etcd_safe` lead; replaces §9's states)

Read at `lean` `b0a063163c`. Branch of this work: `etcd-safe-plan/2026-11-24`.

| Stage | State | Owner | Where |
|---|---|---|---|
| D0 statement | **redrafted** 2026-11-24 (§11.2): `etcd_safe` (crashes) and `etcd_safe_nocrash`, over `etcdNetExts`, D8's machines; no `WellFormed`/`TrustBoundary`/`NetStart`/`HNs` premise. Packet to the owner | etcd_safe lead | `Spec/.../dist/TopLevelRobustness.lean`, `Proof/.../dist/TopLevelDefs.lean` |
| D1 Go | done | — | `examples/etcd/dist` |
| D2 net swap | done (`82847d941b`); **step 5 not done** (`etc/gen-init.py` `NET_MAIN`: Net's copies of os, syscall, poll, io/fs, porcupine, lintest) | etcd_safe lead (unowned until now) | `etc/gen-init.py`, `Net/Proof/{os,syscall}/Init.lean` |
| D2 translation | **not started**: only `dist/putget` (project `putget-dist`). `server` needs `etcdserver/api/etcdhttp` (not translated) and `net/http`'s server; `client`/`kvremote` need `remote` (Net only), `walarea`, `math/rand/v2` | etcd_safe lead | `etc/goose.py` |
| D3 mixed bridge | `[net, fs]` only (`robust_of_netFsBoot{,_addrs}`, hard-wired to `kvnetExts`) | etcd_safe lead (D4c) | `Net/Statement/NetFsBridge.lean` |
| D4 bundle under crash | **not started** (§12) | etcd_safe lead | — |
| D5 transport | S0, S1, S2 interface (`6d5a98fb3d`, axioms `Invoke`/`Serve`/`NewClient`/`NewServer`/`RegisterService`/`grpc.start`) landed; S2 proofs in flight (`phase7-s2-core`); S5 server pieces in flight (`prove-ps2-s5srv`, partly landed); **S3 (streams), S4, S5 client not started** | #24 owner; proving session 2 (S5) | `notes/phase7-plan.md` |
| D6 server restart | **spec phase** (2026-11-24, `notes/etcd-dist-d6.md`: `memberGen`, `NewServer.specC`, the crash and torn-batch laws; tasks T1-T9); `NewServerR` exists for the graceful restart only | etcd_safe lead | `dist/crash/MemberGen.lean`, `etcdserver/InvCrashImage.lean`, `Spec/.../NewServerCrash.lean` |
| D7 no-crash split | `d7-idsplit` **landed** (`2f67a12c06`): `idClusterInv gen`, `srvClusterBoot_allocG`, `clusterFacts`, `clusterAllocN`, `memberBoot_of_slice`, `cluster_svc_start`. `etcdClusterStart` and the k-member boot: on `dist-putgetk/2026-11-24` (n members) | putgetK lead | `etcdstart/AllocN.lean`, `dist/ClusterStart.lean` |
| D8 clients | `remote` proved (`counter_remote_robust`, `Report`); **kv instance not started** (needs D2 step 5, D2 translation of `kvremote`, D7's one KV state); watch/cache/auth need `remote`'s ownership-carrying wire (A) | etcd_safe lead | `Net/Proof/.../lib/remote/` |
| D9 assembly | skeleton `etcd_safe_nocrash_of_boot` (from `EtcdBootNC`, `EtcdBootNCBad`); no axiom, no sorry | etcd_safe lead | `Proof/.../dist/TopLevelRobustness.lean` |
| putget milestones | `putget_safe` (2 machines; interim S2 axioms A1/A3-A5, A4/A5 false until `bridge-new-addrleft` lands), `putgetK_safe` (n members, in progress) | putget leads | `dist-putget-interim/2026-11-24`, `dist-putgetk/2026-11-24` |

### 11.1 Critical path to a closed `etcd_safe`

Sound interim axioms at a piece's interface stand in for what is proved elsewhere (S2-S5, bootstrap #34,
per-function contracts), so the path is the work nobody else does:

1. **putgetK_safe** (n members, no crash): the k-member boot over interim S2/S5 axioms. (putgetK lead.)
2. **M1 `etcd_kv_safe_nocrash`** (smallest next milestone): n members + the `kv` workload (orchestrator and
   client machines over `remote`), no crash, unary gRPC only (Txn/Range/Put: no S3). Needs D2 step 5,
   the translation of `dist/server` and of `dist/client`'s kv part with `kvremote`, the kv instance of
   `remoteDistSafe` (txnlin's model, `PendDec`, `codecOk`), and putgetK's k-member boot. A corollary-shaped
   instance of `etcd_safe_nocrash` at deployments with one `kv` workload.
3. **M2 `putget_crash_safe`** (first crash milestone; in parallel with M1): one member machine that crashes
   and restarts, the putget client stable. Exercises all of D4 and D6 with no peer transport (k = 1: no
   rafthttp traffic) and no new workload proof. Needs D4a-D4c and D6.
4. **M3 `etcd_kv_safe`**: M1 with crashing members (D6 at k members: the raft log's durability across a
   member's crash, the restart invariant of D7).
5. **`etcd_safe_nocrash`**, then **`etcd_safe`**: the remaining workloads (watch/cache need S3 or interim
   stream axioms; auth/lease rows need `remote`'s wire (A); durable is M2's check at k members).

The long poles: D6 (weeks: the restart from a crash state, per member, with the cluster's invariants
surviving it) and the workload instances (D8, ~2k lines). S3/S5 are not on the path while their interim
axioms hold.

### 11.2 The statement (2026-11-24 redraft)

- **`WellFormed` moved into the programs** (no pure premise the program can check): each machine's program
  takes the whole deployment and its index (`serverProg d i`, `clientProg d j`, `nodeProg d n`), runs
  Go's `deployment.WellFormed` (`examples/etcd/dist/deployment`, tested by `TestWellFormed`) and returns if it
  fails. Done 2026-11-24 (branch `etcd-safe-go/2026-11-24`): `server.MainDeployment(d, i)`,
  `client.MainDeployment(d, j, ready)`, `client.NodeDeployment(d, n)` (binaries `cmd/{server,client,node}`
  read the deployment's JSON and an index; the harness writes one `deployment.json`), the Go check matched to
  Lean's clause by clause (now with the client machines' addresses and counts, unknown kinds, and kv/watch/cache's
  `clients * ops` bounds); `TestDist` runs through these entry points. The skeleton case-splits:
  `EtcdBootNCBad` (malformed: the bridge at no address, every program returns after its check). This also
  removes `memberId` from the premises (Q5): Go computes it with Perennial's proved `crypto/sha1`.
- **`TrustBoundary` dropped**: Iris contract premises become per-function axioms (premises-to-axioms).
- **`NetStart` and the net halves of `ServerStart`/`ClientStart` dropped**: `Robust` itself assumes the
  extensions' initial states (net's `initLocal`/`initGlobal` are exactly `init`).
- Kept: `BootFacts` (pure, until bootstrap's results are Lean functions of `d`), `EtcdEnv`, `FsInit` (until
  D4a), `HEnv`/`HEnvTok` (approved for `putget_safe`), instance binders. Bound `2 ^ 28 - 1` (`putget_safe`'s)
  for both, until the proofs fix theirs (kvnet's crash theorem has `2 ^ 61`).
- `putget`'s `S2Holds` generalization from the D9 commit was not taken (the putget files are the putget
  leads'); the skeleton does not need it yet.

### 11.3 M1's assembly (P9, 2026-11-25, branch `etcd-safe-p9`; `notes/etcd-dist-p9.md`)

**Blocked at the instance's spec**: `remote`'s `PendDec`/`Run.spec` cannot describe txnlin's model (its
`Gen` is not a function of the model input, `decIn` is partial, `decOut` reads an output by its input's
kind, `outOf` is not injective); a generalization of `remote`'s store (wire input vs model input, a
state guard, `PendDec` "at a configuration") is proposed to the lead (`notes/etcd-dist-p9.md`, ledger
2026-11-25). The assembly below assumes it.

`etcd_kv_safe_nocrash`: `etcd_safe_nocrash`'s statement at deployments with k members and one `kv`
workload (an orchestrator machine `clientProg d 0` running `kvremote.Orch`, `Clients` client machines
`nodeProg d c` running `kvremote.Node`), under `putget_safe`'s interim S2/S5 axioms. Steps, each its own
module (linking where it uses `wp_*`):

1. **The kv store** (`dist/kvremote/Store.lean`, defs): `kvR γk : RBase GF MS MI VIn Output` with
   `sysState st := ∃ σ, etcdKV γk σ ∗ ⌜GoodKV σ ∧ absSt σ = st ∧ kvRevFits σ.rev⌝` (timeless), `Eop` the
   KV invariants' mask (`callUpd`'s), `B := TSo`, `good st := st.rev < 2 ^ 63`; `PendDec (kvR γk)
   linkvtxnS` (pure, from `decOut_outOf`, `pSeq_ok`, `pSeq_errW_pending`, `pSeq_errR`); `hinj`. (Done 2026-11-25, with `O := VOut`, outputs that fit a slice, and `good` bounding the
   state's values too: `notes/etcd-dist-p9.md`, fourth session.)
2. **The codec** (`dist/enc/*` specs and proofs; `dist/kvremote/{EncInput,DecInput,EncOutput,DecOutput,
   Codec}.lean`): `codecOk (kvR γk) (Codec())`.
3. **The client machine** (`dist/kvremote/Node.lean`): `opMaybe (kvR γk) a tok op` for `Node`'s `op`
   (`txnlin.Call.spec`, `wp_Call`; `tok cli := isNewClient cl … ∗ clientWriteOnce … ∗ kvRegsAt`s of the
   members' published views, D7 §4), then `ServeClient.spec`; `Node`'s WP: never returns.
4. **The orchestrator** (`dist/kvremote/Orch.lean`): `Run.spec` at `kvR γk`, `linkvtxnS`, `txnlin.Model`'s
   `isModel` (`Model.wp_proof`), `Gen.spec`; `Orch` returns a verdict that is not `Illegal`, so `client.RunKV`
   (`examples/etcd/dist/client/kv.go`), which panics only on `Illegal`, does not panic.
5. **The start** (`dist/kvremote/Start.lean`, global ghost state): from D7's `clusterAllocN`/
   `clusterFacts` (the cluster's `etcdKV γk` at the boot state), allocate `pendCtx (kvR γk) linkvtxnS γ`
   with `pendLib` at `pInit` (the boot state is empty: `absSt σ₀ = mInit`), `mapCtx_alloc` with budget
   `ops * readTries` per client address, `remoteAddr (kvR γk) a_c` for each client machine (remote's
   `remote_start`); hand `pendLib` and the units to the orchestrator's share, `remoteAddr` and the
   members' views to each client machine's.
   **The deployment's extensions** (P9, 2026-11-25): every machine, the client machines included, runs over
   `etcdNetExts := ⟨[idIssueExt, Fs.fsExt, Net.netExt]⟩` (`etcdstart/NetExts.lean`; `etcdNetExts_hasIdIssue`).
   The client machines need the request-ID extension: `Call_dist.spec` (the lead's statement of `Call` across
   machines, which `kvremote.Node`'s proof applies) is stated under `[HasExt idIssueExt]`, as are N2's
   `KV_*_dist`/`Txn_Commit_dist`. The bundle provides it; a bundle for client machines without
   `idIssueExt` would not.
   Done so far (`dist/kvremote/Start.lean`, defs): `kv_start` (the kv part: `mapCtx_alloc`, `pend_alloc`,
   `addrs_set_proto`) and `kv_start_deployment` (one kv workload; the members' part a hypothesis
   `member_boot_dist`, which N5 proves). Not done: step 6's use (the boot WPs, the shares
   through N7-kv's `orchShare`/`nodeShare`).
6. **The theorem** (`dist/kvremote/TopLevelRobustness.lean`, linking): `etcd_safe_nocrash_of_boot`'s
   shape with `EtcdBootNC` discharged by putgetK's k-member boot (`member_bootK`; `dist-putgetk`) for the
   members, step 5 for the start, steps 3-4 for the client and orchestrator machines; `EtcdBootNCBad`
   as today.

Sizes: 1 ~300 lines, 2 ~700 (enc ~300, the codec ~400), 3 ~250, 4 ~200, 5 ~300, 6 ~250; the `remote`
generalization ~150 more.

## 12. The crash plan: D4 (the bundle under crash) and D6 (server restart)

Specs first, then invariants, then proofs in parallel.

**D4a. `fsSemWithS` gets `initLocal := FsInit`** (trusted semantics, small). Today `fsSemWithS`
(`GooseLang/Ext/Fs/Premises.lean:37`) keeps the default `initLocal` (any state), so every theorem over
`etcdFsSem` carries `FsInit` as a premise. With it, `FsInit` is `Robust`'s own assumption, as for
`fs_semantics` (`Fs/Impl.lean:1330`). Owner sign-off (a trusted change). Independent of everything else.

**D4b. The issue record keyed by incarnation, with a crash interpretation** (trusted semantics + axiom
review). Today `IdIssueState := GMap w64 Loc` survives a crash unchanged (`IdIssue/Impl.lean:40,77`) and
`idIssueExt` has no `ExtCrashInterp`. Change: the local state holds an epoch the crash relation increments,
the record maps an id to `(machine, epoch, Loc)` (the global part, shared by machines; or local, if the
member's prefix bits make ids disjoint across machines -- they do: `WellFormed`'s 16 low bits), `Issue`
excludes reissuing an id under another key. Its semantics example (`examples/.../semantics`) and the
nonissue's update; an axiom review (`axiom` skill) of `idutil.Next`'s trusted model over it. Ghost side:
`idIssueCtx` per epoch; the crash interpretation drops the old epoch's ghost generator records but keeps
the issued ids (so a restarted generator cannot reissue them). The D7 split puts `idPfxInv` on the
member's machine: it must be re-established at each generation from the global `idKeyGenFacts` (the
ghost-level `idIncarnation_alloc`, `idutil/Defs.lean:1011`, exists for the graceful restart).

**D4a/D4b prototypes (2026-11-24, branch `etcd-safe-d4b/2026-11-24`; awaiting the owner's sign-off).**
D4a: `fsSemWithS`'s `initLocal st _ := FsInit st` (`Premises.lean`), `fs_init_compatS` (`FilteredSem.lean`),
`etcdNetExts_initR` (no `FsInit` premise). No proof proves `extsInitLocal`, so nothing breaks; the `FsInit`
in `ServerStart`/`ClientStart`, putget's `MemberFiles` and bboltfs's `bootCrashRobust.spec` becomes
redundant (dropping it is a statement change, not done). D4b, as designed above but with tombstones in place
of an epoch counter (equivalent: a key `(e, g)` with `e` below the current epoch can never be issued
again, so only "past or current `g`" matters): `IdIssueState := GMap w64 (Option Loc)`, crash
`M' = idIssueCrash M` (every entry `none`), `"Issue"` refuses `none`; ghost API unchanged (`idIssueFrag id
g` is `id ↪□ some g`) plus `idIssuePast id` (`id ↪□ none`, exclusive with `idIssueFrag`);
`IdIssue/Crash.lean`: `idIssue_crash_interp` (new ghost map with the old entries as `none`; rest
`idIssueCrashStart hL hL'`: the old map's authority and the new map's past elements;
`idIssueCrashStart_past`/`idIssueFrag_crash_past` turn an old incarnation's fact into the new one's
`idIssuePast`). Semantics examples `examples/idissue/semantics/`; review
`notes/axiom-review/idissue-crash.md`. For D4c/D6: `idPfxBody`'s `Ip : GMap w64 Loc` must carry the
previous generations' ids as `idIssuePast` (e.g. `Ip : GMap w64 (Option Loc)` with `idIssueElemAt`) when
`idPfxInv` is re-established after a crash.

**D4c. The bridge for `etcdNetExts` with crashing machines** (untrusted). Generalize
`robust_of_netFsBoot{,_addrs}` (`Net/Statement/NetFsBridge.lean`, hard-wired to `kvnetExts`) to a bundle
`[idIssue, fs at a restricted semantics, net]` with D4b's crash interpretation: `crashPre`, `CrashBootWp`
gain the issue record's crash rest. `etcdFsSem`'s crash relation is the file extension's
(`fsSemWithS SQ Q`'s `crash` is `OsCrash st st' ∧ Q st st'`, and `etcdFsSem` has `Q := True`: checked). Template: kvnet's `kvPc`/`kvPc_crashBoot`/`kvPc_first`.

**D6. The member's restart from a crash state.** Spec phase first:
1. *The per-generation predicate* `memberGen i` (kvnet's `kvPc`): the persistent cluster facts
   (`clusterFacts`, D7's global part) ∗ the member's durable ghost state at the generation's root
   (`osShared` view of its data dir and WAL area) ∗ empty package state.
2. *`NewServer` from a crash state*: one spec for both starts (`haveWAL` chosen by the files), over
   `bootstrap`'s spec (#34 stage 5: `bootstrapRestartContract_holds`; interim axiom if #34 is not there)
   and the WAL's `ReadAll` over fsExt (proved), with `walReadFacts` for crash states (C6, `walFoRes`, the
   WAL tester's `BootFo`). The backend after a power loss: `storage.OpenBackend` is an axiom today;
   its crash-state form is a new interim axiom (reviewed), retired by bbolt over fsExt (`osfs/bboltfs` is
   the start).
3. *The raft log's durability across the member's crash*: raft's invariants hold with the member's state
   being its durable one (what the WAL keeps). Checked by reading the pin: raft v3.7's leader self-acks
   only after persistence (`raft.go:851-857`) and etcd calls `Advance` after `storage.Save` (syncs), so a
   single member never commits an unsynced entry. The kvnet proof's `kvGen_crash` is the model.
4. *The restart invariant* (D7's remainder): the member's local invariants rebuilt from its files and
   the global invariants (`InvRestart`'s graceful version is the start).

**Can start now** (disjoint files): D4a (packet), D4b (design note + semantics example; Lean after
sign-off), D4c (the bridge generalized over an abstract third extension: untrusted), D6.1-D6.2 specs (new
files under `Spec/.../etcdserver/`, `Proof/.../dist/crash/`), D2 step 5 and D2 translation (shared scripts:
announce on #28).

## 13. What the multi-machine theorems make unnecessary (none removed; the owner decides)

`examples/lib/cluster3` and its TCP relay `third_party/bridge` exist to inject partitions inside one
process; over the net extension the network's faults replace them.

| Single-process theorem / cluster3 example | Replaced by |
|---|---|
| `etcd_safe_single_process` (`examples/etcd/all`, 11 drivers) | `etcd_safe` (each driver a workload, §6) |
| `etcd_leaseexpiryN_safe_single_process` | `etcd_safe`'s `leaseExpiry` workload (Q2) |
| `k8s_safe_single_process` (`examples/k8s/all`) | k8s-dist's `k8s_safe` (`notes/k8s-dist.md`, Go done; no Lean yet, not ours) |
| `examples/etcd/txnlinfaultsN` (cluster3 partitioner) | `etcd_safe`'s `kv` (M1/M3) |
| `examples/etcd/partition` (`Check`, `MainWatch`) | `kv`, `watch` |
| `examples/etcd/leasecatchup` | `leaseCatchup` |
| `examples/k8s/etcd3`, `examples/k8s/compactor` | k8s-dist's store and compactor workloads |

Retire with them: `examples/lib/cluster3` (`Partitioner`, `StartBridge`, its proofs);
`third_party/bridge` and its five axioms (`bridgeAt`, `New.wp_proof`, `Blackhole`, `Unblackhole`,
`DropConnections`); the single-process-only premises `Hlow`, `addrsUnclaimed`, `dataDirsAbsent`, `HWal`
over many data directories, the schedules; the collections `etcd-all-single-process`,
`leaseexpiryN-single-process`, `k8s-all-single-process`.

**`examples/k8s/dist/{compactorcopy,storecopy}` import cluster3 and the bridge** only because they are
byte-for-byte copies of the single-process drivers' packages (`TestVerbatim`), made to reach the drivers'
unexported model and checks; the distributed workloads call only the copies' `export.go` wrappers, never
`MainPartition`/`startCluster`. So the dist closure carries cluster3 and the bridge as dead code (their
initializers; no bridge axiom is reached unless called). They should not: split each driver's model and
checks into a package of their own that both the in-process driver and k8s-dist import, and drop the
copies. (A k8s-dist change, its owner's; recorded here.)

## 14. The bounds audit: `Robust`'s separate thread bound (2026-11-24, branch `etcd-safe-lit/2026-11-24`)

The review's rule: a top-level statement takes `Robust`'s separate thread bound (`4e3c90e848`) as a named
constant and the highest step bound the proofs allow, over Perennial's `goose_dist_adequacy_below`
(`DistCrashNstepsBelow [] T n`: the thread bound is on the execution at hand, independent of `N`). Until
now the etcd dist statements said `threads := 2 ^ 28, bound := 2 ^ 28 - 1` and went through
`Net.robust_of_distBootIL`, whose boot form `DistBootWpSL lo bound` fixes `threadBound GF = receiptBound GF
+ 1` and `lo ≤ receiptBound GF ≤ bound`: the receipt bound doubled as the thread bound, so the thread cap
`2 ^ 28` capped the steps too.

**Every use in the etcd dist stack** (the skeleton, `BootBad`, `EtcdBootNC`'s eventual discharge through
the member's boot, and the putget dist pieces it is modelled on):

| Where | Fact | Kind | After |
|---|---|---|---|
| `TopLevelRobustness` (`EtcdBootNC`, `EtcdBootNCBad`, `etcd_safe_nocrash_of_boot`) | `srvLevelK ≤ receiptBound`, `receiptBound ≤ 2^28 - 1`, `DistBootWpSL srvLevelK (2^28-1)` | the floor `srvLevelK` was only there to give `srvLevels` (`srvLevelK ≤ threadBound`) through `threadBound = receiptBound + 1`: a **thread** fact; the cap `2^28 - 1` was the thread cap below | thread bound fixed at `etcdThreads`; receipts `≤ 2^48` |
| `BootBad` (`serverBootBad`, `clientBootBad`, `nodeBootBad`) | `DistBootWpSL srvLevelK (2^28-1)` | uses neither bound (the programs return after the check) | the new boot form, unchanged proofs |
| `etcdstart.StartServer.spec`, `S2Draft.Serve_s2`, `putget.Member.spec` (`ThreadBoundLe 2^28`) | `threadBound GF ≤ 2^28` | **thread** (reader-slot pools `threadBound ≤ rdPoolN`, RWMutex readers `≤ 2^30 - 1`, `raftPool`, the revocation pools: `threadBound ≤ n + 1` with `n` slots fixed) | `etcdThreads = 2^28` meets it |
| `RevokeCtx.srvLevels` (`Serve_s2`, `Member`) | `srvLevelK ≤ threadBound GF` (5 levels of a thread token) | **thread** | `5 ≤ etcdThreads` |
| `StartServer.spec`, `EtcdServer.Start/apply/applyAll/applyEntries`, `mvcc` (`isStore`, `NewStore`, `evLog`), `auth.Fuel`, `lease.Revoke` | `receiptBound GF ≤ 2^48` | **lifetime counter** (receipt cap): `idutil.Generator.Next` issues ids `prefix | lowbit(suffix, 48)`, distinct only for fewer than `2^48` calls (`idutil/Defs.lean`); the store's changes `logCh < 2^48` (revisions, compaction counts); the auth revision's fuel; the no-snapshot catch-up `NoSnapCatchUp = 2^48` (`notes/auth-lease-s4-freeze.md`) | **the binding cap**: `N ≤ 2^48` |
| `StartServer.spec`, `bootstrapContract` | `receiptBound ≤ N + 1`, `N + 7 + bootWB ≤ backend.wbInit = 2^62 - 1` | **lifetime counter** (the backend's write-back tokens) | `N = receiptBound - 1 ≤ 2^48 - 1` meets it |
| `lease` (`|M| < receiptBound ≤ 2^62`), raft/`etcdserver` `≤ 2^61`/`2^62`/`2^64 - 2` | receipt caps | lifetime counters | above `2^48`, not binding |
| `putget` dist (`AdequacyMember`, its `TopLevelRobustness`) | `DistBootWpSL srvLevelK (2^28-1)`, `ReceiptBoundLe 2^28`, `Hprem : n + 12 ≤ 2^40` | as above (thread / receipt); `2^40` is the old `wbInit`, a hypothesis of that skeleton | not ported here (its own statement, `putget_safe`): the same port applies |

No receipt floor exists anywhere in reach (every `… < receiptBound` is a derived fact, not a premise), so
the new bridge needs none; it keeps the floor `lo` for generality and the etcd skeleton uses `lo = 0`.

**The largest step bound the proofs allow is `2^48`** (an execution of `n < 2^48` steps runs at `N = n + 1
≤ 2^48` receipts), not `2^63 - 1`: the cap is `receiptBound GF ≤ 2^48`, a property of the Go code
(`idutil`'s 48-bit suffix wraps after `2^48` ids from one generator) and of the mvcc store's and server's
specs built on it. It needs no premise or axiom: it only caps the step bound. Raising it means re-proving
the server's specs over a larger cap, and `idutil` cannot go past `2^48` ids per generator (a process
restart under D4b's incarnation-keyed issue record would be the way, per generator), so `2^48` stands.

**The thread constant**: `etcdThreads := 2 ^ 28` (`TopLevelDefs.lean`): at least `srvLevelK = 5`, at most
the `2^28` every server and client spec caps `threadBound` by. The client machines fork few goroutines
(one per workload helper, `await.go`; one watcher per watch machine), far below it.

## 15. The robustness review's items against the draft (2026-11-24, branch `etcd-safe-lit/2026-11-24`)

The review (`etcd_robust`/`etcd_safe`, section 2 of the group "etcd" review, and its cross-cutting list) was
written against `lean` `1bdd4e02f1`; this table checks each item at `5f464b7bf9`. `S` = the Spec file
`Spec/.../examples/etcd/dist/TopLevelRobustness.lean`, `D` = `Proof/.../examples/etcd/dist/TopLevelDefs.lean`,
`P` = the skeleton `Proof/.../examples/etcd/dist/TopLevelRobustness.lean`, Go paths under `examples/etcd/dist/`.

| Item | State at `5f464b7bf9` | Evidence |
|---|---|---|
| (a) `TrustBoundary` → per-function axioms | **open, not ours**: `TrustBoundary` is gone from the statement, but the shared bundle is not yet axioms: `[DialWithBalancerBody]` is still an instance binder, and `Hctx` (context's errors) is a named hypothesis of the skeleton | S:55-58 (no `TrustBoundary`), S:121, S:150 (`DialWithBalancerBody`); `BootBad.lean:217-241` (`Hctx`). No branch on `origin` has the per-function axioms of `bootstrap`, `dialWithBalancer` or `context`'s errors yet (searched 2026-11-24): the putget lead's packet lists them "for the separate per-function-axiom effort" |
| (b) `memberId`/`WellFormed` into Go, the whole deployment on every machine | **addressed** | S:31-35, S:123 (`d : Deployment` is the Go value, no `Hd`); D:109 (`memberId` a definition, `membership.memberIdOf`, no longer opaque); D:147-197 (every program gets `deploymentLit d` and its index); Go `deployment/deployment.go:326` (`WellFormed`), `server/server.go:97-102`, `client/client.go:172-201` (each returns on failure); `dist_test.go:53` (`TestWellFormed`: 500 random deployments pass, 13 malformed ones fail); `BootBad.lean` (every machine safe on a malformed deployment) |
| (c) `Hbf`/`BootFacts` quantifying bootstrap's outputs | **open**: (b) removes only `memberId`'s opacity; `BootCore ps ctxs boot` is bootstrap's results, retired by `bootstrap`'s spec (#34, branches `bootstrap-link/2026-11-25`, `bootstrap-stage2/2026-11-25`) | S:125, S:152; D:125-127 |
| (d) `EtcdEnv` folded into the consuming axioms or Go checks; `leasePeersOk` proved | **open, needs trusted changes**: each field is an opaque `Prop` that a trust-boundary axiom takes; folding one in restates that axiom (`storage.NewBackendQuota`, `auth.NewAuthStore`, `EtcdServer.leaseTimeToLive`, grpc's server start, bbolt's open); `leasePeersOk` is opaque (`LeaseRead.lean:152`), and proving what it says needs the peer handler (`etcdhttp.NewPeerHandler`, names-only, phase 7 S5) | S:126, S:153; D:253-264 |
| (e) `HEnv` → a Go `ETCD_VERIFY` check at program start | **open, needs a trusted change**: a check in Go reads the variable once, but `os.Getenv.spec` (`Spec/os/Getenv.lean`) gives `etcdVerifyOffValue` only under the token `envVerifyOff`, and says nothing linking two reads, so the check cannot produce the token the backend's checks need. Removing `HEnv`/`HEnvTok` needs `os.Getenv`'s axiom restated over the process's fixed environment (each key one value per run), which retires `verifyEnvOff` and `envVerifyOffTok`, or the distributed start giving the token (premises-to-axioms item G, an adequacy change) | S:133-134, S:158-159; `Proof/.../verify/Env.lean:46,57` |
| (f) the bounds named; `2^48` the receipt cap, with its reasons in the header | **partly**: `etcdThreads` is named (D:275); the step bound is the bare literal `2 ^ 48` (S:139, S:163) and the header names only `idutil` (S:24-28) | |
| (g) `etcdNetExts` instead of `[GooseExts] … [HasExt …]` | **addressed** | S:105-106 |
| (h) the client machines (`NodeMain`, `Args.Nodes`) | **addressed** (stage D8) | D:195-209 (`nodeProg`, `nodeMachines`), S:131, S:138; Go `client/client.go:193` (`NodeDeployment`), `cmd/node` |
| (i) the driver's liveness retries | **open** | Go `client/client.go:79-105` (`AwaitCluster`, 60 × 500 ms), `client/await.go:9-34` (`AwaitAccept`, 300 × 100 ms), `client/nodes.go:200-210` (`ConnectRetry`), `client/durable.go:13-18, 50` (`durableTries`) |
| (j) redundant `NetStart` and `.init` premises | **addressed** | no `NetStart`; `ServerStart`/`ClientStart` are the file system's only (D:228-235); P:109-111 takes the net's start from `Robust`'s `extsInitLocal`/`extsInitGlobal` |
| (k) the header's history | **partly**: S:9-10 ("2026-11-22, the naming on #24"), S:48 ("approved 2026-11-23"), S:55 ("2026-11-24"), S:113-114; D:107-108, D:250-251 | |

### 15.1 What was done (2026-11-24, same branch)

- **(f)** The step bound is named: `etcdSteps := 2 ^ 48` (`TopLevelDefs.lean`, beside `etcdThreads`), its
  docstring and the Spec header naming its three reasons (`idutil`'s 48-bit suffix, the mvcc store's change
  count, the auth store's fuel). The statements say `(bound := etcdSteps)`; the skeleton, `EtcdBootNC`,
  `EtcdBootNCBad` and `BootBad`'s three boot proofs say `etcdSteps` too.
- **(k)** The Spec header and `TopLevelDefs.lean` carry no history (dates, review numbers, "was opaque", the
  prometheus note, the comparison with the single-process theorem); `TopLevelDefs`' stale header ("one
  decidable premise", "the boot programs are placeholders") rewritten.
- **(i)** The programs retry nothing for liveness: `client.MainReady` no longer calls `AwaitCluster`; kv,
  watch, cache and auth no longer call `AwaitAccept`; a client machine (`NodeMain`, `kvremote.Node`) makes its
  client once and returns if that fails (`ConnectRetry`, `kvremote.connect` gone from them); `durable` does one
  final Range (`durableTries` gone). kv has no set-up any more (`hasSetUp`). `AwaitAccept`, `AwaitCluster` and
  `ConnectRetry` stay exported for `examples/k8s/dist`, which has its own review item. The wait moved to the
  harness: `robust.Run.RunClientsAwait` (`RunClients` with a hook between the client machines' start and the
  orchestrators'), and `examples/etcd/dist`'s `Cluster.await` (from each orchestrator machine, every member's
  client address, served only once the member is ready, and the workload's client machines' addresses accept a
  connection). `TestDist -short` in the local mode, one round per kind (kv, leaseExpiry, compact, durable,
  leaseRead, watch, cache, auth): every workload `checked`. Translation regenerated (`client`, `kvremote`).
- **(b)** `TestWellFormed` also rejects a repeated or invalid member name, an empty token, a snapshot count of 0,
  a periodic compactor below its minimum and an unknown mode, kv beside a workload writing keys, and auth without
  the token provider (and accepts auth with it).

### 15.2 What is left, and on what it waits

- **(a)**, and the shared bundle's context and dial parts (`Hctx`/`Hcec`, `[DialWithBalancerBody]`): no
  per-function axioms exist yet on any branch. What plugs in: `[DialWithBalancerBody]` (an instance binder of
  both statements and of `EtcdBootNC`/`EtcdBootNCBad`) is replaced by a per-function axiom
  `Proof/go_etcd_io/etcd/client/v3/Client__dialWithBalancer.lean` (or the translated body), and the binder
  dropped from the statements; `Hctx` (the hypothesis of `etcdBootNCBad_holds`, `etcd_safe_nocrash_of_bootWF`,
  `BootBad.lean`) is discharged by the proved facts on `context`'s initializer (premises-to-axioms item F:
  PROVE, never an axiom, `isPkgInit context` being unsealed), `serverBootBad`/`clientBootBad`/`nodeBootBad`
  then taking no hypothesis; `bootstrapContract`, `bootMarshal`, `rnLoggerZapOk`, `rnTimeoutDetectorOk` are
  not in this statement (they enter `EtcdBootNC`'s discharge through the member's boot, from the same
  per-function axioms putget uses).
- **(c)** `BootFacts`: waits on `bootstrap`'s spec (#34); (b) leaves only `perm : ps.Perm d.ids` depending on
  the deployment.
- **(d)** `EtcdEnv`: each field folded into its consuming axiom is a restatement of a trust-boundary axiom (a
  trusted change, not done here); `leasePeersOk` is opaque, and what it says needs the peer handler's model
  (phase 7 S5).
- **(e)** `HEnv`/`HEnvTok`: a Go check alone cannot produce the token (see the table). The trust-shrinking
  route: restate `os.Getenv`'s axiom over the process's fixed environment (one value per key per run, a
  persistent agreement), so that a check at the program's start gives every later read's value; with it the
  axioms `verifyEnvOff` and `envVerifyOffTok` go, and so do `HEnv` and `HEnvTok`. A trusted change for the
  owner (an axiom restated), not done here.

## 16. Integration line (2026-11-25, branch `etcd-safe-main/2026-11-24`; issue #50, pieces P1 and N0)

The line that collects the settled `etcd_safe` branches and builds them together (full VM build green,
`etc/tcb-report.py --check` and every collection matching). Merged heads, in order, onto
`etcd-safe-lit/2026-11-24` (`c022542b8b`, which carries `-d2` and `-wf`):

| # | branch | head |
|---|---|---|
| 1 | `etcd-safe-crashskel/2026-11-24` (crash skeleton `etcd_safe_of_boot`, D4a-D4c, W1 in `etcdFsSem`) | `87c770d1cc` |
| 2 | `raft-restart-confpoint/2026-11-24` (option D) | `66ce406ae2` |
| 3 | `lean` | `e785a7776e` |
| 4 | `dist-putget-interim/2026-11-24` (A1 `etcdSvc`, A3 `Serve_dist`, A2, `envPub`; with `hprem-axioms`) | `cc2bfed144` |
| 5 | `dist-putgetk/2026-11-24` (ClusterStart, `StartMember_dist`, `holdForever`) | `650a7c4887` |
| 6 | `hprem-axioms/2026-11-24` (already in 4) | `14bd8f185c` |
| 7 | `lean` (with `4bb5562851`, `http.register` consumes `netAddrLeft`) | `2f8ee1548e` |

What the merges needed (all on this line only; the source branches untouched):
- **etcd pin**: `lean`'s `df6af0c36` (fmt stage 1) and D6 T4's `8aa40fd5c` (the snapshot guard), both on
  `6b942d23f`, combined as `47d6cdeeb` (fork branch `goose-lean-fmt1c-snapguard`: the guard cherry-picked,
  clean; its test passes). The translation is unchanged by the combination.
- **`etcd_robust.spec`'s bounds** stay `2 ^ 28` threads and `2 ^ 28 - 1` steps:
  `robust_of_dist_crash_adequacy_etcdNet` gives a generation `receiptBound + 1` threads. They move to
  `etcdThreads`/`etcdSteps` once the crash bridge separates threads from receipts (#50, P11).
- **membership**: `lean`'s claim #34 specs of `NewMember`/`computeMemberID`/`newMember` (general, over
  `etcdserver.Assumptions`) keep the plain names; D2's one-URL specs, over `membership.Assumptions` (which
  the dist client has), are the variants `.specOne` (`<fn>One.lean`), with the URL plain and shorter than
  `2 ^ 61` bytes (`strings.Join`'s new bound); `deployment.memberIDs`/`IdsOk` take the peers valid and
  within `typed.maxLen`, which `WellFormed` has. To go once membership's defs are over
  `membership.Assumptions`.
- **`NewRaftLoggerZap`**: `lean`'s stage-4 spec (`zapLoggerOk` to `isLogger`, a hypothesis of
  `raftConfig`) keeps the plain name; `hprem-axioms`' axiom keeps its reviewed statement as
  `NewRaftLoggerZap.specNN`/`wp_proofNN` (a rename in the baselines), which `newRaftNode` takes.
- **The bridges**: both thread-bound bridges kept side by side (`robust_of_distBootILT` here,
  `robust_of_distBootIT` putget's); one should go.
- **D6 T4's `specRAt`/`specC`** follow `specR`: `lean`'s `etcdURLsFit` premises, without
  `rnNewStorageOk` (wal-nostorageok) and the two raft-wrapper contracts (hprem-axioms).
- **putgetK_safe's unlanded statement, adapted here only** (the coordinator's decision, 2026-11-25):
  `hprem-axioms`' swap as for `putgetN` (`BootLogFacts.wire` in place of the premise `bootMarshal`,
  `commonPremises` gone from `premises` and `StartMember_dist.spec`); the client's share carries
  `Net.addrOk ep` in place of `plainEndpoint ep` (putget's new `Client.spec`). `putgetk.Start` is listed
  in `etc/tier-linking.txt`.
- **The trust-base report**: `etc/proof_roots.py` runs a root that reaches the part `Net` only outside its
  `net/http`/`net/textproto`/`net/rpc` apart from those that do (the dist roots import the main tree's
  `net/http`, which one environment cannot hold with the part's).
- The trust base against `etcd-safe-lit`'s: `+` the four interim axioms of putget (dist-putget-interim),
  `proto.MarshalBootConfChange.wp_proof`, `contention.NewTimeoutDetector.wp_proof`,
  `NewRaftLoggerZap.wp_proofNN` (hprem-axioms), `proto.UnmarshalWalRecordE.wp_proof` (`lean`); `-`
  `errors.AsNoMatch`, `fmt.ErrorfSlice`, `fmt.SprintfSlice`, `fmt.SprintfWalName`, `slices.ContainsFunc`
  (`lean`). 337 axioms, no `sorry` reached (`NewServer.wp_proofC`'s is unlinked).

### 16.1 Round 2 (2026-11-25): the crash and transport branches; the pin bump held back

Merged onto `c370ac2d30`: `etcd-safe-crash/2026-11-24` @ `05926dc6af` (P11, the crash bridge on `Robust`'s thread
bound, so `etcd_robust.spec` is at `etcdThreads`/`etcdSteps`; P10 `EtcdBootCBad`; C-I1; the fs extension's
`szCrash`/`ftruncate`; `dbOpts`; D6 notes) and `etcd-safe-transport/2026-11-24` @ `f152a3be06` (S5's interim axioms
and the proxy check; route B: the members read with `IsLearner`, `PromoteMember`, the wide `ccApplyOk`,
`clusterImageOk_restModel` split). What the merges needed:
- **`http.reserve`**: the transport branch's narrowing (`netAddrPend`, `89cfadf10c`) and `lean`'s fix of the same
  hole (`httpAddrNet`, `501e3fa84d`, on this line since round 1) both spend the address's pending set and do not
  compose; `lean`'s kept, the branch's `netAddrRsv`/`netAddrPend` split and its re-proofs dropped
  (`notes/axiom-review/http-reserve-pend.md`, superseded).
- **`etcd_robust.spec`**: the first merge kept round 1's `2 ^ 28` bounds silently (only this line had changed those
  lines); restored to the crash branch's `etcdThreads`/`etcdSteps`.
- `NewServer_dist`'s pre lost `rnLoggerZapOk`/`rnTimeoutDetectorOk`/`rnNewStorageOk` (gone from `specG`, which the
  axiom mirrors: hprem-axioms, wal-nostorageok); `bootstrapAtR_of_crash` gives C-I2's new `bootLen ≤ σ.commit` from
  the restart contract's `i ≤ σ.commit`; the transport branch's §16 is §17 here.
- SpecPlan's PkgInit: `lib/remote` is the part `Net`'s translation (`etc/gen-specs-pkginit.py`'s `NET_PART`), so the
  dist modules generate and build; `nonissues/bbolt-init-not-crash-safe.md` moved to `issues/`.

**The pin bump to `e94f33b50` (`goose-lean-fmt1c-crashfixes`) is on `etcd-safe-main-pin/2026-11-24`, not here**: it
leaves proofs broken that need new specs, not merge work. With P6 (`etcd-safe-walfix-p6` @ `2c17304ea8`, applied
there as its diff against `lean`: P6 also carries 309 `lean` commits, among them `EtcdVerifyOff` in place of the
`envVerifyOff` token this line uses some 120 times, a separate integration) the WAL builds; what still fails there:
`storage.OpenSnapshotBackend` (the new `syncDir` after the rename: no spec of a directory sync in the backend's
file model), and, without a failure today because `bootstrap`'s restart branch is a law, the new unsaved-WAL branch
of `bootstrap` (`wal.Unsaved`, `removeBackendDurably`, `wal.DiscardUnsaved`: the latter deferred to P6b) and
`finishDefrag`'s `syncParentDir`. Retranslation at the pin: `etcdserver` (bootstrap), `storage` (`syncDir`),
`storage/backend` (`syncParentDir`), `storage/wal` (the torn-Save fix, `Unsaved`, `DiscardUnsaved`,
`encodeState`); the bbolt `replace` in etcd's `go.mod` changes no translation (bbolt is project `bbolt`'s, from its
own fork pin; the etcd project names it only).

**Checkpoint (2026-11-25, end of round 2's session).** `etcd-safe-main/2026-11-24` @ `42de3cddaf`: full VM build
green, `etc/tcb-report.py --check` matches (337 axioms, 0 `sorry`; the baseline file is round 1's, unchanged: no
axiom C-I1 or S5 added is reached by a linked result yet). `etcd-safe-main-pin/2026-11-24` (the pin and P6, built
on the VM): every module but `storage.OpenSnapshotBackend` and what imports it. **Next, on the pin branch**
(the coordinator's request): specify `storage.syncDir` (`server/storage/backend.go`, the same body as
`fileutil.syncDir`: copy `Spec/.../fileutil/syncDir.lean` and its proof, with `isPkgInit` of `storage`), and call
it in `OpenSnapshotBackend`'s proof after the rename, with the parent directory's `osPathS`/`osCallPerm` taken out
of `fileAt dst`'s `nameAtF` (`path = child d b`; `filepath.Dir (child d b) = d` is needed) inside `onFs`, and put
back. The durable-name fact C-I1's `dbCrash` leaves to the caller (`Fs.Named`, from a directory sync after the
rename) needs the rename's log position: `os.Rename.spec` (proved, `Proof/os/Rename.lean`) would have to return
`osLogLb n` past its entry, and the post of `OpenSnapshotBackend` `osCommitLb n`; T7 decides the form.

**Step 1, 2026-11-25 (pin branch): done so far, and the blocker.**
- `storage.syncDir` translated: added to `storage.toml`'s `translate` list, with `path/filepath` and `fileutil` in
  its `imports` (until then names-only: `OpenSnapshotBackend` called an unspecified function). The package
  initializers and PkgTables were regenerated (`etc/gen-init.py`).
- `Spec/.../storage/syncDir.lean` is `fileutil.syncDir`'s spec with the file extension's instances (and
  `os.file.FieldAssumptions`) bound inside the spec, as `bbolt.Open.spec` does, so that `OpenSnapshotBackend`
  (which uses the `onFs` vocabulary) can call it at `theFs`'s instances. `Proof/.../storage/syncDir.lean` is
  `fileutil.syncDir`'s proof, over `OpenDir.spec`/`Fsync.specDirS` taken at any instances. To link it in the server:
  `storage_syncDir: =<fileutil.OpenDir.wp_proof> =<fileutil.Fsync.wp_proofDirS~os.File.Sync.wp_proofDirS>`,
  with the fileutil and os proof modules added to `--server`'s `EXTRA_IMPORTS`.
- `config.dirModel_backendPathOf` (`OpenSnapshotBackendLemmas.lean`, built) holds for any data directory:
  `filepath.Dir(cfg.BackendPath())` is the snapshot directory. It rests on `path.cleanModel_snoc_slash`
  (`Clean(p + "/") = Clean(p)`). In the proof, the directory `d` of `fileAt dst`'s `nameAtF` is the snapshot
  directory (`parentOf`), so the sync takes that claim's `osPathS R d`/`osCallPerm`.
- **Blocker: the sync can fail, and `applySnapshot` panics when it does.** `applySnapshot` calls
  `lg.Panic` on any error from `OpenSnapshotBackend`. Its proof refutes the error case only through
  `snapOpensOk`'s `dirReadOk`/`renameOk`, and no spec makes `syncDir` error-free. `Fsync.specDirS`'s error needs
  `¬ FsNoErrIno`, which `theFs`'s `FsNoErrAll` refutes, and `os.File.Close.wp_dirSNE` exists. But the directory's
  open has no no-error spec: `wp_osOpenDirS` (Fs) allows any errno except `ENOENT`, and so do
  `os.OpenFile.wp_dirSOk`, `os.Open.wp_dirSOk` and `fileutil.OpenDir.spec`. No new axiom or premise was added
  (reusing `renameOk` to cover the sync would change a trusted premise's meaning). The route with no new trust is
  a no-error chain:
  (a) `Fs.openDir_succ`, a success from every free fd (`OpenEffect`'s `.dir` case; compare `openFile_succ`),
  and a `Q` variant of `wp_osOpenDirGenS'` (as `wp_osOpenFileSQ`), giving `wp_osOpenDirSNE`, whose errno on
  failure is `EINTR` (`open_failure_eintr`);
  (b) `os.OpenFile.wp_dirSNE`, which retries `EINTR`, so it returns no error;
  (c) `os.Open.wp_dirSNE`;
  (d) `fileutil.OpenDir.specNE`;
  (e) `storage.syncDir.spec` restated with no error (`⌜err = nil⌝ ∗ osCommitLb n`), under `[FsNoErrAll]` as
  well (taken from `theFs`).
  `OpenSnapshotBackend`'s error disjunct then stays as it is.
- **The post for T7**, once the chain exists: in the success disjunct, `onFs (∃ x e, osLogEnt x e ∗ ⌜e` is the rename
  of the snapshot's file onto `db`⌝ ∗ `osCommitLb (x + 1))`. That needs `os.Rename.spec`'s post to keep the
  `osLogged x e` that `wp_osRenameFileSNE` gives (it is dropped as `-` in `rename_fileNE` today). Its `osLogLb (x+1)`
  then feeds `syncDir`. The fact is persistent, so it survives `OpenBackend` (an axiom whose `bPath` hides the
  claim's history). T7 combines it with the claim it holds (`bPath`) to show that the durable tree names the inode.
- P8 is integrated on `etcd-safe-main-pin-p8/2026-11-24`, not here: `NewServerRAt` needs restating over
  `srvFilesC` first (see that branch's §16.1).

**Step 2, 2026-11-25 (pin branch): the blocker closed with no new trust.** The no-error chain, each
link from `etcdFsSem`'s step premise `etcdSQ` (`NoIoErr allIo` ∧ `NoMapLockErr allIo`, packed as
`theFs`'s `FsNoErrAll` by `etcdFsNoErr`) and nothing else:
- `Fs.openDir_succ` (`GooseLang/Ext/Fs/NoErrSpecsOpenDir.lean`): a read-only `open` of a directory has a
  success from every free fd (`OpenEffect`'s directory case); `wp_osOpenDirGenSQ`
  (`TreeSharedOpenDir.lean`, `wp_osOpenDirGenS'` now its instance) gives a failure's errno from the
  step; `wp_osOpenDirSNE`: with `open_failure_eintr`, a failure is `EINTR` (`NoIoErr`'s "a success
  exists → errno 0" with a free fd, `NoMapLockErr`'s `EINTR` clause with none).
- `os.OpenFile.wp_dirSNE`, `os.Open.wp_dirSNE` (`Proof/os/NsSNE.lean`): `OpenFile` retries `EINTR`, so
  no error, under `FsNoErrOn (· = p)` and `PathFits p`.
- `fileutil.OpenDir.specNE`/`wp_proofNE`.
- `storage.syncDir.spec` restated with no error (`RET nil`, `osCommitLb n`) under `FsNoErrOn (· = dir)`
  and `PathFits dir`: `Fsync.specDirS`'s error needs `¬ FsNoErrIno`, the close is
  `os.File.Close.wp_dirSNE` (`NoIoErr`'s `DirClose`).
- `os.Rename.spec`'s post keeps the rename's log entry (`backend.renamed src dst`: `renameEntF`, the
  entry `x` a `.rename` of a file from `d/bs` onto `d/bt`, and `osLogLb (x + 1)`).
- `OpenSnapshotBackend` (`theFs` split; the directory is the snapshot directory, `snap.backendPath_dir`;
  it fits, `Fs.pathFits_of_child`): the success disjunct adds `backend.renamedDur src (backendPathOf dd)`
  (the entry with `osCommitLb (x + 1)`), the error disjunct is unchanged. Not persistent as stated
  (the instance did not synthesize through `onFs`'s eight binders; add one for T7 if it needs it).
  `SnapApplyWalk` drops it for now (`-`): T7 is its consumer.
Bounds: the 17 new matches (NewServer's pattern restated in `NewServerCrash`, `NewServerDist`,
`PeerServeDist`, `StartMemberDist`, and one stock match in `Proof/.../NewServerRAt.lean`, the crash
branch's restart proof) are owner allows in `etc/bounds-allow.txt`; `--check` at 400.
Checked: the dependents (`applySnapshot`, the server `Link`, dist `TopLevelRobustness`, `BootBad`), then a
full VM build of the branch (29155 jobs, green); `etc/tcb-report.py --check` (through `vmlake env`) matches
the baseline (337 axioms, 0 `sorry`): no axiom added or removed.

**P8 integration (2026-11-25), branch `etcd-safe-main-pin-p8/2026-11-24`, not on the pin branch.** P8's diff
against P6's `2c17304ea8` applies, with two add/add conflicts resolved (`CrashInterim.lean`,
`InvCrashImage.lean`; kept this line's `envVerifyOff` and the `issues/` path). Every P8 module builds. Two
errors, both in this line's crash-branch file `NewServerRAt.lean`, which P8 never saw:
- `bootstrapAtR_of_crash` (l. 113): the crash contract's pre is now `srvFilesC`, and `bootstrapAtR`'s is
  `srvFiles`. Fix: weaken through `srvFiles_srvFilesC` inside the triple (`icases Hc with #Hc`, then
  `iintro !>`, and apply `Hc` with the files converted).
- `srvCrashImageAt_disk` (l. 140) cannot be repaired: a crash image now holds only `srvFilesC`, and
  `srvDiskImageAt` (the graceful image) needs `srvFiles` (the WAL's synced mark at `|H|`).
  `NewServerCrash`'s route (crash image, then graceful image, then `NewServer.specR`) needs `srvDiskImageAt`
  and `bootstrapAtR` restated over `srvFilesC`. That is proposal (1)'s consumer change
  (`notes/wal-p8-handoff.md`): nothing on the restart path needs the mark. The other way is to raise the mark
  at boot.

**P8 on the pin (2026-11-25), branch `etcd-safe-p8-pin` off `etcd-safe-main-pin-p8/2026-11-24`.** Both errors are
fixed by the consumer change: `srvFilesC` moves from `SrvCrash` to `InvRestart`, and `srvDiskImageAt`,
`bootstrapRestartContract` and `bootstrapAtR` take it. The graceful stop (`StopShutdown`) weakens its
`walFiles` through `walFiles_walFilesC`; `NewServerR` uses `srvFilesC_dataDir_len`; `bootstrapAtR_of_crash`
and `srvCrashImageAt_disk` hold unchanged. `bootstrapRestartContract` is an unproved premise (of
`etcdstart.bootPremiseR`, reaching the restart examples' linked results, no closed theorem since D2): its pre is
now weaker, so the premise is stronger, still true of Go (no restart step reads the WAL's synced mark). It
builds on fk-lean2 (`NewServerR`, `NewServerRAt`, `NewServerCrash` (its labeled `sorry` unchanged),
`StopShutdown`, `etcdstart.Restart`, `BuiltRestart`, the P8 modules), with no new axiom or `sorry`.

### 16.2 Round 3 (2026-11-25): `lean` merged into the pin line, then P8

Branch `etcd-safe-main-r3/2026-11-25`, from `etcd-safe-main-pin/2026-11-24` @ `3717c7903b`: `origin/lean` @ `676aede0a1`
merged (391 commits), then P8 (`etcd-safe-p8-pin` @ `f94ff9bca1`, branched from this line at `3e45d8157c`; a plain
merge). The etcd pin stays `e94f33b50` (`lean` did not move its own). What the merge needed:
- **`EtcdVerifyOff` adopted everywhere** (the owner's decision on `lean`): `etcd_robust`, `etcd_robust_nocrash`,
  `putget_safe` and `putgetK_safe` take `(HEnv : EtcdVerifyOff)` in place of `HEnv : ∀ m ∈ …, verifyEnvOff m.1` and
  `HEnvTok : ⊢ envVerifyOff`; the crash/dist specs and bundles (`NewServerCrash`, `NewServerDist`, `StartMemberDist`,
  `putgetk.Member`, `NewServerRAt`, `CrashInterim`, `InvCrashImage`, `memberStartRes_areas`) carry `⌜EtcdVerifyOff⌝`.
- **ctx-leaf-fix**: `Hctx`/`Hcec` (classes gone, theorems now) dropped from putget's and putgetK's statements, their
  boots, the dist `InitLinked`s (gen-init) and `BootBad`.
- **kv/kvdurable retired, kvnet → kvraft**: `lean`'s; option D's `kvreconf/ApplyConfLemmas` hunk ported to KvRaft's own
  file; `Net/Statement/DistCrashAdequacyKvnet.lean` over `kvraftExts`/`kvraftInitCompat`.
- **Client specs**: `lean`'s `levelTok 0` combined with this line's `noProxyOptsAt`/`cfg` field; the dist clients
  (`putget.Client`, `putgetk.Client`) take `levelTok 0` at `ThreadBoundLe 2 ^ 30`, split off the main thread's token
  in `client_boot`.
- **tracecheck**: `lean`'s drawn voter count with hprem-axioms' axiom: `premises_of_spec n` at `bootLog n`
  (`bootWire_bootLog`), so `raft_tracecheck_robust` takes neither `Hprem` (lean's) nor `boot`/`Hbf`/`Hbw` (this line's).
- **Duplicates**: `lean`'s `ccBootWire` (`CCModel`, over `cc1EncRaw`) replaces this line's `proto/BootWire.lean`;
  `DistBootWpST`/`robust_of_distBootIT`: this line's (no `DistDeploy`), at `lean`'s argument order (`threads bound`);
  `copy-part` leaves `BootMarshal` out of RaftNoAx (its raft marshals with `raftpb.MarshalConfChangeV1`).
- `BootBridge` (claim #34) unfolds `ccAddOk` (route B's boot policy); four premise witnesses (bboltfs, WalTester,
  mvccrand, mvccfull) give the local start's `FsInit` (fs's `initLocal` on this line).
- Generated: gen-init (L1: Net's copy of `lib/remote`'s `Init` is stale, the main tree's is the one source; Dsverify's
  three `Base` imports repointed), copy-part, SpecPlan PkgInit; the walfs `Link` (pin step 2's `OpenDir.specNE`).
- Gates: `iris-premise`/`premise-witness` baselines list `putgetK_safe`/`etcd_robust_nocrash` (older than the gates on
  this line); etcdstart's API lists `NetExtsCrash`.
**Checked:** goose, gen-init, gen-raft-tla, copy-part, gen-specs-pkginit, tier, issues, bounds (390), iris-premise,
premise-witness, api; every `Link` regenerated on the VM matches; full VM build green after P8.
**P7 merged** (`origin/etcd-safe-p7` @ `5573c4c603`, D6-T6: `snapDir_crash.law` proved; its base `lean` @ `2f8ee1548e`
already on this line). Conflicts: dist `TopLevelRobustness` (Spec, Proof) and `deployment/deployment.go` kept this line's
(P7's sides were older versions plus the same `EtcdVerifyOff` merge: this line's thread-bound bridge, the verified
`AddrOk`); `notes/etcd-dist-d6.md` (§T6 after this line's sections) and `notes/axiom-review/README.md` (the `snapdir-crash`
row) kept both. gen-init: up to date with no change (the 15 differences on P7's own branch were D2's `lib/remote`
initializers, which this line's configuration already generates from the main tree's one source). Regenerated:
`InvNodeChan`'s copies (gen-raft-tla, copy-part). `etc/api/backend.txt` lists `FileDur` (P7's `rafthttp/Net` imports it).
**Checked:** goose, gen-init, gen-raft-tla, copy-part, gen-specs-pkginit, tier, issues, bounds (390), iris-premise,
premise-witness, api, import-all; every `Link` regenerated on the VM matches; full VM build green (28661 jobs);
`tcb-report --check` (338 axioms, 0 sorries) and every collection unchanged.

### 16.3 `bootstrap`'s interim axiom at `etcd_safe`'s shape (2026-11-25, branch `etcd-safe-bootax/2026-11-25`)

`bootstrap.spec` (#34) is false at a cluster of several members (the #34 ledger, B4: `isMemberBootstrapped`'s
`GET /members` to the other members, `advertiseMatchesCluster`'s in-place sort of several URLs), so the
members' `bootstrap` contract was an Iris premise (`Hprem`). Now an interim axiom, the trust-boundary
counterpart of #34's restated spec (#34 comment 7152459179, etcd_safe's requirements):
- **`bootstrap.wp_proof_dist : bootstrap.specDist`** (`Spec/.../etcdserver/bootstrapDist.lean`,
  `Proof/.../etcdserver/bootstrapDist.lean`): `bootstrap.spec` word for word plus four shape premises (one peer
  URL per initial-cluster entry, at most 64 entries, this member's peer URLs its entry's, one client URL) and, in
  the precondition, the round-tripper contract `etcd_dist.bootRTOk γ id dir` (`S5Interim.lean`: every other
  peer's address `httpAddrAt γ pid a`, and `noProxyEnv`), exactly `NewServer_dist`'s `#Hpeers ∗ #Hnoproxy`, which
  the S5 interim axioms' callers hold. A failure is a returned error in the post; the post names `bootGo`'s
  values. First start only (`bootCfgFresh`, `wal.bootRes`); the crash side (`bootstrapCrashContract`, which
  etcd-grove-03 restates on `etcd-safe-t10`) is untouched.
- **Retirement is a swap:** `bootstrap.specDist_of_spec` (`dist/BootDist.lean`) derives `specDist` from
  `bootstrap.spec`; when #34 proves its restated spec, the axiom becomes that theorem.
- **Derived:** `etcd_dist.bootstrapContract_of_specDist`, `bootPremiseDist_of_specDist` (`dist/BootDist.lean`,
  defs; over `etcdstart.BootBridge`, now importable). `putgetk`'s member boot derives every member's contract
  from the axiom and the pure `BootGoK` (`putgetk/Defs.lean`).
- **Statements changed** (putgetK's line only; `putget_safe`'s `Hprem` and the shared `etcdstart.bootPremise`
  unchanged): `putgetK_safe.spec` (top level), `PutgetKBoot`, `putgetk.Member.spec` and `StartMember_dist.spec`
  (PLACEHOLDER, its `bootPremise` now `bootPremiseDist`): the premise `Hprem : ∀ n, n + 12 ≤ 2 ^ 40 → ∀ hG, ⊢
  premises … n peers clients ps ctxs boot` becomes the pure `Hbgo : BootGoK peers clients ps ctxs` (Go's
  values at each member's URLs, the shape, at most 64 members). `NewServer_dist.wp_proof` keeps `#Hboot :
  bootstrapContract …` in its precondition (an axiom's precondition, now dischargeable from
  `bootstrapContract_of_specDist`, not a premise of any statement).
- **Review:** fresh `axiom`-skill review, survives with docstring/evidence changes (applied), re-reviewed:
  `notes/axiom-review/bootstrap-dist.md`. A non-etcd `/members` answer `[null]` panics `bootstrap`
  (`nonissues/etcd-bootstrap-members-null-panic.md`); `bootRTOk` excludes both routes to one.
- **Go evidence** (`examples/axiomcx/bootstrapdist`, pin `e94f33b50`): three members boot through `NewServer`
  (the first with its peers unreachable, the others after a `GET /members` answered by its peer handler); a
  hanging peer (timeout, boot succeeds); two returned errors (data directory a file; this member already
  published); the two panics `bootRTOk` excludes (a stand-in at a peer address, a proxy).
- Gates: tier, bounds (390), premise-witness, iris-premise (putgetK's `Hprem` line dropped), api (etcdstart
  lists `BootBridge`). Full VM build green (28664 jobs). `tcb-report --check` matches the baseline unchanged
  (338 axioms, 0 `sorry`): no proof root reaches the axiom, since `putgetK_safe` is proved only as
  `putgetK_safe_of_S5` (`putgetk/Start.lean`, over the named hypotheses `HS5`, `HSM`), which is not a root
  (`etc/proof_roots.py`); the baseline and the collections gain it when `putgetK_safe` (or the member boot of
  `etcd_safe`) becomes a root.

## 17. Interim transport (2026-11-24, branch `etcd-safe-transport/2026-11-24`; §16 there, renumbered at its merge into the integration line, 2026-11-25)

The cross-machine transport `etcd_safe_nocrash` needs, as interim trust-boundary axioms at the external interfaces
(each reviewed by a fresh `axiom`-skill agent; the reviews' verdicts below). Branch base: `etcd-safe-lit`
(`c022542b8b`) merged with `dist-putgetk` (which carries `dist-putget-interim` up to `886b7e46f1`) and three of
`dist-putget-interim`'s later commits cherry-picked (`395a24818f`, `e41f4752d2`, `39b0b45cf8`); its last one,
`6c436a379d` (`putget_safe` at `Robust`'s thread bound), sits on a squash-merge of `lean` and conflicts with lit's
thread-bound bridge: left for the integration branch. The tier check's three refusals are `putgetk/Start.lean`'s
(unbuilt WIP on `dist-putgetk`), not this work's.

### 17.1 N4 (I-3, I-4): the member's peer side

**Vocabulary** (`Proof/.../etcd/dist/S5Interim.lean`, defs, no axiom): `httpPeerSvc` (opaque, a pair of
`Net.Proto`s, as grpc's `grpcCliPI`/`grpcSrvPI`: no proof establishes either of any bytes), `httpAddrAt a :=
addrProto a httpPeerSvc.1 httpPeerSvc.2`, **`http_addr_set` a theorem** (`addr_set_proto`), `s5Interim : S5Draft`
and **`s5Holds : S5Holds GF`** (the D9 skeleton's and `putgetk`'s named hypothesis, discharged); `noProxyEnv`
(the four proxy variables `osEnvIs k ""`); `peerHandlerOf h s` (opaque, per process).

**Axioms** (each in its own Spec/Proof pair under `.../etcd/dist/`, docstring: what, why true, what retires it):
- `NewServer_dist.wp_proof : NewServer.specG_dist on cmp` (I-3): `NewServer.specG` verbatim but for the network:
  no `γn` binder (the post's `∃ γn` with `γn.N = srvNet γ ∧ γn.dir = dir`, as `putgetk`'s `StartMember_dist`),
  `netHttpOk γn id` replaced by `httpAddrAt γ pid a` of every other peer's directory address, and `noProxyEnv` added.
- `NewPeerHandler_dist.wp_proof` and `PeerServe_dist.wp_proof` (I-4): `etcdhttp.NewPeerHandler(lg, s)` on a
  started member returns `peerHandlerOf h s`; `http.Serve(pl, h)` at `pa` (`httpAddrAt pa`, `netListenerOpen pl
  pa`, `srvNetMember`, `isServerReqM`, the `httpProcSlots` of `srvServeRes`) is safe, post `True`. Two axioms because
  `http.Server` is an axiomatized type here (its composite literal has no field model): the program now calls
  `http.Serve(pl, h)`, which is `(&http.Server{Handler: h}).Serve(pl)`.
- `os.Getenv.wp_proofEnv : os.Getenv.specEnv` (`Proof/os/GetenvEnv.lean`; vocabulary `Proof/os/EnvIs.lean`): the
  value read is the process's for the run (`osEnvIs key v`, opaque, per process: it takes the `HeapGS`). Beside
  `os.Getenv.spec`, not in place of it.

**The proxy hole, closed in the program** (`examples/etcd/dist/server`): `MainLogger` returns at once if
`HTTP_PROXY`, `http_proxy`, `HTTPS_PROXY` or `https_proxy` is nonempty (`proxyEnvSet`, `os.Getenv`), before any
net/http use (net/http reads them once, `envProxyFunc`'s `sync.Once`); nothing in the process sets them. Go tests:
`TestProxyEnvSet` (false with none set; true with each one; and non-vacuity: with none set
`httpproxy.FromEnvironment` proxies no peer URL, with each one set it proxies the peer URL of its scheme) and
`TestMainLoggerProxyRefused` (with `HTTP_PROXY` set `Main` returns before `NewServer`: no data directory).
`os=`/`io/fs=` added to project `putget-dist`'s lean roots (this repository's `os`, as etcd's packages). Not
Unsetenv: `os.Unsetenv` has no spec, and a model of it is a larger trusted change. Not the fork's `Proxy: nil`.

**Also changed in the program**: the peer handler is served after `s.Start()` (etcd's embed does the same:
`StartEtcd` starts the server, then `servePeers`): `/leases` waits on the server's apply wait, which `start` makes
(a forwarded lease request reaching a member before its `Start` would call a nil `*timeList`; after a crash a peer
may still forward to the restarted member as its old leader).

### 17.2 N2 (I-1): the service table's unary entries

**Not done: `etcdSvc` stays an axiom, and no `etcdSvc_unary` law is added.** The law of the plan (`etcdSvc γE mid
m.path = some ⟨Req.wire, Rep.wire, fun md γs => ∀ ν, envAt γE ν -∗ ▷ etcdMethodSpec m (etcdEnvOf ν) md γs⟩`) needs
`etcdEnvOf ν` (and the view's read names and cluster id) as *definitions* tied to the member's own names; over
today's `EnvView` (`⟨st⟩` only) they could only be opaque, and a table whose specs are at names the member does not
own would make `Serve_dist` (A3) claim a server meets specs it cannot meet (the client's deposit at other names
than the server's), while giving the clients nothing to derive A4/A5 from. Defining them is #24's S2 etcd side (in
flight with its owner): not duplicated here. What was checked (step 1, O1/O2):
- **Heap**: every client-facing unary spec has a heap-free form over `GooseGlobalGS` and `GoLocalContext` since
  2026-11-23 (KV: `etcdPutSpecW`, `etcdRangeSpecW`/`EW`, `etcdDeleteSpecW`, `etcdTxnSpecW`, `etcdCompactSpecW`;
  auth-on `…OnW`/`…MW`; lease `etcdLeaseGrantSpec*W`, `etcdLeaseRevokeSpec*W`, `etcdLeaseTTLSpec*W`,
  `etcdLeaseLeasesSpec*W`; auth `etcdAuthenticateSpecW`, `etcdUserAddSpecW`, ..., `etcdAuthEnableSpecW`). **The
  auth-on forms take a parameter `T`, which the server's registrations instantiate as `srvTLSId s`**
  (`srvCfgFieldAddr s "ClientCertAuthEnabled" ↦□ true`, `AuthnServedOn.lean`: a points-to on the member's heap): a
  table entry must fix `T` heap-free (e.g. `False`, the configuration's `ClientCertAuthEnabled` being false,
  `srvTLSId_false`), with the server converting.
- **The view** (O1): the specs read `E.γs`, `E.Nx`, `E.Cp`, `E.authOn`, the whole `ReadNames` (`committedAtLeast`
  reads `γr.committed`, `γr.raft`) and `cid`. `ReadNames.raft` holds `SrvRaft`, whose `rule` and `snapLoc : w64 →
  Option GName` are functions: not countable, so not a `dghostVar` value as it stands.
- **Restart** (step 5): `restartNames` (`InvRestart.lean`) keeps only `rd.raft`, `kvCongr` of `rd.kv` (with `st`),
  `ids.issued` and `ids.pfx`; `ReadNames`' other fields (`committed`, `applied`, `cursor`, ...) are the
  incarnation's. A view holding them would differ after a restart (a restarted member could not publish the same
  one); `committedAtLeast γr` reads `γr.committed`, so the crash theorem needs the client-facing specs stated over
  the cluster-level names only (`rd.raft`, `kvCongr`'s fields). Today's `EnvView` (`st`) is restart-stable
  (`restartNames_st`).
- A route found on the way, for #24's owner: the member's `ρ` and `E₀` are inputs of its boot (the start's share,
  `memberBoot γ ctxs ρ E₀ …`), and `NewServer`'s `E` agrees with `E₀` (`envAgree`: `γs`, `Nx`, ...): a table
  defined at the start over `E₀`/`ρ.rd` (no publication) may work once `E.Cp`'s agreement and the cluster id (a
  pure function of the members' ids) are checked.

Since no table content was added, A3's re-review (step 6) has nothing new to review.

### 17.3 The axiom reviews (2026-11-24; fresh agents with the `axiom` skill, given the code, not the reasoning)

- **`os.Getenv.wp_proofEnv`: sound**, docstrings corrected (the setters' evidence is that none has a spec and the
  Go closure of the programs has no non-test caller, not "the programs are verified"; `golang.org/x/sys/unix`'s
  setters; cgo's `setenv` does not reach Go's copy; per process *run*: `HeapGS` `⟨G, L⟩` with `L` bound per boot).
  Evidence `/tmp/envaxiom/` (not kept in the repository). Shared caveat of every names-only contract: the axioms
  quantify over every `go.Semantics`, whose `functions "os.Getenv"` could be any `GoFunc` (as `notes/audit.md`'s
  `dialWithBalancer` row).
- **`NewServer_dist`: unsound as first stated; fixed.** `httpPeerSvc` named no cluster, so a second ghost cluster
  (`srvClusterBoot_alloc` is a theorem) with the same configuration (same ids) could run a duplicate of member 1 at the
  same peer addresses; Go: the duplicate's raft panics (`tocommit(58) is out of range [lastIndex(3)]`, 5/6 runs, with
  bootstrap's `GET /members` refused by a fault). Fix applied: `httpPeerSvc γ id` (an address set once, for one
  cluster and one member), `Hpeers` at `γ pid`, the docstring's "allocated once by the start" argument replaced.
  **Re-review (fresh agent, same day): survives.** Routes blocked: two members at one address (`dirHostsDistinct`,
  `addrUnset` spent once), one id twice (`nodeVacant`/`raftState` exclusive; the docstring's "exclusive `nodeBoot`"
  corrected: `nodeBoot` is persistent), an own address set for another id, disagreeing peer configurations (ids, peers,
  contexts pinned to the cluster's allocation), relaying bytes (protocols per connection), the proxy, bootstrap's
  `GET /members` (a non-etcd server there crashes `NewServer`: `[null]` members, a nil dereference, unrecovered; out of
  reach through `Hpeers`). Hardening applied: indexed by the whole `SrvRaft` `γ`, not only `γ.cl`. Open, not a
  counterexample: `bootstrapCluster.spec` takes only `roundTripperOk H prt` and asserts no panic, its soundness
  resting on its callers' address facts (`Hpeers` here, `netHttpOk` in one process): state them in it, or say so.
- **`NewPeerHandler_dist`: sound.**
- **`PeerServe_dist`: unsound in combination with two existing axioms; recorded, not fixed here.**
  (1) The single-process start (`goose_adequacy_start`) hands out both the net extension's `addrUnset pa` and the
  HTTP registry's `httpProtoFree pa`: a one-process program sets `pa` with `http_addr_set`, serves the peer handler
  there with this axiom, reserves `pa` in the registry with a `True` request protocol (`http.reserve`) and sends a
  forged heartbeat through `rafthttp.NewRoundTripper`'s round tripper; Go: the member's raft panics
  (`tocommit(1000000) is out of range`). Fix (a trusted change on `lean`, for the owner): `http.reserve` also consumes
  `addrUnset a` (the `http.register`/`netAddrLeft` hole of `notes/putget-dist-plan.md` §12, review 5, is the same
  family). (2) The names-only `leasehttp.RenewHTTP` axiom posts to any URL: requests to `pa`'s `/leases/internal`
  (a recovered nil dereference), `/members/promote/<id>` (a rejected promote's conf-change entry reaches the log:
  outside `srvRule`/`ccLogOk`, no Go panic found), `/leases`. Fix: restrict `RenewHTTP` to a member's lease URL. Applied
  here: `pa` tied to the member's directory entry and its cluster (`httpAddrAt γ id pa`, `γn.N = srvNet γ`);
  docstrings no longer claim that nothing but the axioms writes at `pa`. Evidence `/tmp/peerforge/` (not kept).
- `etcdSvc` (A1) and A3: no new table content, so no re-review.
- **2026-11-25, the two holes of `PeerServe_dist`.**
  - **(1) closed: `http.reserve` narrowed** (`notes/axiom-review/http-reserve-pend.md`). Old:
    `⊢ httpProtoFree a ==∗ httpProtoAt a P ∗ httpProtoOwn a P`. New: `⊢ httpProtoFree a ∗ netAddrPend a ==∗ …` (the
    same post), `netAddrPend a` the address's exclusive empty pending set (`netPend NG a ∅`), which every law making
    an `addrProto` spends (`addr_set_proto`, `_tok`, `lis_set_proto` through `lisUnset`), so `http_addr_set pa` and
    `reserve pa` exclude each other. `net.Listen.spec` (proved) now takes `netAddrRsv` (`netAddrFree` without the
    pending set) and leaves `netAddrLis`; `netAddrFree_split`, `netAddrLeft_intro` rejoin. Re-proved users: the
    reservations (`netHttp_reserve3`, `netHttp_reserveL`, `alloc3Http`, `alloc3OnHttp`, `memberStartRes_split`,
    `alloc3`, `alloc3On`, `allocN`, `allocNOn`), the bundles (`memberFreshRes`, `memberRestartRes` hold `netAddrRsv`),
    the peer listeners (`etcdstart.NewMember`, `StartMemberAuth`, `auth3.startMember`, `restart`/`restartN`
    `newMember`, specs and proofs), the other `Listen` callers (`cluster3.StartBridge`, `cluster3.StartMember`,
    `etcdstart.Serve`) and the draft `ListenerClose_spec`. No new axiom, `sorry` or premise; no top-level statement
    changed.
  - **(2) open: `leasehttp.RenewHTTP` not narrowed.** Restricting `url` to a member's lease URL (`u ++ LeasePrefix`,
    `u` a peer URL of a cluster member, `http://<netAddrLit host>`) needs its one caller, `EtcdServer.LeaseRenew`
    (in the landed lease results: lease, leaseN, authlease, leaseexpiry(N), k8s), to know the leader's `PeerURLs`
    are such: `waitLeader`'s post and `RaftCluster.Member`'s say nothing of them (a fresh `Member` record, any
    strings), and the cluster's lock invariant (`rcLockInv`/`memAt`) records no fact of its members' peer URLs. A
    fact of the record alone is no restriction (a program allocates a `Member` with any URLs). So the landed proof
    of `LeaseRenew` uses `RenewHTTP` at URLs it knows nothing of, and narrowing it means first adding to the
    cluster's invariant a fact of every member's peer URLs (from bootstrap's `memberRO`/directory facts and each
    `AddMember`/`UpdateRaftAttributes` writer) and to `waitLeader`'s post. Stopped there (the task's rule: a landed
    result that cannot be re-proved without the old power); `PeerServe_dist` stays unsound in combination with
    `RenewHTTP` until then (its docstring says so).
  - **Fresh review** (`axiom` skill, given the axioms and the Go code, `RenewHTTP`'s route declared known): `PeerServe_dist`
    with the narrowed `reserve` **survives**. Attacks: reserve/set in either order; taking the pending set out of an
    address's invariant (cannot close it again); a wildcard listener (`lisUnset` holds `pa`'s pending set); two
    spellings of one socket (`addrOk`, `netAddrLit` canonical); `reserve` at a second `HeapGS` (its registry predicates
    are indexed by `hG`: inferred, unchecked); writing through the net extension (opaque `httpPeerSvc`); other clients
    (gRPC needs `grpc.start`'s listener at `pa`; the prober's `GET /raft/probing` is peer API; `leaseTimeToLive`
    forwards only in its cluster). Docstrings corrected as it asked (`PeerServeDist`, `InvNet`'s header, the review
    note). Side finding outside the targets: `rafthttp.addPeerToProber.wp_proof` admits a nil prober `p` (Go:
    `p.AddHTTP` panics); unexported, etcd's callers pass non-nil, so no counterexample; a premise `p ≠ nil` would
    make it true.
  - **`NewServer_dist` at its final text** (`httpPeerSvc` indexed by the whole `SrvRaft γ`, 4277b6acaf), fresh `axiom`-skill
    review with `PeerServe_dist`, `NewPeerHandler_dist`, the narrowed `reserve` and the starts. The three versions:
    unindexed (review affa32: **refuted**, a duplicate member in a second ghost cluster with the same configuration);
    cluster+member index (review a1f026: no counterexample); whole-`SrvRaft` index (this review: **survives**). Its
    argument: `httpPeerSvc` is opaque with no laws, so the re-indexing only refines the cluster+member version; a
    second `γ'` over one cluster is pinned out (`ownCommittedOps`, `nodeBoot`/`nodeVacant`/`raftState`, `srvRaftLogInv`);
    plus attacks 4-10 as for `PeerServe_dist` (registry, wildcard, aliasing, relay, `π`, proxy, double serve). Not
    tried: the crash law and restart path. Stale docstrings it found (`S5Interim`'s `httpAddrAt` "of the cluster `cl`",
    one-argument `httpAddrAt` in `NewServerDist`/`PeerServeDist`, `NewServerDist`'s "only the other members accept",
    `Start.lean`'s `netAddrFree`/`nameFree` wording) are fixed with route B's commit. Note: the dist top-level theorems
    still take the unindexed `S5Draft.httpAddrAt` as a hypothesis, so these axioms are on no exported result's path yet.
  - **Route B (2026-11-24, chosen with the coordinator), Go evidence** (`examples/premisefix/peerforge`, at the examples'
    etcd pin): `PromoteMember` of an unknown id is refused before any proposal (`isLearnerReady`: `ErrIDNotFound`, no
    entry applied); of a voter it proposes an `AddNode{IsPromote}` that apply rejects (`ErrMemberNotLearner`): one entry
    applied, members unchanged, no panic; the same through `RenewHTTP` to `/members/promote/<decimal id>`.
    `RenewHTTP` to `/leases/internal`: the handler dereferences a nil `LeaseTimeToLiveRequest`
    (`lease/leasehttp/http.go:123`, before any lock), `net/http`'s `conn.serve` recovers (`http: panic serving`), the
    client gets `EOF`; afterwards `LeaseGrant`, `LeaseRenew`, `LeaseTimeToLive`, `RenewHTTP` to `/leases` and `Range`
    succeed. 3/3 runs. Next: widen `ccApplyOk` to admit rejected promotes and re-prove its consumers.
  - **Route B, stopped before the widening (2026-11-25): it needs an axiom's statement changed.** With `v3`,
    `ValidateConfigurationChange` of a promote (`membership/cluster.go:324-330`) reads `membersMap[id].IsLearner`, and
    the member is present (every `cfg` id is a boot member in the `members` bucket), so the load is reached. The only
    source of `membersMap` is the trust-boundary axiom `schema.membershipBackend.MustReadMembersFromBackend.wp_proof`,
    whose post `membership.membersRead` gives each record's `PeerURLs` only (`memberURLsAt`), and its model
    `membership.membersOf` (opaque, with the axioms `membersOf_decode`, `membersOfBk_empty`) has codomain
    `GMap w64 (List GoString) × GMap w64 Bool`, no learner flag; so the promote branch has no proof and `ccValidM`
    cannot state Go's verdict (member present and a learner). Needed, for the owner: `membersOf`'s members carry
    `IsLearner` (`membersOf_decode` gives `(mm.peerURLs, mm.isLearner)`: `json.Unmarshal` of `json.Marshal` keeps a
    bool) and `membersRead` gives `mIsLearnerAddr l ↦ b` (`readMembersFromBackend` unmarshals the whole `Member`), or
    a new axiom on a separate opaque. Also: without `v3` (a replayed promote at restart, whose rejection set the
    consistent index) Go calls `RaftCluster.PromoteMember(id, false)`, names-only today (`membership.toml`): translate
    it and prove it (lock, `isLearner.Set(0)` for the local id, a log line, unlock). The rest is as planned:
    `ccApplyOk`'s promote disjunct, `ccValidM`'s promote branch, an invariant that every saved member is a voter
    (from `ccApplyOk`'s `isLearner = false` and `membersOf_decode`), then the consumers.

  - **Route B, steps 1-2 and the validation's promotion branch (2026-11-25).**
    - *The members extension* (approved for the final packet): `membership.membersOf`'s members carry the
      learner flag (`GMap w64 (List GoString × Bool) × GMap w64 Bool`); `membersOf_decode` gives the flags by
      id with no UTF-8 premise (a boolean and the key, which `json.Marshal`'s coercion never touches, as
      `memberEnc_id_learner`) and the `(peerURLs, isLearner)` pairs under `hu`; `membersRead` gives each
      record's `IsLearner` field (`memberReadAt`, in place of `memberURLsAt`). Go evidence
      `examples/axiomcx/memberslearner` (the real `snapshotmeta.ReadMembers` over `json.Marshal`ed members:
      the flag reads back, beside a peer URL coerced to U+FFFD). Docstrings cite the pin `6b942d23f`
      (`readMembersFromBackend` now reads the members through `snapshotmeta.ReadMembers`).
    - *`RaftCluster.PromoteMember` translated with its body* (`membership.toml`) and proved without
      `shouldApplyV3` (lock, the learner gauge for the local id, a log line, unlock); linked in the server's
      `Link`. `etc/goose.py --check` and `etc/gen-init.py --check` pass.
    - *`ValidateConfigurationChange`* admits a promotion's context (`∃ i b`) and `ccValidM` has Go's
      promotion branch (`ccIsPromote`: the member present and a learner); proved (`ErrIDNotFound`,
      `ErrMemberNotLearner`, `nil`).
    - **Stopped before widening `ccApplyOk`: it changes another axiom.** Admitting a promotion into the
      committed log's policy (`ccPolOk`/`ccLogOk`) makes `ccPolOk_static` (committed conf entries are
      `ccBootOk`) false, and its consumers on the snapshot path (`SnapRecvFacts`, `SnapRecvOn`,
      `ApplyAllSnapLemmas`) pass that fact to the trust-boundary axiom
      `membership.clusterImageOk_restModel`, whose premise is `∀ m ∈ L', m.typ ≠ 0 → ccBootOk γ.raft.cfg
      m.data`. Either its premise is widened (to the wide policy, so the axiom claims the image fact also
      for logs with promotions), or `ccBootOk` keeps its name with a wide meaning (the same claim,
      silently). Go: a promotion of a voter is rejected (`ErrMemberNotLearner`, no bucket written:
      `applyConfChange` returns before `PromoteMember`), and a replayed one (`PromoteMember(id, false)`)
      writes no bucket, so the widened claim is true of Go; but it is an axiom change beyond the members
      extension, for the owner. `BootFacts`/`BootCore.cc` (`ccBootOk`, defined from `ccApplyOk`) widen with
      it and must not be narrowed (coordinator, 2026-11-25: five top-level statements reach `ccApplyOk`
      through `BootFacts`; a weaker premise is a stronger theorem). So a boot entry may then be a
      promotion, and the boot proofs (`memBoot`, which inserts every boot change's member;
      `memOk_memBoot`, `boot_step`, `memSync_boot`) must handle it: `memBoot` should skip a promotion's
      member, matching Go (a boot promotion of an id not yet saved is rejected, `ErrIDNotFound`).
    - *Fresh review* (`axiom` skill, given the axioms and the Go code at the pin) of `membersOf`,
      `membersOfBk_empty`, the restated `membersOf_decode` and `MustReadMembersFromBackend`'s contract:
      **survives**. Attacks: the learner flag without `hu` (the real `ReadMembers`), ids at `0` and
      `2^64-1`, URL escapes and nil/empty slices under `hu`, `null` and extra records, the fresh records'
      ownership, the validation's promotion branch against `cluster.go:324-330`. Docstring citations
      corrected (the pin's `ReadMembers`/`MustParseMemberID`, `membership.go:84-117`). Side finding, not a
      counterexample (pre-existing): `apply.memberEnc` is a function of `MemberM`, but Go marshals a nil and
      an empty `PeerURLs` differently (`null`/`[]`); harmless while no verified reader sees the bytes;
      the robust form is "`MustSaveMemberToBackend` writes some value decoding to `mm`".

  - **Route B, step 3 stopped at the design (2026-11-25): the boot policy cannot widen.**
    - *Go evidence* (step 1, `examples/axiomcx/promotenobucket`, at the examples' etcd pin `6b942d23f`,
      3/3 runs): (a) the real server applies a promotion of itself, a voter: `PromoteMember` returns
      `ErrMemberNotLearner`, `applyConfChange` logs the validation's failure with `shouldApplyV3`
      and never runs `PromoteMember(id, true)`; the `members`, `members_removed` and `cluster`
      buckets are byte for byte as before; (b) restarted on the same data directory, the WAL replay
      applies the entry again with `shouldApplyV3` false (the rejection set the consistent index):
      `PromoteMember(_, false)` runs once ("ignore already promoted member"), no validation fails,
      the buckets as before; (c) the image read back (`MustReadMembersFromBackend`'s members with
      learner flags and peer URLs, the removed ids, the cluster version, the downgrade record) after
      (a) and after (b) equals the one before; (d) at the `RaftCluster` level, a promotion of an id
      not saved yet is `ErrIDNotFound`, writing nothing, and replayed writes nothing either.
    - *Why `ccBootOk` cannot widen with `ccApplyOk`* (the decision of 2026-11-25 assumed it could):
      a promotion among the **boot** entries is not harmless. Applied at the first boot with
      `shouldApplyV3`, it is rejected with `ErrIDNotFound` (its member not saved yet: (d)), so its
      member is never saved, while raft's bootstrap has already put it in raft's configuration. A
      restart then builds its conf state from the `members` bucket (`buildConfStateFromV3store`,
      the restart log's "Constructed a new raft snapshot from v3 state"), without that member. In
      the proof: `restModel_confState` (`RestConf.lean`, used by `StopShutdown`'s stop image) needs
      every id of `ps` saved (`memVoters`), which `boot_fold` gets from every boot entry being a
      non-promotion `AddNode`; with a boot promotion its conclusion is false of the model and of Go.
      So widening `BootFacts`/`BootCore.cc` would make the stop/restart results unprovable, not
      just need new cases (and the `memBoot`-skips-promotions plan does not help: the bucket, not
      `memBoot`, is what the restart reads). A promotion **after** the boot log is harmless (a), (b), (c).
    - *Proposed instead (needs the coordinator's OK, not done):* the boot policy stays as it is and
      only the committed log's policy widens. `ccAddOk` := today's `ccApplyOk` (a non-promotion
      `AddNode` of a voter of `cfg`); `ccApplyOk cfg m := m.type = 0 ∧ m.nodeId ∈ cfg ∧
      ((ccContextOf m.context = some (m.nodeId, false) ∧ (ccMemberOf m.context).isLearner = false) ∨
      ccContextOf m.context = some (m.nodeId, true))` (the §17.3 promote disjunct); `ccBootOk` defined
      from `ccAddOk` (its meaning unchanged, so `BootCore`/`BootFacts` and the five top-level
      statements unchanged: neither narrowed nor widened); `ccPolOk`/`ccLogOk` (the log invariant's
      and the KV invariant's per-entry policy) and `srvRuleKeeps` over the wide `ccApplyOk`;
      `ccPolOk_static` deleted (false), `srv_committed_ccBoot` returning the wide policy; the boot
      entries' narrowness kept as a new last conjunct of `srvClusterOk`
      (`⌜∀ e ∈ γ.raft.boot, ccBootOk γ.raft.cfg e.Data'⌝`, from `BootCore.cc` at the cluster's
      allocation; four `icases` patterns that name its current last conjunct get a `-`).
      `clusterImageOk_restModel`'s premise `∀ m ∈ L', m.typ ≠ 0 → ccBootOk cfg m.data` becomes
      `(∀ m ∈ L', m.typ ≠ 0 → ∀ cc, ccDecodeV1 m.data = some cc → ccApplyOk cfg cc) ∧
      (∀ j m, L'[j]? = some m → j < γ.raft.boot.length → m.typ ≠ 0 → ccBootOk cfg m.data)`, which the
      old premise implies (a pure widening); its docstring gains (a)-(d) and the voter argument
      (every saved member a voter, so a promotion never validates and `ccRest`'s promotion branch,
      unfaithful to `PromoteMember(id, true)`, is never taken).
    - *The re-proofs it needs* (estimated 1000-2000 lines): `applyConfChange`'s spec and proof get the
      promotion branches (with `v3`: a premise that a promotion does not validate, `ccValidOn rs.bk m
      = false`, which its callers in `EtcdServer__apply` derive from the rest model's voters; without
      `v3`: `PromoteMember(id, false)`, proved, and no `AddPeer`); `memSync` gains the members'
      learner flags (`restEntry_sync`, `fold_sync`, `memSync_boot`), `ccRest_memVoters` and
      `restEntry_memVoters` a promotion case (refused: the bucket's members are voters,
      `membersOf_decode`'s flags); the four `clusterImageOk_restModel` call sites (`SnapRecvFacts`,
      `SnapRecvOn`, `ApplyAllSnapLemmas` twice) the boot-prefix conjunct from `srvClusterOk`; the
      restart sites (`NewServerRFacts`, `StopShutdown`, `ApplyRDefs`) the boot facts from
      `srvClusterOk`; `srvRule_keeps` (`InvCfgView`) over the wide policy (it reads only the type and
      node); `InvApRes`, `ApplyRDefs`, `SDRun`, `KVLemmas`, `KVAuthModel`, `ProposeOn` follow.
      `etcd_noRefusal`/`etcd_noOtherRefusal` unaffected (a promotion of a voter changes no
      learner flag; their docstrings' `ccLogOk` caveat is about a re-add as a learner).

  - **Route B, done (2026-11-25; the design above approved by the coordinator).** Definitions
    (`SrvRaftLog.lean`): `ccAddOk` (the former `ccApplyOk`), `ccApplyOk` with the promotion disjunct,
    `ccBootOk` from `ccAddOk` (meaning unchanged), `ccWideOk` (the wide policy of an entry's bytes),
    `ccPolOk_wide` in place of `ccPolOk_static`, `srvRuleKeeps` and `srv_committed_ccBoot` over
    `ccWideOk`, `srvClusterOk`'s new last conjunct (the boot entries' `ccBootOk`, from `BootCore.cc` at
    `NewServerAlloc`/`NewServerAllocOn`), `srv_bootPrefix_ccBoot` (a committed log's first `|boot|`
    entries `ccBootOk`), `srv_first_boot`/`srv_first_entry` also give the first entry's
    non-promotion context. `clusterImageOk_restModel`'s premise widened as proposed (old premise
    verbatim: `(∀ m ∈ L', m.typ ≠ W32 0 → ccBootOk γ.raft.cfg m.data) →`; new: `(∀ m ∈ L', m.typ ≠ W32 0
    → ccWideOk γ.raft.cfg m.data) → (∀ (j : Nat) (m : EntryModel), L'[j]? = some m → j <
    γ.raft.boot.length → m.typ ≠ W32 0 → ccBootOk γ.raft.cfg m.data) →`). Re-proved: the four call
    sites; `RestConf` (`memVoters` now over a cover list, with the bucket's exact members and nothing
    removed; `ccValidOn_promote_false`, `memVoters_restModel`, `ccValidOn_restModel_promote`,
    `memVoters_boot`); `RestReplay` (`restEntry_sync`/`fold_sync` refuse a promotion through
    `memVoters`); the restart sites (`NewServerRFacts`, `StopShutdown`, `ApplyRDefs`: the boot facts
    from `srvClusterOk`); `applyConfChange` (spec: with `v3`, a promotion does not validate, a new
    premise; proof: the replayed promotion's `PromoteMember(id, false)`, linked); `EtcdServer__apply`
    (the premise from `srv_promote_novalid`, `ApplyRDefs.lean`). `BootFacts`/`BootCore` and the five
    top-level statements (etcd.dist, dist.putget, leaseexpiryN, etcd.all, k8s.all) unchanged in
    meaning: they reach the policy only through `BootCore.cc`'s `ccBootOk`, whose body now names
    `ccAddOk`, the same proposition the old `ccApplyOk` was. No axiom but the approved one changed,
    no `sorry`, `etcd_noRefusal`/`etcd_noOtherRefusal` untouched.
  - **Fresh reviews of route B** (`axiom` skill, given the axioms and the Go code, not the reasoning):
    (i) the widened `clusterImageOk_restModel`: **survives** (promotions of voters with odd contexts,
    case-folded and duplicate JSON keys, the boot boundary, replays, ids outside the configuration,
    context/node mismatch; a temporary Go test over the real `ValidateConfigurationChange`/
    `AddMember`/`PromoteMember` on bbolt, buckets byte for byte unchanged); docstring fixed as it asked
    (`PromoteMember(id, false)` also resets the local learner gauge; the route-B bullet's pin). Noted,
    pre-existing: the axiom takes no fact tying `γ.raft.boot` to the running cluster. (ii)
    `PeerServe_dist` with the unchanged `RenewHTTP`/`promoteHTTPOk` and the widened invariants:
    **survives** (a 3-member Go cluster, 4/4 runs: forged promotions of every voter through
    `RenewHTTP` at followers, unknown/out-of-range ids, 90 concurrent promotions across restarts and a
    full WAL replay; rafthttp's paths refuse `RenewHTTP`'s requests with 412; `/leases/internal`'s nil
    dereference recovered). Its docstring rewritten: sound against `RenewHTTP`'s request shape (not
    "any request": arbitrary bytes with raft's headers would crash raft, and no program can write
    them at `pa`), with the waiter note. The server-side `/leases/internal` panic recorded:
    `nonissues/etcd-leasehttp-internal-nil-request-panic.md`.

None of these axioms is in a top-level result's cone yet (no proof of `server.MainLogger` exists): they are not in
`etc/tcb-baseline.txt`; they join it, and `notes/audit.md`, with the first proof that uses them.

## 18. O1 and N2: the client-facing view and the clientv3 interim contracts (design, 2026-11-25; branch `etcd-safe-n2/2026-11-25`)

The etcd_safe lead's spec phase for #50's O1/N2 (coordinator-E's answers 7166749927, item 6: per-function interim axioms
at clientv3's interface, not an `etcdSvc` law). **Design only: no axiom added, nothing built** (the VM was down; no local
Lean). Base `etcd-safe-main-r3/2026-11-25` @ `5a1c41d945`. Drafts: `Proof/.../etcd/dist/ClientViewDist.lean` (defs and
`.spec` abbreviations only, namespace `etcd_dist.view`, unbuilt, imported by nothing). The coordinator picks the O1 option
before any axiom review or proof.

### 18.1 The workloads' clientv3 calls

U = unary, S = stream (N3). "Machine": O = the workload's orchestrator, N = its client machines (`NodeMain`). Every client
is `etcdstart.NewClients` (`clientv3.New` with `grpc.WithNoProxy()`, no RPC) except `auth.go`'s `newUserClient`
(`clientv3.New` with `Username`: `New` itself calls `Auth.Authenticate`).

| Workload | Machine, endpoints | Calls | Member state the specs read / change |
|---|---|---|---|
| kv | N (`kvremote.Node` → `txnlin.Call`), all eps rotated | `Get(k)` U, `Get(from, WithRange(to))` U, `Put` U, `Delete` U, `Txn().If(cmps).Then(ops).Else(ops).Commit()` U (cmps on Value/Version/ModRevision; ops Get/Put/Delete) | KV state (`etcdKV γk`: reads by a persistent read update, writes by a one-shot update); reply revisions, versions, mod revisions |
| putget | O, all eps | `Put` U, `Get` U | KV state |
| durable | O, all eps | `Put` ×n U, `Get(prefix, WithPrefix())` U | KV state (values, version 1) |
| compact | O, all eps | `Put` U, `Compact(rev)` U, `Get(k)` U, `Get(k, WithRev(r))` U; `Watch(k, WithRev(2))` S ×2 (`checkCompactRev`) | KV state; revision reached (`kvRevLb`, the cluster's `rlog`); compaction mode `cmp`, retention `cret`; the compaction revision (watch: N3) |
| watch | O (all eps); N writers (all eps rotated) | O: `Watch(prefix, WithPrefix, WithRev(1), WithProgressNotify, WithCreatedNotify)` S; N: `Put` U (`etcdstart.Writer`) | KV state, watch history (N3) |
| cache | O (all eps); N writers | O: `cache.New` (its watch S, and the cache's own `KV.Get` U in `get`/`serverRevision`), `c.Watch` S, `c.RequestProgress` S, `c.Get(prefix, WithRev)` (served by the cache, which may call `KV.Get` U); N: `Put` U | KV state, watch history (N3) |
| auth | O (eps[0], then every member); N principals (one member each) | O: `auth.SetUp` (`Put` ×8, `UserAdd`, `UserGrantRole`, `RoleAdd`, `RoleGrantPermission`, `UserAdd`, `UserGrantRole`, `UserAdd`, `AuthEnable`, all U); barriers: `New(Username)` (`Authenticate` U) and `Get` U per member; root's `Put` U; root's and u's `Watch` S. N: `New(Username)` (`Authenticate` U), `Put` ×2, `Get` ×3 (ranges), `Txn…Commit` ×4 (one nested), `Delete` ×2, all U; a refused `Watch` S | auth store (users, roles, enabled), the auth history (`KVNames.hist`), tokens (`γa`), KV state |
| authLease | O only (eps[0], eps[1], eps[2] mod k) | `auth.SetUp`, barriers, `New(Username)` ×3; `Lease.Grant` U, `Put(WithLease)` U, `Txn().Then(OpPut WithLease).Commit()` U; refused `Grant`/`Revoke`/`TimeToLive`/`TimeToLive(WithAttachedKeys)`/`Leases` U; refused leased `Put`/`Txn` U; `Get` U, `Revoke` U | lessor (leases, attachments), auth store, KV state |
| leaseRead | O, one member at a time | `Lease.Leases` U, `Lease.TimeToLive(id)` U | nothing of the member (the listing has no duplicate, the TTL reply's id is the one asked) |
| leaseCatchup | O: one client of member k-1, one of member 0 | `Lease.Grant(maxTTL)` U at k-1, `Grant` ×20 U at 0, `Leases` U polled at k-1 | member k-1's lessor history (monotone mode) |
| leaseExpiry | O: one client per member | `Lease.Grant(1)` U per member, `Leases` U polled and once more | each member's lessor history (revocable mode: absent stays absent) |

(`AwaitCluster`'s `Get` is k8s/dist's, not on etcd_safe's path.)

What the proved client-side specs read (the specs these drafts mirror, `Spec/go_etcd_io/etcd/client/v3/`): `kv.Put/Get/
Delete/Compact.spec` and `txn.Commit.spec` are stated over `isKv api γ dup` and read the member only through `γ : KVNames`
(`etcdKV γ` = its `st`; `kvRevLb`/`kvRevLbZ` = its `rlog` and `kvModel`'s `c0`/`ch0`/`log0`; `cmp`, `cret`); `isKv_intro`
asks of each member only `kvSame x.γr.kv γ` and, for one-shot writes, `noRefusalAt`. Nothing of `E`, of `ReadNames`'
incarnation fields (`committed`, `applied`, `cursor`, ...) or of `cid` reaches those posts: the floors (`committedAtLeast γr
0`, `kvLogLb E.γs []`) are internal to the client proofs. The lease specs at a lessor read only `γl` (`leaseGrantedAt`,
`lessorLb`, `leaseIdsAt`, `leaseLiveFrom`, `leaseReqIs`). The auth specs read `γa` (`etcdAuthenticateSpecW`), `T`, `E` and
`ρ` (`authHistAuT`, the auth history `hist`).

### 18.2 What is restart-stable

- KV: `kvCongr` (what `restartNames` keeps) has every `kvSame` field, so every incarnation of every member is `kvSame`
  to the cluster's `γk` (`ClusterNames.γk`, `clusterAllocN`'s). **The KV specs are already cluster-level and restart-stable.**
- Lessor: `γl = mvcc.api.mvccLeases E.γ` is `NewServer`'s choice (existential `E` in `NewServer.specG`'s post; a restart's
  `NewLessor` recovers into a fresh history, `lease.srvInvAt … σ₀`). **Not known at the start, not restart-stable.**
- Auth: `γa` (`E.authMode = .on γa`) is `NewServer`'s; `KVNames.hist` is a member's own (outside `kvCongr`). **Not
  restart-stable.**
- `SrvRaft` is not countable (`rule`, `snapLoc` are functions): no `dghostVar` holds it. No draft needs it.

### 18.3 O1: three options

| | A. Publish a larger `EnvView` | **B. The view is the start's cluster names (recommended)** | C. B for the KV, A's publication for `γl` |
|---|---|---|---|
| What | `EnvView` gains the `kvSame` fields (countable) and `γl`; the member publishes after `NewServer` (`env_publish`) | `DistView := ⟨kv, ls, auth⟩`, a Lean value: `ClusterNames.γk`, a new per-member lessor name `ls mid` allocated by the start, the auth mode. `etcdSvc` and `etcdAddrAt` indexed by `Γ` in place of `γE`; no publication | KV and auth mode as B; `γl` published per member (one-shot `dghostVar` of a `GName`) |
| Where it lives | the publication invariant (`envPubInv`), read under a later (`envAt_pub`) | the start's share as a value: `etcdClusterStart` already runs `clusterAllocN` before it sets the client addresses (`members_svc_start`), so `etcdAddr_set` at `Γ` needs nothing new; `memberBoot γ ctxs ρ E₀` gets `ρ.rd.kv = c.γk` from its slice; `envAgree` is not needed (no draft reads an `E` field) | both |
| Server side | `Serve_dist`'s `ν = memberView ρ` | `Serve_dist` takes `⌜memberViewOk Γ ρ⌝` (`kvCongr ρ.rd.kv Γ.kv`; with P-L1 also the lessor's tie) in place of `envAt γE ν ∗ ⌜ν = memberView ρ⌝`; a restart gets it from `restartNames` (`kvCongr` is an equivalence) | as B, plus the publication |
| Restart (D6) | **breaks**: the view is one-shot per address, a restarted member's `γl'` differs, so it cannot serve | **holds** (by construction: only restart-stable names) | KV holds; lease drafts usable in `etcd_safe_nocrash` only |
| Multi-endpoint clients (kv, putget, durable, compact, watch, cache, writers) | a view per member: the reply is "at some member's view" | one `Γ` for every member: the drafts are exactly `kv.X.spec` | as B |
| Lease drafts | axiomatizable now (the name is the server's own) | **after P-L1** (below) | now, nocrash only; restated for the crash theorem later (two reviews) |
| Cost | publication of non-restart-stable names; a second form for crashes | re-index A1/A2/A3/A4/A5 (all interim, in the packet: re-review); P-L1 | both forms |

**Recommendation: B.** It is the only option where every name an axiom mentions is a name a server proof owns, the same
statements serve `etcd_safe_nocrash` and `etcd_safe`, and the multi-endpoint workloads use the proved `kv.X.spec` shape
unchanged. It also removes machinery: `envPub_start`/`env_publish`/`envAt_pub` and the review-F2 later leave the dist
starts, and `Client_Put_dist`/`Client_Get_dist` (A4/A5, putget-specific) become corollaries of `KV_Put_dist`/`KV_Get_dist`
(`putGetInv` is a client invariant over `etcdKV Γ.kv`): two axioms fewer, theorems in their place.

**Why the server side needs nothing more now.** `etcdSvc` stays an opaque axiom with no law (§17.2), so no proof learns an
entry; the client-side axioms carry each call's contract, and `Serve_dist` (post `True`) only ties the address to a member
whose names agree with `Γ`. At retirement (#24's S2: `etcdSvc` defined, `Invoke` over the net model), each entry is the
member's `etcdXSpec E ρ.rd cid mid`, and the dist statement is `kv.X.spec`'s proof over an `isKv` built from the
registration (`isKv_intro`: `kvSame` from `memberViewOk`).

**Prove items B needs (no trust):**
- **P-L1 (before any lessor-reading axiom):** `NewServer.specG` (and `specC`/`specR`) take the lessor's history name from
  the caller (`lease.lessorAt γL 0 σ₀` allocated by the start, `mvcc.api.mvccLeases E.γ = γL` in the post), as `ρ` is
  taken today; `ClusterNames` gains `ls : w64 → GName`. Without it the lease drafts' facts would be about a name whose
  authority sits unused in the member's share, which an axiom review would refute (a client fact contradicting the empty
  authority).
- **D6 (crash theorem only):** a restarted member's lessor history continues at `ls mid`. Go's reason is the ready gate
  (`examples/etcd/dist/server/server.go:202`, `<-s.ReadyNotify()` before serving clients: the replay re-applies what a power
  loss took from bbolt before the member's own publish entry applies), whose meaning is that file's `TODO(proof)`. Without
  it a restarted member could list a lease revoked before the crash (`Recover` reads bbolt at a lower consistent index):
  leaseExpiry's check would be false.
- Auth (N11): the same treatment (per-member auth names in `Γ`), not designed here.

### 18.4 N2: the drafts (`ClientViewDist.lean`)

Each is `abbrev X.spec (svc : DistView → w64 → GrpcSvc GF) : Prop`; `svc` stands for A1 re-indexed at `Γ` (the axiom would
be `X.wp_proof : X.spec etcdSvcV`). Shape as `Client_Get_dist` (`isNewClient`, `clientNoProxy`, the address fact, a client
context), with `levelTok 0` threaded as in the proved specs (the retiring proof needs it; a stronger precondition is a
weaker axiom), the error arm `⌜err ≠ nil ∧ resp = null⌝` only (no `kvErr`/`statusErrOk`: nothing claimed of a remote
error).

| Draft | Function | Mirrors (client spec / server spec) | Reads of `Γ` | Axiomatizable |
|---|---|---|---|---|
| `KV_Put_dist` | `(*kv).Put` | `kv.Put.spec` at `dup = false` / `etcdPutSpecW` | `kv`, `auth = false` | after O1-B |
| `KV_Get_dist` | `(*kv).Get` | `kv.Get.spec` / `etcdRangeSpecEW` | `kv` | after O1-B |
| `KV_Delete_dist` | `(*kv).Delete` | `kv.Delete.spec` at `dup = false` / `etcdDeleteSpecW` | `kv`, `auth = false` | after O1-B |
| `KV_Compact_dist` | `(*kv).Compact` | `kv.Compact.spec` / `etcdCompactSpecW` | `kv` (`cmp`, `cret`) | after O1-B |
| `Txn_Commit_dist` | `(*txn).Commit` | `txn.Commit.spec` at `dup = false` / `etcdTxnSpecW` | `kv`, `auth = false` | after O1-B |
| `Lease_Grant_dist` | `(*lessor).Grant` | `lessor.Grant.spec` at `etcdLeaseGrantSpec γl` / `etcdLeaseGrantSpecW` (mono) | `ls mid`, `kv.lm = .mono` | after P-L1 |
| `Lease_GrantLive_dist` | `(*lessor).Grant` | `lessor.Grant.spec` at `etcdLeaseGrantSpecLive γl` / `etcdLeaseGrantSpecLiveW` | `ls mid`, `kv.lm = .revocable` | after P-L1 |
| `Lease_LeasesGranted_dist` | `(*lessor).Leases` | `lessor.Leases.spec` at `etcdLeaseLeasesSpec γl` / `etcdLeaseLeasesSpecW` | `ls mid`, mono | after P-L1 |
| `Lease_LeasesLive_dist` | `(*lessor).Leases` | `lessor.Leases.spec` at `etcdLeaseLeasesSpecLive γl` / `etcdLeaseLeasesSpecLiveW` | `ls mid`, revocable | after P-L1 |
| `Client_LeaseLeases_dist` (etcd-grove-03's) | `(*lessor).Leases` | `lessor.Leases.spec` at `etcdLeaseLeasesSpecAny` / `etcdLeaseLeasesSpecAnyW` | nothing | after O1-B (or now, over `γE`) |
| `Client_LeaseTimeToLive_dist` (etcd-grove-03's) | `(*lessor).TimeToLive` (no options) | `lessor.TimeToLive.spec` at `etcdLeaseTTLSpec` / `etcdLeaseTTLSpecW` | nothing | after O1-B (or now) |

The workloads call `cli.Put`/`cli.Get`/... (`*Client`'s promoted methods through its `KV` field): a proved promotion lemma
per method gives them from the `(*kv)` drafts, so the axioms sit at the functions the proved specs are about. The cache
library's own `c.kv.Get` is `KV_Get_dist` directly.

**Per workload:** kv, putget, durable, writers: `KV_Put/Get/Delete_dist`, `Txn_Commit_dist`; compact: `KV_Put/Get/
Compact_dist` (its `kvRevLbZ Γ.kv (rev + 1)` is the Put's `kvRevLb` at `rev + 1`); leaseRead: the two view-free ones;
leaseCatchup: `Lease_Grant_dist` at k-1 and 0, `Lease_LeasesGranted_dist` at k-1 with `G = [g1]` (leasecatchup's argument
verbatim: g1 is listed whatever the fillers do); leaseExpiry: `Lease_GrantLive_dist`, `Lease_LeasesLive_dist`
(leaseexpiryN's `gone`/`listed` over `leaseAbsentFrom`, `lessorLb` from the previous listing).

**Why none can be proved now, in the standing rule's order** (same for all eleven):
1. *The real Go is translated* (clientv3 with bodies, grpc-go's model `models/grpc`), and its functions are proved in one
   process (`kv.X.spec`, `lessor.X.spec`) over `Invoke`'s registration (`isGrpcRpcsMd`, `kvRegsAt`). Across machines the
   call goes through grpc's `Invoke` over the net extension: the S2 interface exists (`grpcAddrAt`, opaque
   `grpcCliPI`/`grpcSrvPI`), but no proof establishes the protocols of any bytes and `etcdSvc` has no law, so nothing can
   be proved over the existing S2/S5 statements. Needs #24's S2 client side (`notes/phase7-plan.md` §1.3, §2.4).
2. *A Go model with the same behaviour* is the grpc model itself, which is what S2 proves over: the same gap.
3. *Trusted code*: a stand-in for clientv3 + grpc would still need the wire proof, and would trust more than a contract per
   function.
So each is an interim axiom with that reason; the lessor four also wait for P-L1. Each needs a fresh `axiom`-skill review
(given the code, not this reasoning) and enters the single etcd_safe packet.

**Soundness for a remote call (Go):**
- *Who answers.* `clientNoProxy`: the client dials the endpoints themselves (F1). `etcdAddrAtV ep Γ mid` is set once by the
  start (`addrUnset` spent) and served only by `Serve_dist` at a member with `memberViewOk Γ ρ`; `bridge.New` consumes
  `netAddrLeft` (review 4). So every reply is a real member's handler at names `kvCongr` to `Γ.kv`.
- *Errors, timeouts, retries are the error arm.* A deadline is `ctx`'s error (`DeadlineExceeded`); a partition or a crashed
  member is `Unavailable`; both return `err ≠ nil` with no claim. Reads: clientv3's retry interceptor retries an immutable
  RPC on `Unavailable` at the next endpoint (`isSafeRetryImmutableRPC`); the read update is persistent (`□`), as in
  `kv.Get.spec`. Writes (`Put`, `Delete`, writing `Txn`): retried only after a refusal (`isSafeRetryMutableRPC`), which an
  auth-off member never sends to a KV call (`etcd_noRefusal`'s argument, `noRefusalAt`), so a write is sent at most once:
  the one-shot update. A write whose call errs may still be applied later (the member already proposed it): the update was
  handed over and the error arm returns nothing of it, the unknown outcome the workloads' checks already allow.
- *What a success claims* is `kv.X.spec`'s post, which the in-process proof derives from the member's `etcdXSpecW` at its
  names through `kvSame`: header revision, the state the update fired at, `kvRevLb` of the cluster's `rlog`. Lease ones:
  the member-local facts at its lessor (`LeaseLeases` is `EtcdServer.LeaseLeases`, the member's own lessor, no read index:
  hence one endpoint and `ls mid`); `LeaseGrant` replies after the member's apply of the grant (the reply waits on the
  apply wait), so the grant is in that member's history.
- `Compact` with `cmp = true` implies auth off (`NewServer`'s `cmp = true → on = false`); its call is idempotent past the
  compacted revision (an error then), so a retry is harmless either way.

**F7's auth-on rows (S1, 2026-11-26; drafts in `Proof/.../dist/AuthViewDist.lean`, review list
`notes/etcd-dist-f7-reviews.md`).** All read `Γ.auth = true`, `Γ.kv` (`hist`, `rlog`) and, where member-local,
the member's auth names `A mid` (`Γ.au` after P-A1); every success arm names the serving member and its check, every
error arm claims nothing (the lead's condition, #50 01:29:52Z). F2's three rows "after F7's auth view" are
`KV_PutOn_dist` (its `leaseID ≠ 0` case is `KV_PutLease_dist`), `Lease_RevokeOn_dist`, `Lease_TimeToLiveKeysOn_dist`.

| Draft | Function | Mirrors (client spec / server spec) | Reads of `Γ` | Axiomatizable |
|---|---|---|---|---|
| `New_user_dist` | `clientv3.New` (user) | `clientv3.New.spec` / `Authenticate`'s `CheckPassword` | `kv`, `A mid` | after review |
| `KV_PutOn_dist` | `(*kv).Put` (incl. `WithLease`) | `client_put_on` / `etcdPutSpecOn` | `kv` | after review |
| `KV_DeleteOn_dist` | `(*kv).Delete` | `client_delete_on` / `etcdDeleteSpecOn` | `kv` | after review |
| `Txn_CommitOn_dist` | `(*txn).Commit` | `client_txn_on` / `etcdTxnSpecOn` | `kv`, `A mid` | after review |
| `KV_GetOn_dist` | `(*kv).Get` | `client_range_on` / `etcdRangeSpecOn` | `kv`, `A mid` (the floor) | after review, P-A1 |
| `Auth_UserAdd_dist`, `Auth_UserGrantRole_dist`, `Auth_RoleAdd_dist`, `Auth_RoleGrantPermission_dist`, `Auth_AuthEnable_dist` | `(*authClient).X` | `authClient.X.spec` / `etcdXSpecW` | `kv` (`hist`) | after review |
| `Lease_GrantOn_dist` | `(*lessor).Grant` | `client_lease_grant_on` / `etcdLeaseGrantSpecOn` | `kv`, `ls mid`, `A mid` | after review, P-L1, P-A1 |
| `Lease_RevokeOn_dist` | `(*lessor).Revoke` | `client_lease_revoke_on` / `etcdLeaseRevokeSpecOn` | `kv`, `A mid` | after review, P-A1 |
| `Lease_TimeToLiveKeysOn_dist` | `(*lessor).TimeToLive` + `WithAttachedKeys()` | `lessor.TimeToLive.spec` / `etcdLeaseTTLSpecMdW` | `ls mid`, `A mid` | after review, P-L1, P-A1 |
| `Lease_LeasesOn_dist` | `(*lessor).Leases` | `lessor.Leases.spec` / `etcdLeaseLeasesSpecMdW` | `ls mid`, `A mid` | after review, P-L1, P-A1 |
| `Serve_dist_proposed`, `NewServer.specG_dist_proposed` | `etcdstart.Serve`, `NewServer` | the current axioms (re-review) | `kv.hist`, `A mid` | S2 (`Proof/.../dist/AuthServeProposed.lean`) |

### 18.5 Streams (N3, out of scope): what they would need

`watcher.Watch` and `RequestProgress` (watch, compact ×2, cache's own watch, auth's root/u/refused watches): a stream
contract (SW1's `.stream` entries, or an interim `Watch_dist` axiom) over `Γ.kv`: the events are the KV history at the
cluster's `st` (a cluster-level history name: the proved `WatchCheck`/`WatchRun` specs are over the watch environment `V`,
whose server names would have to be `Γ`'s); the compaction revision's facts (`E.Cp` is a member's: needs a cluster-level
permit, e.g. from `rlog`/`cret`); progress notifications' revision; resumption at another endpoint after a fault
(`WatchResume`, multi-endpoint); restart-stability of all of it (D6).

### 18.6 Implementation (2026-11-25; option B, the coordinator's decision)

**The view.** `DistView := ⟨kv, ls, auth⟩` (`S2Interim.lean`), a Lean value; `DistView.ofKV γk` the auth-off view
(lessor names a constant until P-L1: no contract reads them); `ClusterNames.view c := DistView.ofKV c.γk`.
`etcdSvc (Γ : DistView) (mid)`, `etcdAddrAt a Γ mid`, `membersAt eps Γ` (every endpoint some member's),
`etcdAddr_set` at `Γ`. **Removed** (clean end state, no compat layer): `EnvView`, `memberView`, `envPubN`,
`envPubHalf`, `envAt`, `envPubInv`, `envPub_start`, `env_publish(_h)`, `envAt_agree`, `envAt_pub(_h)`,
`putGetInv_st`; in the starts `memberSvcShare`, `cluster_svc_start`, `svcList`, putget's `memberPubOk`/`putgetPub`,
putgetk's `memberPubOkK`/`kvAgree`/`rnOf`.

**Trusted statements** (reviewed: `notes/axiom-review/n2-kv-dist.md`, a fresh `axiom`-skill agent given the code;
all seven sound after F1-F5, re-reviewed):
- `etcdSvc` re-indexed by `Γ` (was `γE : GName`).
- `Serve_dist.spec`: `(Γ : DistView)` for `(γE : GName) (ν : EnvView)`; the pure premise `… ∧ kvCongr ρ.rd.kv Γ.kv ∧
  Γ.auth = false` in place of `… ∧ ν = memberView ρ` and `envAt γE ν`; the address fact at `Γ`. (`Γ.auth = false`:
  review F2, a weaker axiom; the member's own auth is off by `memberUp`.)
- **New interim axioms** (each its own Spec/Proof pair beside `ClientGetDist.lean`, the header saying why: real Go
  translated, the cross-machine proof needs #24's S2 client side, retired by it): `KV_Put_dist.wp_proof`,
  `KV_Get_dist.wp_proof`, `KV_Delete_dist.wp_proof`, `KV_Compact_dist.wp_proof`, `Txn_Commit_dist.wp_proof`, the
  §18.4 drafts verbatim but for `svc` (the table is `etcdSvc`) over `kvClientAt` (`KVClientDist.lean`).
- **Retired axioms**: `Client_Put_dist.wp_proof` and `Client_Get_dist.wp_proof` are theorems
  (`ClientPutDist.lean`, `ClientGetDist.lean`) from `KV_Put_dist`/`KV_Get_dist` taken as hypotheses (the promotion
  `ptr_Put_unfold`/`ptr_Get_unfold`, putget's updates at KV names: `putGetInvK`, `putAu_of_putGetInvK`,
  `getAu_of_putGetInvK` in `KVClientDist.lean`). Their statements changed (no publication): `(Γ : DistView) (mid)
  (γf : GName)` for `(γE : GName) (mid)` (and, in Get, `(ν : EnvView) (γr : ReadNames) (γf)` with `γr.kv.st = ν.st`);
  pre `levelTok 0 ∗ … ∗ etcdAddrAt ep Γ mid ∗ … ∗ putGetInvK Γ.kv γf key val` (Get: `∗ monoNatLbOwn γf 1`), Put also
  `Γ.auth = false`; post `levelTok 0 ∗ ((⌜err = nil⌝ ∗ monoNatLbOwn γf 1) ∨ …)` (Get: the old value arm). Not
  top-level statements.
- Lease drafts stay `.spec` definitions in `ClientViewDist.lean` (re-indexed: `etcdAddrAt ep Γ mid`; P-L1).
  etcd-grove-03's `Client_LeaseLeases_dist`/`Client_LeaseTimeToLive_dist` are not on this line: left alone.

**Top-level statements**: no text change (`putget_safe.spec`, `putgetK_safe.spec` and the etcd_safe skeleton's
named none of `γE`/`envAt`).

**Proofs adapted.** `srvMemberBoot_alloc`, `memberBoot_of`, `memberBoot_of_slice` also return `kvCongr ρ.rd.kv γk`
(proved; their users' patterns adjusted: `alloc1`, `alloc3Http`, `memberBoots_of`). `ClusterStart`: `memberStartShare`
holds the address fact at `c.view`, `clientStartShare c ms` each member's; `etcdClusterStart` returns `c` only.
putget: the start runs `clusterAllocN` at `[id]` (`putget_shares`; the view fixed before the member runs), allocates
the client's `putGetInvK` from the cluster's `etcdKV`, sets the client address (`putget_addr`); the member starts
from its slice (`wp_StartServer1_slice`, `StartOneSlice.lean`: `memberBoot_of_slice`, `net1_alloc`, `StartServer`)
and serves at `c.view`; the client's `Put`/`Get` are the theorems. putgetk: the same over `etcdClusterStart`; a
refused configuration's client share is at a fresh view (`putGetInvK_alloc_fresh`).

**Go** (§18.8 item 4): `dist/client/auth.go`'s `newUserClient` dials with `grpc.WithNoProxy()`; `go vet`/`go test`
of the client package; `TestDist -short` with `DIST_RUN=1 DIST_WANT=auth` passes (an auth workload, kills, power
losses, partitions); `etc/goose.py --project putget-dist` retranslated (`client.lean`), `etc/gen-init.py` regenerated
the client's `Init`/`InitLinked`/`PkgTable` (`--check` passes).

**Build and trust base** (VM, full `lake build` green, 28674 jobs, at `72794bc473`): `tier-check --check` ok
(208 known), `bounds-check --check` ok (390); gen-link: every dist/putget/server link agrees (the five differing
modes, `--bbolt`, `--kvraft`, `--kvraft-udp`, `--wal-tester`, `--walfs`, touch nothing here). `tcb-report --check`:
**`etc/tcb-baseline.txt` gains `etcd_dist.KV_Put_dist.wp_proof` and `etcd_dist.KV_Get_dist.wp_proof` and loses
`etcd_dist.Client_Put_dist.wp_proof` and `etcd_dist.Client_Get_dist.wp_proof`**, and `putget-dist.txt` the same (no
publication axiom existed: the publication was proved). `KV_Delete_dist`, `KV_Compact_dist`, `Txn_Commit_dist` are
declared but reached by no root yet (M1's Node links them), so the report, which lists the axioms the roots rest on,
does not list them; they enter the baseline with their first user.

### 18.7 Changes to etcd-grove-03's two drafts

Bodies unchanged. Under B: `etcdAddrAt ep γE mid` → `etcdAddrAtV svc ep Γ mid` (inside `leaseClientV`), and `levelTok 0`
threaded through pre and post (as `lessor.Leases.spec`/`lessor.TimeToLive.spec`). Their proofs (`leaseList`,
`leaseReadCheck`, `RunLeaseRead`) need only that rename and the token (their `RunLeaseRead.spec` already keeps
`levelTok 0`). Under A they stay as they are.

### 18.8 Open questions

1. **O1: A, B or C** (recommended B). With B: the re-indexing of A1-A5 is a trusted change (re-reviews), and A4/A5 become
   theorems.
2. **P-L1 ownership**: `NewServer`/`NewLessor` taking the lessor name (server proof work, no trust); who takes it.
3. **The ready gate's meaning (D6)**: needed by every lessor draft in `etcd_safe`, and by any read that a restarted member
   must not answer from a stale bbolt image.
4. **Auth (N11)**, two Go findings for its design: `dist/client/auth.go`'s `newUserClient` has no `grpc.WithNoProxy()` (the
   F1 hole for every user client of auth and authLease: `clientNoProxy` fails, a program change); with auth on a write is
   retried after an auth refusal (`ErrInvalidAuthToken` → token refresh → resend), so the auth-on write drafts need the
   persistent update (`dup = true`), not the one-shot one. Also `γa` and `KVNames.hist` need B's per-member treatment.
5. **authLease's refusals** (`TimeToLive(WithAttachedKeys)`, `Revoke`, leased `Put`/`Txn`): only "an error" is checked; the
   drafts would be auth-on forms (N11b), with `T := False` (the configuration's `ClientCertAuthEnabled` false,
   `srvTLSId_false`) fixed heap-free in the table.
6. **Naming at adoption**: the general `KV_Put_dist`/`KV_Get_dist` are stronger than A4/A5, so by the naming rule they take
   the plain names and the putget forms become `Client_Put_dist_putGet`/`Client_Get_dist_putGet` (theorems).

## 20. No-crash landing line (2026-11-25, branch `etcd-safe-nc/2026-11-25`)

The line that lands the multi-machine theorems without crashes (`etcd_kv_safe_nocrash`, then
`etcd_safe_nocrash`), with **none of the crash work or crash trust**: the crash line's trusted items go to the
owner as their own packet. §16's rounds describe the crash line (`etcd-safe-main-r3/r4`); this line reused only
their resolutions of files with no crash content. From `lean` @ `08313db96d`, in order:

| # | what | head |
|---|---|---|
| 1 | merge `etcd-safe-lit/2026-11-24` (D2's translation, deployment/`WellFormed`, the restated statements and skeleton, `BootBad`) | `c022542b8b` |
| 2 | merge `etcd-safe-transport/2026-11-24` (S5's interim axioms, the proxy check, route B; carries putgetk up to `faeb92b070`) | `f152a3be06` |
| 3 | merge `dist-putgetk/2026-11-24` (the newest pushed putgetk head; `lean` has none of it) | `650a7c4887` |
| 4 | round 1-3's non-crash integration changes (below) | `9f1b410842` |
| 5 | `etcd-safe-bootax/2026-11-25`'s five commits since `etcd-safe-main-r3` @ `5a1c41d945`, cherry-picked (`-x`) | `7c022029c1` |

Excluded: `etcd-safe-crashskel`, `-crash` (D4a-c', P10/P11, C-I1, `BoltCrashWhole`, the fs extension's
`szCrash`), the etcd pin bumps (`8aa40fd5c`, `47d6cdeeb`, `e94f33b50`) with P6/P7/P8/OSB and the pin steps
(`storage.syncDir`), `raft-restart-confpoint` (option D), `d6t4b` (T4), T7/P5/P6b. The etcd pin is `lean`'s
(`df6af0c36`). No file was taken from the crash line alone.

**What the merges needed** (each file's round-3 version taken only where no crash-line commit touched it,
with `lean`'s changes since `676aede0a1` applied on top; every file that differs from round 3's tree was
classified so):
- **http.reserve**: `lean`'s `httpAddrNet` (round 2's resolution): `Spec/net/Listen`, `Proof/net/{InvNet,Listen}`,
  `http/{Axioms,ListenerClose}`, rafthttp's `TransportState`, etcdstart's `Alloc*`/`StartRes`/`Serve`,
  cluster3's `StartBridge`/`StartMember`, `runtime/Start`; `http-reserve-pend.md` superseded.
- **dist statements**: lit's, with `lean`'s `EtcdVerifyOff` (round 3); the Spec header without the crash line's
  W1 restriction (the fs extension's crash is "unrestricted" here, as on `lean`); the Proof skeleton without the
  crash form (`EtcdBootC`, `EtcdBootCBad`, `etcd_safe_of_boot`, `NetExtsCrash`). `etcd_robust.spec` stays a
  statement only (no proof on this line).
- **BootBad**: round 3's (no `Hctx`: ctx-leaf-fix's `ContextReadErrs.errs`), without `crashBootBad_of_wp`,
  `etcdBootCBad_holds`, `etcd_safe_of_bootWF`; `etcd_safe_nocrash_of_bootWF` kept.
- **membership**: `lean`'s claim #34 specs keep the plain names, D2's one-URL specs are `.specOne` (round 1),
  with deployment's `IdsOk`/`memberIDs`/`WellFormed`, its `Link` and link list.
- **putgetK on `lean`** (rounds 1, 3): hprem-axioms' wire swap, the client's `AddrOk`, `EtcdVerifyOff`, no
  `Hctx`/`Hcec`, `levelTok 0`; `NewServer_dist`/`StartMember_dist`'s pre as `specG`'s; `BootBridge` over
  `ccAddOk`; `tier-linking` lists `putgetk.Start`.
- **Generated/tooling**: gen-init (Net's stale copy of `lib/remote`'s `Init` removed, Dsverify's three `Base`
  imports repointed: round 3's L1), gen-specs-pkginit's `NET_PART` (`lib/remote`), `proof_roots`' part-Net
  split, goose's `putgetk-dist` project; bounds-allow for the dist member specs (round 2's lines without
  `NewServerCrash`/`NewServerRAt`).
- **Kept `lean`'s, not round 3's**: tracecheck (its `Hprem`: round 3's swap came from merging `hprem-axioms`
  directly), `NewRaftLoggerZap` (one spec, no `specNN`), `copy-part`, the premise witnesses (round 3's
  `FsInit` edits followed the crash line's `etcdFsSem`), the dist bridges (no duplicate here).
- **bootax**: the iris-premise baseline is `lean`'s (no `putget_safe`/`putgetK_safe` `Hprem` line); the
  premise-witness baseline gains the `putgetK_safe` line.

**Checked:** goose `--check` (projects etcd, putget-dist, putgetk-dist), gen-init, gen-specs-pkginit, gen-raft-tla,
copy-part, tier (208 known), bounds (390), api (6 configs), iris-premise, premise-witness, issues index; full VM
build green at `6ae57b8e7c` (28948 jobs, first try); every `Link` regenerated on the VM matches (61), btree's
too. Through `vmlake env`: `tcb-report --check` matches the baseline unchanged (364 axioms, 0 `sorry`, `lean`'s),
and every collection matches (bootax's collections included; it added none). `etc/tcb-collections/etcd-dist.txt`
(roots: the dist `TopLevelRobustness`): empty baseline (2 roots, 0 axioms, 0 `sorry`). bootax's Go evidence
(`examples/axiomcx/bootstrapdist`, run at `e94f33b50` on its branch) passes 5/5 at this line's pin `df6af0c36`.

**Trust-base diff against `lean`** (declared axioms; none is reached by a root yet, so the reported trust base is
`lean`'s): from lit, etcdhttp's generated `initFuncsOk`/`opaqueInitsOk` (D2's translation of `etcdhttp`); from
the transport branch, `NewServer_dist.wp_proof`, `PeerServe_dist.wp_proof`, `NewPeerHandler_dist.wp_proof`,
`os.Getenv.wp_proofEnv` (the proxy check) and the restated `membership.membersOf_decode` (route B's
`IsLearner`); from putgetk, none; from bootax, `bootstrap.wp_proof_dist`. No crash item (D4a/D4b/D4c',
`DistCrashAdequacy`, C-I1's `dbCrash*`, `BoltCrashWhole`, `szCrash`, snapDir changes, the pin's translation).
No new axiom, `sorry` or top-level premise beyond the merged branches'; no Go change of this line's own.

### 20.1 N2 ported (2026-11-25, branch `etcd-safe-nc-n2/2026-11-25`)

§18's O1/N2 work (option B: `Γ : DistView`, `etcdSvc`/`etcdAddrAt`/`Serve_dist` at the view, no publication,
`Client_Put/Get_dist` theorems from the interim axioms `KV_Put/Get_dist`) on this line. Its eleven commits
(`5a1c41d945..etcd-safe-n2/2026-11-25` @ `b5f215386a`) were on `etcd-safe-main-r3`, so they were cherry-picked
(`-x`), in order, onto `etcd-safe-nc/2026-11-25` @ `a9d9b94558`, and the conflicts resolved there; one commit
of this line's own regenerates `SpecPlan`'s `PkgInit` of `dist/client` (`gen-specs-pkginit`, after the
`newUserClient` change).

**Conflicts and resolutions** (both sides kept: this line's bootax port and `lean`'s putget changes, and N2's
re-indexing and removal of the publication):
- `Spec`/`Proof` `ClientPutDist`/`ClientGetDist`: N2's (the theorems and their new statements). This line's
  only change to them was `levelTok 0` in the axioms' pre and post, which N2's statements already carry.
- putget `AdequacyMember`: bootax's `premises_holds … Hfips Hbg` (no `Hprem`), without the publication's
  `memberPubOk_putgetPub`; putget `TopLevelRobustness`: `member_boot … Hbg Hfips σm Hm c`; `AdequacyClient`:
  this line's `Hl0` token name at N2's `client Γ mid`; `Spec`/`Proof` putget `Client`: N2's (`Hauth`, the
  token threaded), one-line binder header.
- putgetk `Member`/`AdequacyMember`/`Start`: N2's (no `Pub`, the view `c.view`/`DistView.ofKV γk0`) with
  bootax's `Hbgo` in place of `Hprem` and `bootstrap.wp_proof_dist` passed to `Member.wp_proof`.
- `dist/client/PkgTable` (generated): `etc/gen-init.py` rerun; notes: §18 placed before §20.
- The final tree equals the three-way merge of r3, this line and N2's head in every N2-touched file but these
  hunks. No N2 change needed a crash-line-only definition: the changed modules and their importers built
  unmodified. No interim axiom's statement differs from N2's reviewed one (`notes/axiom-review/n2-kv-dist.md`).
- N2's Go change (`dist/client/auth.go`: `newUserClient` with `grpc.WithNoProxy()`, §18.8 item 4) comes with
  it; `goose.py --check --project putget-dist` passes at this line's pin.

**Checked:** gen-init, gen-specs-pkginit, gen-raft-tla, gen-rpcdriver-boottable `--check`; tier (208 known), bounds
(390), iris-premise (16, all listed), premise-witness (47 statements); VM build of the changed modules' importers
(13492 jobs), then the full build (28959 jobs), both first try; every `Link` regenerated on the VM matches (61), btree's
too. Through `vmlake env`: `tcb-report --check` matches (364 axioms, 0 `sorry`) and every collection matches. The
baseline change is exactly N2's: `etc/tcb-baseline.txt` and `putget-dist.txt` gain `etcd_dist.KV_Put_dist.wp_proof`
and `etcd_dist.KV_Get_dist.wp_proof` and lose `etcd_dist.Client_Put_dist.wp_proof` and
`etcd_dist.Client_Get_dist.wp_proof`. `KV_Delete_dist`, `KV_Compact_dist` and `Txn_Commit_dist` are declared, but no
root reaches them yet (M1's Node will). No new axiom beyond N2's reviewed ones, no `sorry`, no new top-level premise.
## 19. N5: the member machine's boot, `server.MainDeployment(d, i)` (2026-11-25, branch `etcd-safe-n5/2026-11-25`)

From `etcd-safe-bootax/2026-11-25` @ `c14f88dec2`. First stopped on the interim peer transport's index (below);
the coordinator decided the fix (2026-11-25): **index by the cluster**, done (see "Done" at the end of this section).

**The blocker: `httpAddrAt` is indexed by the member's whole `SrvRaft`, which holds its own storage registry.**
`httpAddrAt γ id a := addrProto a (httpPeerSvc γ id).1 (httpPeerSvc γ id).2` (`S5Interim.lean`), `httpPeerSvc`
opaque, indexed by the whole `SrvRaft γ` since the 2026-11-24 re-review's hardening (§17.3: "indexed by the whole
`SrvRaft` `γ`, not only `γ.cl`"). But the `γ` a member's `NewServer` runs at is per member: `memberBoot_of_slice`
gives `memberBoot { c.γ with reg := c.reg id }` (`etcdstart/AllocN.lean`), because `NewServer` owns its storage
registry's authority (`ghostMapAuth γ.reg 1 ∅`, `memberSlice`; `MemStorReg := ⟨γ.reg⟩`), so two members' `γ`s
differ in `reg`. The three texts that read `httpAddrAt` all take it at the reading member's `γ`:
- `NewServer_dist`'s `#Hpeers`: `httpAddrAt γ_A pid a` for every other peer `pid` of member `A`;
- `bootstrap.wp_proof_dist`'s `bootRTOk γ id dir` (through `bootPremiseDist`, whose `γ` carries
  `MemStorReg := ⟨γ.reg⟩`): the same, at `γ_A`;
- `PeerServe_dist`: `httpAddrAt γ id pa` at a `γ` with `γn.N = srvNet γ`.
At three members `A`, `B`, `C`, `B`'s address `b` must then carry `httpPeerSvc γ_A B` (for `A`'s `NewServer`) and
`httpPeerSvc γ_C B` (for `C`'s); an address is set once (`addr_set_proto` spends `addrUnset b`), and two
applications of the opaque `httpPeerSvc` to different records are not provably equal, so no start can give both.
(One member: `Hpeers` and `bootRTOk` are vacuous but `noProxyEnv`; two: only if `srvNet` does not read `reg`.)
`etcdClusterStart`'s `memberStartShare` is still over `S5Draft`'s unindexed `httpAddrAt`, so no share was ever
built at the indexed one, which is why this did not surface.

**Proposed fix** (a change to the interim axioms' trusted vocabulary, for the owner): index the peer protocols by the
cluster, not the member's whole record: `httpAddrAt γ id a := addrProto a (httpPeerSvc γ.cl id).1 (…).2`, with
`httpPeerSvc` taking the `Cluster` (the re-reviewed form before the hardening; `γ.cl` is allocated once per cluster,
so the review's counterexample, a second ghost cluster with the same ids, stays excluded). The axioms' statements
(`NewServer_dist`, `PeerServe_dist`, `bootstrap.wp_proof_dist`) are unchanged as text; `httpAddrAt γ_A pid a` and
`httpAddrAt γ_C pid a` become the same proposition. Alternative: keep the record but erase `reg`
(`httpPeerSvc { γ with reg := default } id`). Either wants the axiom skill's re-review of `NewServer_dist`.

**What N5 needs besides, found on the way (none blocks):**
- The Go refactor is still needed: `Serve_dist` is about `etcdstart.Serve`, and `MainLogger` inlines its body
  (`v3rpc.Server`, `net.Listen`, `go gs.Serve`). `if etcdstart.Serve(s, c.Client) != nil { return }` after
  `<-s.ReadyNotify()` keeps the order (serving after ready); the package doc's sentence on not using it goes.
- `ReadyNotify` is called before serving, so it needs a spec: `return s.readych`, whose channel `srvReadyCh` (in
  `srvReadyCloser`, `InvMonitors.lean`) is an `ownBroadcastChan rdc γ True .Pending` that `Start` hands to
  `publishV3`. Before `Start`, split off the read-only field and the broadcast idiom's persistent receiver part;
  the receive then blocks until `publishV3` closes it (post `True`).
- `wp_Start_built` drops `memberBuilt`'s `memberPeerServeRes` (`-`); `MainLogger` serves the peer handler after
  `Start`, so it needs `memberBuilt … false ⊢ memberBuilt … true ∗ (httpProcSlots × srvServeRes γn τ) ∗
  □ srvNetMember γn s id τ` before `Start`. `NewServer_dist`'s post must also be turned into `memberBuilt` (the
  single-process `etcdstart.newServer` proof does this for `NewServer.spec`; `putgetk` never did, its
  `StartMember_dist` being a named hypothesis).
- Bounds: `etcdSteps = 2 ^ 48` fits (`N = 2 ^ 48 - 1`: `N + 7 + bootWB ≤ backend.wbInit = 2 ^ 62 - 1`).

**Done (2026-11-25, same branch).**
- **The cluster index** (`149d218c5d`): `httpPeerSvc (cl : Cluster) (id : w64)`, `httpAddrAt γ id a := addrProto a
  (httpPeerSvc γ.cl id).1 (…).2` (`S5Interim.lean`, the two declarations and their docstrings, and the header's
  mention); the axioms' statements word for word unchanged. Fresh `axiom`-skill re-review of `NewServer_dist`,
  `PeerServe_dist`, `NewPeerHandler_dist` and `bootstrap.wp_proof_dist`'s `bootRTOk` together:
  **all survive** (`notes/axiom-review/s5-cluster-index.md`; Go evidence: strangers answered by a real three-member
  cluster's `/members` boot or get "already bootstrapped", no panic); its docstring changes D1-D6 applied.
- **Go program changes** (for the no-crash packet; `go test ./etcd/dist/ ./etcd/dist/server/` pass, `TestDist`
  needs root, not run):
  - `MainLogger` serves clients with `etcdstart.Serve(s, c.Client)` after `<-s.ReadyNotify()` (its inline body,
    `Serve_dist`'s subject); the package doc's sentence on not using it gone.
  - `deployment.WellFormed` bounds member names by `MaxNameLen = 200` (Lean `typed.maxNameLen`; addresses and the
    token stay at `MaxLen = 255`): the member's data directory `<name>.etcd` and its WAL area's paths must fit in
    a path component, and the proof's bound (`dirFits_memberDataDir`, `wp_walAreas`) is 200. **Names of 201-255
    bytes are now refused by the check, so those machines return at once.** `TestWellFormed`: 200 accepted, 201
    refused. `Deployment.WellFormed.members` gives the members' facts.
- **Translated**: `EtcdServer.ReadyNotify` (`etcdserver.toml`).
- **Specs** (`Spec/.../dist/server/`, namespace `etcd_dist.server`): `MainDeployment.spec`,
  `MainDeploymentLogger.spec` (from `deploymentRepr`, the machine's fresh WAL area and `⌜d.WellFormed⌝ -∗` member
  `i`'s share), `MainLogger.spec` (at `configRepr` and the share), `ConfigOf.spec`, `serverConfig.spec`
  (`memberCfg`), `inCluster.spec`, `proxyEnvSet.spec` (`false` gives `noProxyEnv`), `holdForever.spec`; and
  `EtcdServer.ReadyNotify.spec` (from `srvReadyRecv`, `ReadyRecv.lean`), `net.Listen.specProto` (a listener at an
  `addrProto` address). Vocabulary: `dist/server/MemberDefs.lean` (`memberShareD`: putgetK's `memberShareK` at the
  deployment's members with `peerAddrFactsAt`, the indexed peer facts; `BootGoD`: putgetK's `BootGoK` plus the
  peers' permutation, which `BootFacts` lacks). Scope premise of the specs: `d.cfg.auth = false` (`Serve_dist`
  serves a member with auth off).
- **For `EtcdBootNC`'s discharge** (not N5's): `BootGoD d ps ctxs` is a hypothesis of the member boot that
  `EtcdBootNC`'s `BootPremises` does not give (`BootFacts` has neither the permutation nor Go's values at the
  members' URLs: putgetK takes `BootGoK` as a top-level premise); auth deployments need `Serve_dist`'s auth-on form;
  the start must produce `memberShareD` (`etcdClusterStart` at `peerAddrFactsAt`).

**On `etcd-safe-n5/2026-11-25` (head `d2c8f9a7cd`, built on the VM):** every N5 proof, and `member_boot_dist`
(`dist/server/AdequacyMember.lean`): `Net.DistBootWpSLT etcdThreads 0 etcdSteps (serverProg d i) σ (∃ c γE,
memberShareD c d ps ctxs boot i γE Pub)` at a well-formed `d`, hypotheses `Hauth : d.cfg.auth = false` and
`BootGoD d ps ctxs` beyond `EtcdBootNC`'s premises; every proof and interim axiom plugged in. Leaf proofs and
`MainLogger` by helpers (A, B). bounds: `MemberSplit`'s hand-off of the HTTP stock allowed (`etc/bounds-allow.txt`).
No `Link` entry: the linking is the manual `AdequacyMember` module, as putgetK's.

**Port (2026-11-25), branch `etcd-safe-nc-n5/2026-11-25`** from `etcd-safe-nc-n2/2026-11-25` @ `b35f8f67ca` (the
no-crash line with N2): N5's commits cherry-picked (`-x`); the generated files regenerated at this line's pins (the
server translation, `dist/server`'s Init/PkgTable, SpecPlan's PkgInit; `ReadyNotify`'s translation at the etcd pin
`df6af0c36`); `bounds-allow` without the crash line's `NewServerRAt` entry. Done on this branch (built on the VM, 11272 jobs: `server.AdequacyMember`, `dist.TopLevelRobustness` (Spec and
Proof), `BootBad`, `BootFactsSat`, `deployment.Link`, `putgetk.Start`; tier, bounds, premise-witness, gen-init
checks pass):
- **Γ** (helper C): `memberShareD c d ps ctxs boot i` without the publication: its client fact is
  `etcdAddrAt (member i's client) c.view (member i's id)` (N2's `memberStartShare`), `Serve_dist` at `Γ = c.view`
  with `kvCongr ρ.rd.kv c.view.kv` from `memberBoot_of_slice`; the specs take `BootCore ps ctxs boot`.
- **`member_boot_dist`** (`dist/server/AdequacyMember.lean`), the name and form M1's start takes:
  `Net.DistBootWpSLT etcdThreads 0 etcdSteps (serverProg d i) σ (∃ c, memberShareD c d (distPs d) (distCtxs d) boot i)`
  at `Hd : d.WellFormed`, `Hbf : BootFacts d boot`, `EtcdEnv d`, `EtcdVerifyOff`, `GodebugFips140Off`,
  `d.members[i]? = some m`, `ServerStart m σ`, and **one hypothesis beyond `EtcdBootNC`'s premises:
  `Hauth : d.cfg.auth = false`** (M1's scope; the full theorem needs `Serve_dist`'s auth-on form, N11).

**Packet items (the no-crash packet), Go program and statement changes of N5:**
- Go: `MainLogger` calls `etcdstart.Serve(s, c.Client)` after `<-s.ReadyNotify()` (its inline body before).
- Go: `deployment.WellFormed` bounds member names by `MaxNameLen = 200`: names of 201-255 bytes are now refused,
  so those machines return at once.
- Go: `deployment.WellFormed` refuses a member whose computed id is `MaxUint64` or `MaxUint64 − 1` (`RaftIdOk`;
  raft v3.7's `Config.validate` refuses them, `StartNode` panics). Typed `WellFormed` mirrors it;
  `TestWellFormed` tests `RaftIdOk` on crafted ids (a refusing deployment needs a SHA-1 preimage).
- **BootFacts: ps/ctxs pinned to Go's computed values (they were free).** Old text (`etcd_robust_nocrash.spec`,
  and the same in `etcd_robust.spec`):
  ```
      (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (Hbf : BootFacts d ps ctxs boot)
  ```
  with `structure BootFacts (d) (ps) (ctxs) (boot) : Prop extends BootCore ps ctxs boot where perm : ps.Perm d.ids`.
  New text:
  ```
      (boot : List LogEntry) (Hbf : BootFacts d boot)
  ```
  with (`TopLevelDefs.lean`) `abbrev BootFacts (d) (boot) : Prop := BootCore (distPs d) (distCtxs d) boot`,
  `distPs d := bootGo.ps (distURLs d) d.token`, `distCtxs d := bootGo.ctxs (distURLs d) d.token`, `distURLs d` the
  deployment's initial cluster (each name to its one peer URL `http://peer`). `EtcdBootNC`'s `BootPremises` is
  `∃ boot, BootFacts d boot ∧ …`. Compiled witness of the remaining `BootFacts`: `BootFacts.sat : ∃ d boot,
  d.WellFormed ∧ BootFacts d boot` (`BootFactsSat.lean`, a one-member deployment); the dist statements stay `* draft`
  in the premise-witness baseline (their other premises have no witness yet).


## 21. M1 assembly (2026-11-25, branch `etcd-safe-m1-top/2026-11-25`; the etcd_safe lead's helper)

**Needs `KvDefs` (N7-kv) to build.** `KvOnly` is in N7-kv's `Proof/.../dist/client/KvDefs.lean`, which is not on this
base. The branch builds once it is rebased onto etcd-grove-03's `etcd-safe-m1`, which carries N7-kv.

**Scope.** This branch has M1's statement, its skeleton, the premise witness and the collection root. It
starts from `etcd-safe-nc-n2/2026-11-25` @ `b35f8f67ca`. etcd-grove-03 does §11.3 steps 1-5 on their
branch `etcd-safe-m1`: the merge of `etcd-safe-p9-nc`, the port of `kvremote/Start.lean` to Γ,
`wp_Node`'s hypotheses, and N7-kv's replay with its instance lemmas. This branch goes onto their head when
they post it. It touches none of their files.

**Done (local commit `bf30d11ac5`).**
- **The statement**: `Spec/.../dist/kvremote/TopLevelRobustness.lean`, `etcd_kv_safe_nocrash.spec`. Its
  binders are `etcd_robust_nocrash.spec`'s, in the same order and over the same `TopLevelDefs`
  definitions, plus `Hscope : KvOnly d ∧ d.cfg.auth = false` after `d`. `KvOnly` is N7-kv's
  (`client/KvDefs.lean`: `∀ w ∈ d.workloads, w.kind = W64 0`). The statement is in `kvremote/`, not beside
  `etcd_robust_nocrash.spec`, for two reasons:
  - Spec and Proof stay paired by path (CLAUDE.md, "Layout"), and the premise-witness script pairs
    `kvremote/TopLevelWitness.lean` with it;
  - the shared dist Spec file, which N5's port edits (`BootFacts` pinned), is left alone.
- **Inheriting N5's change.** `etcd_kv_safe_nocrash_of_full : etcd_robust_nocrash.spec →
  etcd_kv_safe_nocrash.spec` (Proof) applies the full statement to M1's arguments. Once N5 changes the
  full statement's `BootFacts` binders, this theorem stops compiling until M1's binders get the same edit
  (`(ps) (ctxs)` dropped, `BootFacts d boot`). So M1 cannot silently diverge. A statement written as
  M1's "body by reference" would need the full statement refactored into a per-deployment definition,
  which is a change to the shared trusted file. Not done.
- **The skeleton** (`Proof/.../dist/kvremote/TopLevelRobustness.lean`, linking):
  - `EtcdKvBootNC` is `EtcdBootNC` with the scope as one more hypothesis.
  - `etcd_kv_safe_nocrash_of_boot (HS : EtcdKvBootNC) : etcd_kv_safe_nocrash.spec` uses
    `etcd_safe_nocrash_of_boot`'s bridge. The malformed case comes from `etcdBootNCBad_holds`.
  - It reuses `BootPremises` by name, so N5's change to it carries over.
  - No axiom, no `sorry`.
- **The witness**: `Proof/.../dist/PremiseWitness.lean` holds per-premise lemmas, shared with P12 (#50).
  - `witnessMember` and `witnessToken` are `putget_safe`'s witness member `putgetd`.
  - `witnessMember_id` proves `memberId … = pgId`, evaluated by the kernel.
  - `bootFacts_witness d hm ht` gives `BootFacts` at `[pgId] [pgCtx] pgBoot` for any deployment of that
    member alone.
  - `serverStart_witness` and `clientStart_witness` give the start states (`witnessMemberσ`,
    `witnessClientσ`).
  - `kvremote/TopLevelWitness.lean` proves `etcd_kv_safe_nocrash.premisesSat`. Its deployment
    `kvDeployment` has that member, auth off, and one `kv` workload with one client machine. It leaves
    out only the opaque `Henv`, `HEnv` and `Hfips` (three baseline lines).
  - `bootFacts_witness` is at the current `BootFacts`. After N5's pinning it must show `BootCore` at
    `distPs`/`distCtxs` (`bootGo.ps`/`bootGo.ctxs`; `putget`'s `pgBootGo` computes those for this member).
- **Collection**: `etc/tcb-collections/etcd-dist.txt` gains the root `kvremote/TopLevelRobustness`.

**Checked** (VM, with N7-kv's `KvDefs.lean` copied in untracked, since it is not on this base): the four modules
(the Spec statement, `dist/PremiseWitness`, `kvremote/TopLevelWitness`, `kvremote/TopLevelRobustness`) built on the
first try (5092 jobs); `premise-witness --check` (48 statements) and `tier-check --check` pass. `#print axioms`:
- `etcd_kv_safe_nocrash_of_full` and `etcd_kv_safe_nocrash.premisesSat`: only `propext`, `Classical.choice` and
  `Quot.sound`;
- `etcd_kv_safe_nocrash_of_boot`: 36 of this repository's axioms, all through `etcdBootNCBad_holds`'s package
  initializers. All are in `etc/tcb-baseline.txt` except etcdhttp's generated `initFuncsOk`/`opaqueInitsOk`,
  which are declared on this line but reached by no root before this one (§20). They enter
  `etc/tcb-baseline.txt` and `etcd-dist.txt` at the `--check --update` after the full build.

**Left: `EtcdKvBootNC`'s discharge** (once etcd-grove-03's head is posted).
- The start:
  - `netProto_alloc`;
  - the members' part of the cluster's start (P9's `member_boot_dist.law` in `Start.lean`, a hypothesis
    there; `etcdClusterStart` at `peerAddrFactsAt`, producing N5's `memberShareD`);
  - `kv_start_deployment` (its `hb` from `kvOnly_bounds`/`BoundsOk`; `d.workloads = [w]` from `KvOnly` and
    `Compatible`'s distinct kinds; the case with no workload separately).
- The boot WPs:
  - members: N5's `member_boot_dist`;
  - orchestrators: N7-kv's `wp_OrchestratorKv` at `kvOrchPre`, with the machine's initialization as in
    `BootBad.clientBadWp`;
  - client machines: `wp_NodeDeploymentKv` at `kvNodePre`, `levelTok 0` from `threadTok_level0` as in
    putgetK's `client_bootK`.
- **A shape issue for the shares.** `DistBootWpSLT`'s share `P` is stated at `[GooseGlobalGS]` only, before
  the machine's `HeapGS` exists. But `kvOrchPre`, `kvNodePre` and `orchShare`/`nodeShare` are defined under
  `[hG : HeapGS]`, even though `kvOrchPre` reads only `hG.goose_globalGS`. Two fixes:
  - (a) state them at `[Gg : GooseGlobalGS]`, a change to etcd-grove-03's files, which N5's `memberShareD`
    already follows;
  - (b) give the shares here as their global parts, and rebuild `kvOrchPre`/`kvNodePre` inside the boot
    lemma at the machine's `hG` (`levelTok 0` is machine-local anyway).

### 21.1 Checkpoint (2026-11-25 ~23:30Z, head `ecbdc08ef2` + this note)

**Merged into this branch:** `etcd-safe-nc-n5/2026-11-25` @ `69f9417d8b` (N5: `member_boot_dist`, `BootFacts`
pinned), `etcd-safe-p12/2026-11-25` @ `758571cd38` (P12's per-premise lemmas, already reconciled with this
branch's `PremiseWitness` names) and etcd-grove-03's `etcd-safe-m1` @ `21db702041` (P9 on the line, `Start.lean`
ported to Γ). One conflict, in the notes: both appended sections are kept.

**Done since §21:**
- M1's statement now has the pinned binders, `(boot) (Hbf : BootFacts d boot)`; `_of_full` and `_of_boot`
  follow them.
- `bootFacts_witness d hm ht : BootFacts d pgBoot` is now proved from N5's `satD_ps`/`satD_ctxs`. This works
  because `distPs`/`distCtxs` read only the members and the token, so there is one computation of Go's peers and
  contexts. `witnessMember_id` is dropped, since it duplicated `satD_ids`. P12's `witnessDeployment_boot`, its
  `etcd_robust(_nocrash).premisesSat` and M1's witness are updated to the new arity.
- `kvMemberBoot`: EtcdKvBootNC's member part, N5's `member_boot_dist` at `σs[i]`. Its share is
  `∃ c, memberShareD c d (distPs d) (distCtxs d) boot i`.
- The baseline header's broken `etc/premise-py` is restored to `etc/premise-witness.py`.

**VM build** (`BootFactsSat`, `PremiseWitness`, `dist/TopLevelWitness`, `server/AdequacyMember`,
`kvremote/Start`, `kvremote/Link`):
- built: everything but `kvremote/Link`, including the pinned witnesses, `AdequacyMember` and `Start`;
- **failed: etcd-grove-03's `kvremote/CallDist.lean`** at `21db702041`. Six errors "typeclass instance
  problem is stuck: `go_etcd_io.etcd.client.v3.Assumptions`" (lines 69, 175, 259, 322, 391, 785), from their
  port. That is their file, so it is left to them.
- `kvremote/TopLevelRobustness` and `kvremote/TopLevelWitness` wait for `KvDefs` (`etcd-safe-n7kv-nc2`).

**Next, in order:**
1. When `etcd-safe-n7kv-nc2` and a fixed `etcd-safe-m1` are pushed: merge both, then build the kvremote
   M1 modules.
2. **The members' start** (the alignment of `Start.lean`'s `member_boot_dist.law`, ours to do). Instantiate
   `MS Γ := ∃ c, ⌜c.view = Γ⌝ ∗ [∗list] i ↦ _ ∈ d.members, memberShareD c d (distPs d) (distCtxs d) boot i`,
   with `boot` a new parameter of the law. Then prove the law, which nobody has proved yet. It is a variant of
   `etcdClusterStart` at N5's indexed peer facts:
   - `clusterAllocN` first, then `S5Interim.http_addr_set` at `c.γ` for every peer address, then
     `members_svc_start`'s client part at `c.view`;
   - `clusterMembersOf d = cmsD d`, by `List.zip`/`map`;
   - `(kvR c.γk).sysState init` from the lease-mode-`none` `etcdKV c.γk (kvModelSt c.γk (bootEntries …))`.
     This needs `GoodKV`, `absSt = init` and `kvGood` of the boot state (`InvBuild.kvModelSt_boot`).
   Either a new defs module beside `Start.lean`, or `Start.lean` itself (allowed for the alignment).
3. **Shares at `GooseGlobalGS`** (option (b), with etcd-grove-03's files untouched). Use putget's pattern,
   `∀ L, X (hG := heapAt G L lctx)` (`putget/Defs.lean`'s `clientShare`). The start's updates (`kv_start`,
   `kv_start_deployment`) are stated under `[hG : HeapGS]`, so running them at the start needs some local
   state `L₀`. A probe is checking whether `GooseLocalGS GF` is inhabited. If it is not, (b) does not work
   and etcd-grove-03 must restate `kvOrchPre`/`kvNodePre`/`kv_start` at `[Gg : GooseGlobalGS]` (option (a)).
4. The orchestrators' and client machines' boot WPs: `BootBad.clientBadWp`'s initialization, then
   `wp_OrchestratorKv kvOrchPre` / `wp_NodeDeploymentKv kvNodePre`. `levelTok 0` comes from
   `threadTok_level0`, and `Orch.spec → Orch.specWith` is a timeout specialization.
5. `EtcdKvBootNC` from steps 2-4 (`netProto_alloc`, the empty-workload case separately), then
   `etcd_kv_safe_nocrash := etcd_kv_safe_nocrash_of_boot …`. Then the full VM build, the gates and
   `tcb-report --check --update` (etcdhttp's two init axioms enter the baselines).

**Probe result (step 3).** `GooseLocalGS GF` is a class with six fields:
- the extensions' `Exts.LocalGS`;
- `goose_go_local_context`;
- `NaHeapGS Loc val GF`;
- `GoStateGS GF`;
- `ThreadGS GF`;
- `CrashGS GF`.

These carry the functors' inclusions, not only names. So it has no `default`, and `Nonempty` is not
automatic. An `L₀` for `etcdDistGF` could still be put together by hand: `etcdDistGF_gooseGpreS` supplies the
inclusions, and any names will do. But every `kvOrchPre`/`kvR` reading only `hG.goose_globalGS` would then
have to be checked defeq across `L`s. Option (a) avoids both: etcd-grove-03 restates `kvOrchPre`, `kvNodePre`,
`kvR`, `kv_start` and `kv_start_deployment` at `[Gg : GooseGlobalGS]`, as N5's `memberShareD` is.

### 21.2 Session 2 (2026-11-26, from `5a3055d5dc`): (A) to (D), `etcd_kv_safe_nocrash` proved

**Merged:** etcd-grove-03's `etcd-safe-m1` @ `9e1045a209`, which brings the CallDist fix, the shares at
`[Gg : GooseGlobalGS]` (option (a): `kvR`, `kvOrchPre` over `linkvtxnSG`, `kvNodePre` global plus a local
`kvNodePreL`, `Start.lean`) and `[GoLocalContext]` at those sections. Also N7-kv's replays `etcd-safe-n7kv-nc`
@ `6ffd1b9527` and `etcd-safe-n7kv-nc2` @ `5f2923d14d`. Their Proof and Spec files are identical; the one
conflict, in the notes file `etcd-dist-n7kv.md`, was resolved by keeping theirs.

**A statement-adjacent file changed: `dist/TopLevelDefs.lean`'s `etcdDistGF`.** It gains slot 8, iris-lean's
non-atomic invariants (`NaInvF`), and the instance `etcdDistGF_naInvG`, because P9's `kvremote.wp_Orch` takes
`[NaInvG GF]` (porcupine's results). This is not a statement change: no Spec statement mentions `etcdDistGF`
(checked by grep), and since 2026-11-25 it is the proofs' ghost state only.

**Written (step numbers as in §21.1):**
- **(A), step 2: the members' start.**
  - `server/ClusterStartD.lean`, `clusterStartD`:
    1. `clusterAllocN` at `distPs`/`distCtxs`, lease mode `none`, with the compactor slot from the deployment
       (`compactorCfg_of_wf`);
    2. every peer address set to `httpAddrAt c.γ` (`peersAt_start`);
    3. every client address set to `etcdAddrAt … c.view` (`clientsAt_start`);
    4. each member's `memberShareD` (`memberShares_of`).

    It returns `c.γk.log0 = [[], []]`, the client's `etcdKV` at the boot state and `clientSvcFacts (cmsD d) c.view`.
    It needs only `receiptBound ≤ 2 ^ 60`.
  - `kvremote/MembersStart.lean`: the law proved, `member_boot_dist_law : member_boot_dist.law d
    (membersShareKv d boot)`. `kvSys_boot` turns the boot `etcdKV` into `(kvR γk).sysState (kvR γk).B.init`;
    `clusterMembersOf_eq` shows `clusterMembersOf d = cmsD d`.
- **(C), step 4: the client-side boots,** `kvremote/AdequacyClient.lean`.
  - `kvOrchBoot`: the orchestrator boots from `kvOrchPre (ρ := ρ) ns w.ops`, through `wp_OrchestratorKv` with
    `Orch.specWith` from `kvremote.wp_Orch` (the timeout specialized).
  - `kvNodeBoot`: a client machine boots from `kvNodePre (ρ := ρ) (W64 c) a (rotateL clients c)`, through
    `wp_NodeDeploymentKv` at `kvNodePreL`. Its `levelTok 0` comes from `threadTok_level0`, and its thread bound
    from `hT`.
- **(D), step 5: the discharge,** in the Proof file `kvremote/TopLevelRobustness.lean`.
  - `kvOnly_shape`: no workload, or one `kv` workload together with `kv_start`'s bounds.
  - `kvShares`: the machines' shares.
  - `etcdKvBootNC_holds : EtcdKvBootNC`.
  - `theorem etcd_kv_safe_nocrash : etcd_kv_safe_nocrash.spec`.

**Also merged:** etcd-grove-03's `etcd-safe-m1` @ `11242953f7` and `etcd-safe-m1-fin` @ `e19748b443`, which carry
dsv-vr's `Kit`/`OrchProofDefs` for P9's `remote` and `KvDefs.kvOnly_bounds` by statement (theirs kept). The
`WellFormed` conjuncts of `compactorCfg_of_wf` and `kvOnly_shape` are also taken by statement (`grind`), not by
position. `etc/bounds-allow.txt` gains kvremote's two machine preconditions: `kvOrchPre`'s receipt bound and
`kvNodePreL`'s thread bound.

**Checkpoint (2026-11-26 ~01:40Z): green.**
- **Build:** the full VM build passes (`lake build`, 1189 s), as do the gen-link modes and `tier-check`,
  `premise-witness` and `bounds-check` (`--check`).
- **Trust base:** `tcb-report --check` passes at the updated `etc/tcb-baseline.txt` (373 axioms, 0 sorries).
  It gains 9 axioms, which no root reached before M1:
  - etcdhttp's `initFuncsOk` and `opaqueInitsOk`;
  - N2's `KV_Delete_dist` and `Txn_Commit_dist`;
  - N5's `NewServer_dist`, `NewPeerHandler_dist`, `PeerServe_dist`, `bootstrap.wp_proof_dist` and
    `os.Getenv.wp_proofEnv`. These are reached through `member_boot_dist`, whose `AdequacyMember` had no
    `Link` root.
- **etcd-dist collection:** passes at its first baseline (0 → 132 axioms).
- **`#print axioms etcd_kv_safe_nocrash`:** `propext`, `Classical.choice`, `Quot.sound` and the same 132
  repository axioms.
- **Not done:** the merge of `lean` and the landing; the lead decides.
