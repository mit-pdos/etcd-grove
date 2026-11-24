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
ids' issue record (`[HasExt Net.netExt] [HasExt Fs.fsExt] [HasExt idIssueExt]`), as `kvnetRobust`.

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
(proved: `Run` never returns `Illegal` when `apply` is logically atomic), and `examples/raft/kvnet/kvcheck` (#22)
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
- **`examples/lib/robust`** (shared with kvnet's driver, additive): the **bridge variant** of the
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
| harness `addrOk` | `kvnet.AddrOk` | kvnet is a Go module of its own |
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
  - kvnet's claim #22 is building the crashing bridge for `[netExt, fsExt]` (`GooseLang/Ext/NetFs/Adequacy.lean`). **D3 extends that; coordinate on #22.**
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
global twin equal by `rfl` (kvnet's `kvFactsG`/`kvFacts_eq`, `KvNet/.../kvnet/TopStart.lean`). Twins cascade
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
| raft's cluster `γ.cl` with its bootstrap log: `isClusterU`, `clusterInv`, `rdPool` (with its time receipts), the budget, `isCommittedLogLb γ boot`; per voter `raftState γ.cl id init`, `nodeVacant γ.cl id` | `cluster_alloc_boot_impl_tr` | heap, **only because of `bootMarshal`** | a global `cluster_alloc_bootG` without `bootMarshal`, giving per voter `nodeBootG` (below) |
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
  law `nodeBootG ∗ bootMarshal ⊢ nodeBoot` (heap); `cluster_alloc_bootG` gives `nodeBootG`. kvnet never met
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
`cluster_alloc_bootG` and the law (raft API; interfaces, the `RaftTla`/`RaftNoAx`/`KvNet` copies regenerated;
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
bootMarshal vs ctxs bl ⊢ nodeBoot …` at a heap. Additive: no statement changed; `RaftTla`/`RaftNoAx`/`KvNet` copies
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
  `net`'s names), no axiom added. KvNet keeps its own `net` (`net=KvNet`) and never reaches the main tree's.
  `Net/` stops being closed to the main tree: `CLAUDE.md`'s layout and `Net/Code/net.toml`'s header say so.
- **Left after the swap, for kvremote**: (1) Net's own `net/http`, `net/textproto`, `net/rpc` (project
  `models-net`) still declare the main tree's names-only `Code/net/{http,textproto}`'s names until S5.
  clientv3's translation reaches neither, but txnlin's `Defs` reaches the main tree's (rafthttp, through
  the server): a `Net/` module importing txnlin must not reach models-net's modules (remote's closure
  reaches none today). (2) Net's copies of the main tree's initializers (gen-init's `NET_MAIN`: `os`,
  `syscall`, `internal/poll`, `io/fs`, `internal/syscall/unix`, porcupine, lintest and its two instances,
  and `PkgInitExt`) clash with the main tree's in a closure holding both remote's and clientv3's: they are
  retired, `Net/` importing the main tree's (step 5); `etc/copy-part.py --check` then checks that KvNet,
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
  part that copies what it imports (KvNet's way): the copy is every module reaching `Code.net`, 9,900. (b)
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
