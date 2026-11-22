# `etcd_dist_safe`: etcd as a distributed deployment (plan, DRAFT for review)

2026-11-21. Branch `etcd-dist`. A draft for the user and upamanyus (etcd-grove#24): a plan, the
statement and its definitions, no proofs. Files:

- the statement: `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TopLevelRobustness.lean`
  (`etcd_dist_safe.spec`);
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
| D2 translation | goose projects for `server` and `client`; `Init`/`PkgTable`; the main tree's `net` becomes the part's | days | phase 7 S0, S4 |
| D3 mixed adequacy | the bridge from Perennial's `goose_dist_mixed_crash_adequacy` (exists) to `Robust crashing stable`, extending #22's `[netExt, fsExt]` bridge | smaller than ~1k lines | #22 |
| D4 bundle | `[net, fs at etcdFsSem, idIssue]` adequacy and crash interpretation; the issue record keyed by incarnation; shared-mode generations | ~1k lines | wal-safe (b) |
| D5 transport | phase 7 S1-S5 | 60-110k lines (option B's estimate) | upamanyus |
| D6 server | one `NewServer` spec for both starts; `walFoRes`; C6; the backend after a crash; `TrustBoundary` discharged | weeks | D4 |
| D7 cluster | global/local ghost split, the restart invariant | weeks | D6 |
| D8 clients (**Go done** 2026-11-22, §2 "Stage D8"; `remote` ported: `counter_remote_robust`) | (seams: §2, "Stage D1") port dsverify's `Remote` orchestration (`RunRemote`, `ServeClient`, `remoteDistSafe`) onto the net extension in `examples/lib/remote`, over `lintest`/`kvcheck` and the verified porcupine; each workload's client operations as `Remote` calls. Left: the Lean kv instance (blocked on D2's `net` and D7's one KV state; `opMaybe`'s read form done 2026-11-22), watch/cache/auth instances (over `Report`, proved 2026-11-22: §2, "`Report`, proved") | ~2k lines + the port | D1; Lean: D2, D7 |
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
