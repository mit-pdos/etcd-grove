# k8s-dist: k8s_safe's program as a distributed deployment (Go)

2026-11-22, branch `k8s-dist` (the user's decision, kaashoek, 2026-11-22). The Kubernetes workloads
of `k8s_safe` (`examples/k8s/all`: the etcd3 store's partitioned workload and Kubernetes' compactor)
run against real etcd deployments of member machines, every Kubernetes component that is a client of
etcd on a machine of its own, the checks on orchestrator machines over Remote
(`examples/lib/remote`). Go only, as etcd-dist's stages D1 and D8 (`notes/etcd-dist-plan.md` §2);
no Lean. The in-process drivers (`examples/k8s/{etcd3,compactor,all}`) and their tests are unchanged:
`k8s_safe` is proved about them.

## The split

`examples/k8s/dist` (package `dist`, a Go module of its own) holds the driver of the deployment:
the orchestrator and client machine programs (`MainReady`, `NodeMain`) and the deployment
(`Deployment`, `WellFormed`, `RandomDeployment`); `dist_test.go` deploys it. Two etcd clusters, as
`k8s_all`'s two: the store's (`k1` members) and the compactor's (`k2`), each an etcd-dist deployment
with no etcd workload, its members etcd-dist's `server.Main` on machines of their own. Both clusters
have etcd's own compactor off and no auth, as the drivers' clusters (`WellFormed` checks it; the
snapshot settings are random, from etcd-dist's choices).

| Component | Machine(s) | Program |
|---|---|---|
| etcd members | one per member, `store-member-i`, `compactor-member-i` | etcd-dist's `server.Main` |
| the etcd3 store (Kubernetes' `storage/etcd3`, an API server's storage) | `store-node-a`, `a < Apiservers` | `StoreNode`: the driver's store (`etcd3.New` over a kubernetes client of its own, members from `a` on) and one `remote.Serve` per client `c` with `c mod Apiservers = a`, each call the driver's `call` (or `runWatch`) |
| the store's clients, history and checks | `orch-store` | `RunStore`: seeds, then the driver's `Check` with `apply` a `remote.Do` at client `c`'s address; porcupine against the driver's `Model`, then Kubernetes' checker (`realCheck`) on a failure-free history |
| the compactor's writer | `compactor-node-0` | `CompactorNode`: the driver's `writer` per call (`remote.Report`, not awaited) |
| API servers with their own compactor (`NewCompactor`) | `compactor-node-1..3` | `CompactorNode`: per call, the driver's `apiserver` loop without its comparisons (`Sample`: samples, `Stop`, the two reads), reported |
| the two API servers sharing the process's compactor (`StartCompactorPerEndpoint`) | `compactor-node-4` (one process: the sharing is per process) | the same, both storages at once |
| the compactor's checks | `orch-compactor` | `RunCompactor`: every API server called at once (`remote.Report`), `check`'s comparisons on each log (`CheckLog`), panicking with `check`'s messages |

`Apiservers` is random per deployment: one (the driver's shape: one store, all clients), one per
client (D8's kv shape), or between. Several API servers over one cluster are an HA control plane;
the driver's model does not assume one store (its histories are the cluster's).

**Not split.** The DaemonSet controller (`examples/k8s/daemonset`) runs over the model API server
(`daemonset/apimodel`), not over etcd, and is not in `k8s_all`'s program: no machine split applies
(an etcd-backed API server serving REST to a controller machine is a different program, not a split).
authz has no etcd either and is not in `k8s_all`: it stays in-process (its own theorem). There is no
cacher in the drivers (the store's watches are `storage/etcd3`'s own watches): the API server machines
carry them.

**The rules** (etcd-grove#24's, as etcd-dist's): a write gets one attempt (`remote.Do`; the
kubernetes client's own default retries, which the driver keeps, retry only after a refusal); a read
(Get, List, a watch) up to `remote.ReadTries`. A call without an answer is the driver's output of a
failed call: `Output{Err: EOther}` (a write pending, at any later time or never; a read constraining
nothing) or a failed watch, exactly what the driver's model already allows. A compactor API server
without an answer reports nothing, and nothing of it is checked (the driver's checks are each API
server's own). Faults start once both orchestrators have marked their set-up done (`ready`: the store
after its seeds and its API server machines answering; the compactor once its machines answer),
at most 3 minutes.

**The seams.** Store: the driver's `Apply` is split at its prophecy: the store call on the API server
(`storecopy.Serve`, `call`/`runWatch`), the cache bookkeeping (`tbl.put`, `putW`, `done`) on the
orchestrator (`storecopy.Record`, after the answer, before the return stamp, as `Apply`'s). The
output's `Raw` (the store's own answer, which only Kubernetes' checker reads, by `reflect.DeepEqual`)
crosses the wire in an encoding of the values the store returns (objects, lists, `StorageError`s,
the callbacks' errors, `StatusError`s, watch events); the API server checks that it decodes to a
value `DeepEqual` to the store's and otherwise flags it (`RawOK`), and the orchestrator then runs the
driver's model only, saying so. Compactor: `check` is split into `Sample` (the API server: every value
it reads) and `CheckLog` (the orchestrator: every comparison, in `check`'s order); `TestCheckLog`
exercises each panic.

## Copies

The drivers' model, seeds, generator, per-client cache and `check` are unexported, and the drivers
must not change, so the two packages are copied **whole and byte for byte**:
`examples/k8s/dist/storecopy/{k8setcd3,watch,realcheck}.go` (from `examples/k8s/etcd3`) and
`examples/k8s/dist/compactorcopy/compactor.go` (from `examples/k8s/compactor`); `TestVerbatim` fails
if a copy differs from its source or a source has no copy. Each copy has one added file, `export.go`:

| Added (in the copy) | Wraps | Why |
|---|---|---|
| `Seed`, `Seeded.Model`, `Seeded.NewCache`, `Seeded.RealCheck`, `FailureFree` | `seed`, `Model`, `newWCache`, `realCheck`, `failureFree` | the orchestrator's half of `Check` |
| `NewStoreOnly`, `SetFeatures` | `newStore` without `seed`; `noStreaming`, `watchList` | the API server's store; the orchestrator sets the same features |
| `Serve`, `Record` | `Apply` split at its prophecy | the API server's call; the orchestrator's cache |
| `IsWrite`, `Rejections` | `isWrite`; `errDeleteRejected`, `errUpdateRejected` | the codec |
| `Writer`, `NewOwn`, `NewShared`, `Servers`, `SharedServers`, `Writes` | `writer`; `apiserver`'s two constructors; the constants | the compactor's machines |
| `Sample`, `CheckLog`, `Log` | `check` (a modified copy: split in two, the same reads and comparisons) | its reads on the API server, its comparisons on the orchestrator |

Copied from etcd-dist into `examples/k8s/dist` (unexported there): `awaitCluster`, `awaitNodes`,
`rotate`, `connectRetry`, `reportAll` (its `dist/client`); `TestDist`'s re-run in a user namespace
and its per-round set-up (its `dist_test.go`). The runner's process start, set-up wait and fault
loop are written for two clusters (`dist_test.go`'s `run`), over etcd-dist's `Cluster` for the
members.

**etcd-dist, additive** (`examples/etcd/dist/run.go`):
`Cluster.RunFaults(machines, stop)` (the crasher, and one network nemesis over the caller's machines),
`Cluster.Fail`, `Cluster.Failed`. `examples/lib/remote` is unchanged. `etc/goose.py`: the module's
`GO_MOD_PINS` (etcd, raft, bbolt) and `CLIENT_GO_PINS` (k8s versions = `examples/k8s/etcd3`'s).

Departures from the drivers (none weakens a check): porcupine and Kubernetes' checker run with a
5-minute timeout (`CheckTimeout`; a timeout ends without a verdict, never a failure), where the
drivers have none; the compactor runs `Rounds` rounds of its API servers (the driver's one, repeated
with fresh compactors, a writer call per round), so that the faults meet it (one round takes about a
second).

## Running it

`cd examples/k8s/dist; GOTOOLCHAIN=go1.27.3 DIST_RUN=1 go test -run '^TestDist$' -v` (`-short`:
one small deployment; `DIST_ROUNDS` deployments otherwise, default 4; `DIST_OPS` the store clients'
operations; `DIST_ROUNDS_C` the compactor's rounds). Machines and faults are etcd-dist's: on this
machine (a container's root) the test re-runs itself in a user namespace (bridge variant): kills
with sync, partitions both ways and one way, isolations, link faults (delay, loss, duplication,
reordering); no power losses (no device mapper), no resets.

## Results

**2026-11-22, this machine** (a container's root: the bridge variant, kills with sync, no power
losses, no resets; three members per cluster; faults from about 2.5 s, once both set-ups were done).
Every run passed: no panic on any machine, no member exiting on its own, both orchestrators done.

| Run | Deployments | Store checked | Compactor checked | Faults |
|---|---|---|---|---|
| `-short` (3 x 30 ops, 1 API server; one compactor round) | 1 | 1/1, model and Kubernetes' checker | 1/1 (5 of 5 logs) | 2 kills |
| 4 x 200 ops (+ 2 watchers x 20 in two), 20 compactor rounds | 3 | 3/3, model and Kubernetes' checker (done within ~5 s of the first fault) | 3/3 (100 of 100 logs each) | 17 kills, 4 partitions, 1 link fault |
| 4 x 1500 ops (`DIST_OPS`; watchers in one), 200 rounds | 3 | 3/3, model only (a call failed: Kubernetes' checker is defined on failure-free histories only) | 3/3 (1000 of 1000 logs each) | 281 kills, 64 partitions, 42 link faults, 1.5-2.5 min each |
| 4 x 800 ops + 2 watchers x 20, 150 rounds | 3 | 2/3, model only; one porcupine timeout (5 min, Unknown: no verdict) | 3/3 (750 of 750 logs each) | 364 kills, 111 partitions, 37 link faults |

In all, 10 deployments, 664 kills, 179 partitions, 80 link faults; API server counts 1, 4, 5 and 6.
No check failed; no bug found in etcd or Kubernetes (nothing for `issues/` or `nonissues/`). Every
compactor API server answered every round (a 2-second network fault does not outlast a call's
minute). No Raw was flagged lost (`RawOK`) in the runs that reached Kubernetes' checker.
Not exercised here: power losses (no device mapper), resets.

## Open decisions

1. **The DaemonSet controller** runs over the model API server, not etcd: left out (above). Putting
   it on etcd needs an API server serving REST over the etcd3 store, a new program.
2. **`Apiservers`**: the store's clients share API servers or not, at random. Whether a theorem
   should fix one shape (one API server, as the driver; or one per client, as D8's kv) is open.
3. **Compactor rounds** repeat the driver's run (fresh compactors) so that faults meet it; the
   driver's statement has one. A Lean statement over this deployment would take `Rounds` or fix 1.
4. **Kubernetes' checker under faults** runs only on failure-free histories (upstream's), so the long
   runs are checked by the driver's model only.
5. Lean: none started. A statement over this deployment (as `etcd_dist_safe`'s) would need D2
   (`net` for clientv3 in `Net/`) and a `Report`/`Do` instance per workload (the codecs' `wireOk`,
   the store's `opMaybe` from the driver's call spec), as D8's kv.
