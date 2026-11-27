# k8s-dist: k8s_safe's program as a distributed deployment (Go)

2026-11-22, branch `k8s-dist` (the user's decision, kaashoek, 2026-11-22). The Kubernetes workloads
of `k8s_safe` (`examples/k8s/all`: the etcd3 store's partitioned workload and Kubernetes' compactor)
run against real etcd deployments of member machines, every Kubernetes component that is a client of
etcd on a machine of its own, the checks on orchestrator machines over Remote
(`examples/lib/remote`). Go only, as etcd-dist's stages D1 and D8 (`notes/etcd-dist-plan.md` §2);
no Lean. The in-process drivers (`examples/k8s/{etcd3,compactor,all}`) and their tests are unchanged (each driver gains only `export.go`, below):
`k8s_safe` is proved about them.

## The split

`examples/k8s/dist` (package `dist`, a Go module of its own) holds the driver of the deployment:
the orchestrator and client machine programs (`MainReady`, `NodeMain`), and, test-only
(`deploy_test.go`, since 2026-11-22: the machines' programs import neither etcd-dist's deployment
code nor `examples/lib/robust`), the deployment (`Deployment`, `WellFormed`, `RandomDeployment`);
`dist_test.go` deploys it. **One etcd cluster** (since 2026-11-22, the user's decision: below, "One
cluster"), an etcd-dist deployment with no etcd workload, its members etcd-dist's `server.Main` on
machines of their own, which both workloads use at once. The cluster has etcd's own compactor off
and no auth, as the drivers' clusters (`WellFormed` checks it; the snapshot settings are random, from
etcd-dist's choices).

| Component | Machine(s) | Program |
|---|---|---|
| etcd members | one per member, `member-i` | etcd-dist's `server.Main` |
| the etcd3 store (Kubernetes' `storage/etcd3`, an API server's storage) | `store-node-a`, `a < Apiservers` | `StoreNode`: the driver's store (`etcd3.New` over a kubernetes client of its own, members from `a` on) and one `remote.Serve` per client `c` with `c mod Apiservers = a`, each call the driver's `call` (or `runWatch`) |
| the store's clients, history and checks | `orch-store` | `RunStore`: seeds (`SeedShared`), then the driver's clients with `apply` a `remote.Do` at client `c`'s address; porcupine against the driver's `Model` with foreign revisions (`SharedModel`), then Kubernetes' checker (`realCheck`) on a failure-free history without a compacted error or a foreign revision |
| the compactor's writer | `compactor-node-0` | `CompactorNode`: the driver's `writer` per call, of a key outside the store's (`WriterAt`, `WriteKeyShared`; `remote.Report`, not awaited) |
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
(`etcd3.Serve`, `call`/`runWatch`), the cache bookkeeping (`tbl.put`, `putW`, `done`) on the
orchestrator (`etcd3.Record`, after the answer, before the return stamp, as `Apply`'s). The
output's `Raw` (the store's own answer, which only Kubernetes' checker reads, by `reflect.DeepEqual`)
crosses the wire in an encoding of the values the store returns (objects, lists, `StorageError`s,
the callbacks' errors, `StatusError`s, watch events); the API server checks that it decodes to a
value `DeepEqual` to the store's and otherwise flags it (`RawOK`), and the orchestrator then runs the
driver's model only, saying so. Compactor: `check` is split into `Sample` (the API server: every value
it reads) and `CheckLog` (the orchestrator: every comparison, in `check`'s order); `TestCheckLog`
exercises each panic.

## One cluster

2026-11-22, branch `k8s-one-cluster` (the user's decision, kaashoek): in real life one etcd cluster
serves all API servers, its compaction running while they serve requests. So the test runs one
cluster, both workloads against it at once (the store's API servers and the compactor's, every
compaction a Kubernetes compactor's). **Here the test differs from `k8s_all`**, whose program (and
`k8s_safe`'s statement) keeps two clusters, one per workload: the in-process drivers, `k8s_safe` and
their tests are unchanged. What sharing the cluster changes, and how the checks follow:

- **Keys.** The compactor driver's writer puts `/registry/objs/w`, inside the store's keys (Prefix
  `/registry` + `/objs/`): a recursive List or watch of the store would see it. The writer machine
  puts `/k8sdist-compactor/w` instead (`compactor.WriterAt`, `WriteKeyShared`, in `export.go`:
  the driver's `writer` loop with the key a parameter). `compact_rev_key` is outside both. The
  compactor's checks (`Sample`, `CheckLog`) are unchanged.
- **Seeds.** The driver's `seed` wants revisions 2 and 3 of a fresh cluster; the compactor may write
  first. `SeedShared` makes the same two Puts at whatever revisions they get, the history holding the
  empty store up to the first and each seed's store up to the next.
- **Foreign revisions.** Every write of the compactor workload (400 Puts a round, each compactor's
  `compact_rev_key` transaction) is a revision of the one cluster. The driver's `Model` numbers the
  store's revisions itself (a write at the store's revision plus one), so no history of the shared
  cluster passes it. `SharedModel` is `Model` with foreign revisions: the revision may advance at any
  time by any amount, the store's items unchanged, the history holding the store once per revision
  (so a past read at a revision in such a gap reads the store before it, at that revision). Every
  check of `Model` is kept (its own `step` runs on each configuration); only the revision numbers are
  let go. Foreign revisions cannot be enumerated, so the history drives them: before an operation, a
  configuration lets its pending writes take effect (`Model`'s closure, below), then moves to the least revision the answer needs
  (`target`: a write's revision less one, a "not found"'s or a current List's revision, a past List's
  or a Get's resource version, a watch's greatest event revision), then steps. When and at which
  revisions pending writes land, in three modes (`CheckShared` runs them in turn on Illegal; only
  `Full`'s Illegal is the panic): `Lazy`, only before an operation the configuration does not answer
  without them, at the next revision; `Eager`, before every operation, at the next revision or one
  the outputs show for its key but a successful write's answer, up to the bound the operation's
  answer sets (`bound`), or where its answer shows the write (`shows`); `Full`, also at every
  revision the history names and the one after each. `Full` is complete: a pending write's revision
  is either shown exactly (an object, an event, a precondition message) or can move down to one above
  the greatest revision named below it without changing any answer. The earlier modes are not
  (`Lazy`: a write seen only by its content, `Eager`: a past read inside a foreign gap before it).
  Speed-ups, none changing a verdict: histories are hash-consed (`histHashes`: one node per previous
  node and store, the foreign revisions after a node built once), so equal histories are one pointer
  and configurations compare in constant time; a watch is checked by `watchOkIdx`, `watchOk` line for
  line but reading the history through one walk (`hview`) where `histAt` walks back per revision (its
  window is thousands of revisions here), its verdict memoized per history; `TestReplayHistory` with
  `DIST_CROSS` checks the two agree on every watch step. On a 6040-operation history of the long
  runs: 98 s in the first eager version, 34 s with the memo, 0.7 s lazy (a heavy-fault one, below:
  0.6 s). `TestSharedModel` checks
  each mode's verdicts on small histories, both ways.
- **Heavy faults.** Runs under 120-130 kills in five minutes first ended "porcupine timed out": the
  lazy and eager modes answered Illegal and full ran out of time. A replay of the dumped history
  (`DIST_DUMP`, `TestReplayHistory`) showed why: a failed update that took effect at revision 1033,
  shown by a no-op update answering 1033 and by a Get, was given no landing there, since the eager
  mode's landings left out every revision a successful write had answered with, a no-op update's
  included. The eager mode now leaves out only those of Creates, Deletes and updates not asked to be
  no-ops (a write's own), and always tries the answer's own revision for the key; the history checks
  in 0.6 s. A bug of this test's check, not of etcd or Kubernetes. **Still open:** at 4 x 1500 ops
  under 133 kills the lazy mode answered Illegal and the eager one ran out of its 5 minutes (no
  verdict): a failed write that took effect, seen by its content and not its revision, may have
  landed at any revision of the foreign gaps around it, every placement a configuration of its own
  until a read tells them apart (17046 in one state of an earlier such history, at most four pending
  writes). A canonical placement (as late as possible, unless a read inside the gap needs it
  earlier) would close it; the dump replays it.
- **Compacted errors.** The API server reads them off the store's own answer (`StoreOut.Compacted`:
  `apierrors.IsResourceExpired`, or a watch Error event with reason Expired; Kubernetes' etcd3 store
  maps etcd's `ErrCompacted` to those, `interpretListError`, `interpretWatchError`), whether or not
  the Raw crosses the wire. The orchestrator accepts one on an operation at an explicit old revision
  (`PastRead`: a List at its resource version, Exact or the legacy recursive one with a limit; a watch
  from a resource version above 0) or at a revision the store fixed at an earlier read of its own
  (`PinnedRead`: a paged List's later pages, pagedChunks' `WithRev`; any watch: its start revision is
  the current one the store read, `getStartWatchResourceVersion`, or its list's, and the etcd client
  resumes a broken stream from its last revision), and panics on one anywhere else (a Get, a write,
  a List of one page read at the latest revision, which compaction never passes). Its outcome tells
  nothing: a List's is the driver's failed read (`EOther`, constraining nothing); a watch's Error
  event is dropped, as `Model` drops every Error event, and the events before it are checked as
  always. The result line counts them (`N compacted errors accepted (P at an explicit old revision,
  Q at a pinned one)`).
- **Kubernetes' checker** is defined on histories without a failed call, and its model numbers the
  revisions itself as `Model` does: it is skipped, and the result line says why, on a history with a
  compacted error, a failed call, a lost Raw, or one that shows a foreign revision (`NoForeign`: the
  successful writes' revisions above the seeds are not exactly the next ones, or some revision named
  is above the greatest). So in a run where the compactor writes while the store does, Kubernetes'
  checker does not run; it runs when the store's history happens to fall between the compactor's
  writes (one of the `-short` runs below).

The first version accepted a compacted error on explicit old revisions only; an early `-short` run
panicked on a watch from the most recent revision (`MinRV` "", SendInitialEvents false): the store
reads the current revision, then watches from the next, and a kill delays the watch past a
compaction. Hence `PinnedRead`.

## Exported wrappers (until 2026-11-27: copies)

The drivers' model, seeds, generator, per-client cache and `check` are unexported. Each driver's
package has one added file, `export.go` (`examples/k8s/etcd3/export.go`,
`examples/k8s/compactor/export.go`), that exports what the distributed workloads need; no existing
function of the drivers changes, so `k8s_safe`'s proof of them stands (the new functions are
translated with the drivers' packages, projects k8s-apiserver and k8s-compactor).

Until 2026-11-27 (G2 of `notes/k8s-dist-lean-plan.md`, the user's decision, kaashoek) the two
packages were copied **whole and byte for byte** into `examples/k8s/dist/{storecopy,compactorcopy}`
(checked by `TestVerbatim`), with `export.go` in the copy. The copies' reason, "the drivers must not
change", was not a user decision: adding a file changes no proved function, and the copies would
have needed every proof of the copied 2,955 lines duplicated under the copies' Go path. The copies
and `TestVerbatim` are gone; `examples/k8s/dist` imports the drivers.

| Added (`export.go`) | Wraps | Why |
|---|---|---|
| `SeedShared`, `Seeded.Model`, `Seeded.NewCache`, `Seeded.RealCheck`, `FailureFree` | `seed` (at the revisions the shared cluster gives), `Model`, `newWCache`, `realCheck`, `failureFree` | the orchestrator's half of `Check` |
| `Seeded.SharedModel`, `HistoryRevs`, `Seeded.NoForeign`, `AcceptAll` | `Model`'s `step`, `mstep`, `advance` with foreign revisions (below) | the store's check on the shared cluster |
| `PastRead`, `PinnedRead` | `pastRead` | where a compacted error is accepted |
| `SeededAt`, `EncodeItems`, `RVBytes` | the seeds' store; `encodeItems`, `rvBytes` | `TestSharedModel` only |
| `NewStoreOnly`, `SetFeatures` | `newStore` without `seed`; `noStreaming`, `watchList` | the API server's store; the orchestrator sets the same features |
| `Serve`, `Record` | `Apply` split at its prophecy | the API server's call; the orchestrator's cache |
| `IsWrite`, `Rejections` | `isWrite`; `errDeleteRejected`, `errUpdateRejected` | the codec |
| `WriterAt`, `WriteKeyShared`, `NewOwn`, `NewShared`, `Servers`, `SharedServers`, `Writes` | `writer` with a key of the caller's (the driver's `writeKey`, `/registry/objs/w`, is inside the store's keys); `apiserver`'s two constructors; the constants | the compactor's machines |
| `Sample`, `CheckLog`, `Log` | `check` (new code, a modification of `check`: split in two, the same reads and comparisons) | its reads on the API server, its comparisons on the orchestrator |

**No copies of etcd-dist's runner code (since 2026-11-22, the user's decision).** Until then this
package copied `awaitCluster`, `awaitNodes`, `rotate`, `connectRetry`, `reportAll` from etcd-dist's
`dist/client` and `TestDist`'s re-run in a user namespace from its test, and ran its own process
start, set-up wait and fault loop over three additions to etcd-dist's `Cluster` (`RunFaults`,
`Fail`, `Failed`). All of it is now `examples/lib/robust`'s or exported by etcd-dist, and used here:
`robust.Run` (one run; until the one cluster, each cluster's members a `Group` with a crasher of its own; `RunClients` starts the API server and writer machines' processes and the two
orchestrators, holds the faults until both set-ups are done, and makes one network nemesis over every
machine), `robust.RerunTest` and `robust.NewNetworkOrLocal` (in the tests only); the machines'
programs take `client.AwaitCluster`, `client.ConnectRetry`, `client.AwaitAccept`, `client.Rotate` and
`client.CallAll` (the compactor's calls to its API servers) from etcd-dist's `dist/client`, and
`env.ClearProxy`; the tests `dist.MemberAddrs` (in place of their `addrs`). Only the tests import
etcd-dist's `dist`, to deploy the clusters (`Start`, `Deployment`, `WellFormed`, `RunProcess` for
the members' role), and `robust`. The faults' counts are now the run's, one line (`kills …, power losses …`). Where everything lives: `notes/etcd-dist-plan.md` §2,
"What is generic lives in `examples/lib/robust`". `etc/goose.py`: the module's `GO_MOD_PINS` (etcd,
raft, bbolt) and `CLIENT_GO_PINS` (k8s versions = `examples/k8s/etcd3`'s).

Departures from the drivers (none weakens a check): porcupine and Kubernetes' checker run with a
5-minute timeout (`CheckTimeout`; a timeout ends without a verdict, never a failure), where the
drivers have none; the compactor runs `Rounds` rounds of its API servers (the driver's one, repeated
with fresh compactors, a writer call per round), so that the faults meet it (one round takes about a
second).

## Running it

`cd examples/k8s/dist; GOTOOLCHAIN=go1.27.3 DIST_RUN=1 go test -run '^TestDist$' -v` (`-short`:
one small deployment; `DIST_ROUNDS` deployments otherwise, default 4; `DIST_OPS` the store clients'
operations; `DIST_ROUNDS_C` the compactor's rounds; `DIST_DUMP=FILE` writes each deployment's store history to `FILE.<pid>`, with
its seeds' revisions, which `DIST_HISTORY=FILE.<pid> go test -run
TestReplayHistory -v` checks again, timed, with a corrupted copy that must be rejected). Machines and faults are etcd-dist's: on this
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

**2026-11-22, one cluster** (branch `k8s-one-cluster`; this machine, the bridge variant, kills with
sync, no power losses, no resets; three members). No machine panicked and no member exited on its
own in any run; no compacted error came from an operation `PastRead`/`PinnedRead` does not cover
after `PinnedRead` was added (one watch from the most recent revision before, above); no check
answered Illegal. Kubernetes' checker ran in one `-short` deployment (the store finished between the
compactor's writes) and was skipped in every other, saying why (a compacted error or a foreign
revision).

| Runs (the check's version) | Deployments | Store | Compactor | Faults | Compacted errors accepted |
|---|---|---|---|---|---|
| `-short` (3 x 30 ops; 2 rounds), all versions | 16 | 14 checked (1 by the model and Kubernetes' checker), 2 the watch panic above (before `PinnedRead`) | all checked | 1-3 kills each | 0-3 each |
| 3 x (4 x 200 ops, 20 rounds), first version | 3 | 3/3 | 3/3 (100 logs each) | 31 kills, 18 partitions, 9 link faults | 13, 26, 21 |
| 4 x 800 ops, 150-200 rounds, versions 1-2 | 9 | 6 checked, 3 timed out (118-132 kills) | 9/9 | 31-132 kills each | 43-82 each |
| 4 x 1500 ops, 200 rounds, version 2 | 3 | 1 checked, 2 timed out (126, 130 kills) | 3/3 | 57-130 kills | 118-132 each |
| 3 x (4 x 200), 3 x (4 x 800, 150 rounds), version 3 before the landing fix | 6 | 4 checked, 2 timed out (125 kills each; the eager mode's wrong Illegal, above) | 6/6 | 6-125 kills | 10-73 each |
| 3 x (4 x 1500, 200 rounds), final | 3 | 2 checked, 1 timed out (133 kills) | 3/3 (1000 logs each) | 44, 59, 133 kills; 143 partitions, 60 link faults | 100, 107, 114 |

Versions: 1 the first `SharedModel` (`ddffd7f60b`), 2 its first speed-ups (`a08213aa95`), 3 the
three modes and the indexed watch check (never committed alone), final with the landing fix
(`ef5b83bec3`). Replays of the dumped histories with the final check: the three 4 x 800 histories of the run before
the fix (one of them a timeout) check in 0.03-0.6 s, each with a corrupted Get rejected in every mode
and every watch step cross-checked (`DIST_CROSS`). Across the runs, 10 to 132 compacted errors per
long deployment, all on Lists at an explicit old revision but 0-2 on watches (`PinnedRead`).
Nothing for `issues/` or `nonissues/`: the one failure found was this test's own check.

## Open decisions

1. **The DaemonSet controller** runs over the model API server, not etcd: left out (above). Putting
   it on etcd needs an API server serving REST over the etcd3 store, a new program.
2. **`Apiservers`**: the store's clients share API servers or not, at random. Whether a theorem
   should fix one shape (one API server, as the driver; or one per client, as D8's kv) is open.
3. **Compactor rounds** repeat the driver's run (fresh compactors) so that faults meet it; the
   driver's statement has one. A Lean statement over this deployment would take `Rounds` or fix 1.
4. **Kubernetes' checker under faults** runs only on failure-free histories (upstream's), so the long
   runs are checked by the driver's model only. On one cluster it also needs no foreign revision and
   no compacted error, so it does not run once the compactor writes during the store's run: a model
   of its own with foreign revisions would be a change to the maintainers' code.
6. **One cluster or two.** The test has one cluster (the user's decision); `k8s_all`'s program and
   `k8s_safe` keep two. A Lean statement over this deployment would state the store's correctness
   against `SharedModel` (foreign revisions, compacted errors on old-revision reads), not `Model`.
7. **Where a compacted error is accepted**: at an explicit old revision (`PastRead`) and at one the
   store fixed itself (`PinnedRead`: paged Lists, every watch). The second goes past "explicit old
   revision" because a watch from the most recent revision was compacted in an early `-short` run
   (the store's own read of the current revision, then a kill delaying the watch).
   **Decided (kaashoek, 2026-11-22): accepted** — etcd really answers so (the revision the store
   picked is compacted before the watch is established), so the check must allow it.
5. Lean: none started. A statement over this deployment (as `etcd_safe`'s) would need D2
   (`net` for clientv3 in `Net/`) and a `Report`/`Do` instance per workload (the codecs' `wireOk`,
   the store's `opMaybe` from the driver's call spec), as D8's kv.
