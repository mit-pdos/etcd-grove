# crashreconf: the end theorem's program (members crashing, random reconfigurations)

`examples/etcd/crashreconf/`: the program the porcupine adequacy theorem at the etcd client
boundary will be about, in Perennial's distributed GooseLang (`DistLang.lean`: a list of nodes,
each with its own threads and local state; a node crashes alone and reruns its boot program from
what its disk keeps; the network and the other nodes are unchanged). Written 2026-11-10.

## The nodes

A fixed **pool of `NSlots` = 5 member slots** (slot `i`: peer address `127.0.0.1:2430<i+1>`,
client address `127.0.0.1:2431<i+1>`, the peer URL `http://<peer addr>`), of which the first
`NInitial` = 3 form the initial cluster (token `crashreconf`), and **one client node**. The
program is `NSlots + 1` boot functions: `MemberNode(i)` for slot `i`, `ClientNode(clients, ops)`
for the client. Nothing else is shared: every address, name and the initial cluster are constants
of the package, so each boot function takes only its slot.

### A member node (`MemberNode(i)`, rerun from its disk after every crash)

A slot hosts a sequence of **incarnations** `k = 0, 1, 2, ...`: incarnation `k` is etcd member
`s<i>-<k>`, data directory `s<i>-<k>.etcd`. Incarnation `k` is *retired* when the file
`s<i>-<k>.removed` exists. The boot function loops:

1. `k` := the first incarnation that is not retired (each marker opened read-only with
   `os.OpenFile`; the only file operations the node itself does).
2. Start incarnation `k` (both listeners opened first, so that a failed start leaves nothing to
   stop):
   - **bootstrap or restart**, if `k = 0` and the slot is initial: `etcdserver.NewServer` with the
     initial cluster and `NewCluster: true`. etcd itself decides (`bootstrap.go`: `wal.Exist`):
     with a WAL the member restarts from it (as etcd's `main` restarts a member: same name, data
     directory, peer and client URLs, the configuration otherwise ignored), without one it
     bootstraps (a node that crashed before its WAL was created never sent anything: raft starts
     only after `wal.Create`).
   - **restart**, if the member's WAL exists (`wal.Exist(<data dir>/member/wal)`, the check
     `NewServer` makes): `NewServer` with `NewCluster: false` and the one-member map of itself
     (unused on a restart).
   - **join**, otherwise: wait until the cluster lists an *unstarted* member (empty name) whose
     peer URL is the slot's (`MemberList`, linearizable, through a client of the other slots'
     client addresses, polled), then `NewServer` with `NewCluster: false` and the initial cluster
     built from that list (every member's name, the slot's own for the unstarted one, and its peer
     URLs: the string `etcdctl member add` prints). A failed `NewServer` (the list went stale, a
     peer unreachable) loops back to 1.
   Then etcd's whole peer handler (`etcdhttp.NewPeerHandler`, as etcd's `embed` serves it, not
   only `RaftHandler` as etcdstart and cluster3 do: see "Findings") served on the peer listener,
   the server started, its gRPC API (`v3rpc.Server`, etcdstart's keepalive policy) served on the
   client listener.
3. Wait for the server to stop (`StopNotify`). etcd stops a member that applies its own removal
   (`stopWithDelay`, "permanently removed") and one its peers answer with 410 Gone (a member
   removed while it was down: rafthttp's `errMemberRemoved` on `errorc`); nothing else stops it.
   Close both listeners (`grpc.Server.Stop`, the peer listener's `Close`).
4. Ask the cluster whether the incarnation was removed: one linearizable `MemberList` (request
   timeout). If its member id is absent, create the marker `s<i>-<k>.removed` (member ids are
   never reused, so absence is final). Loop back to 1: a removed slot waits there until it is
   added again (a new incarnation, a new member id, a fresh data directory); an unretired one
   restarts (if the list failed, the restart of a removed member stops again at once, and the
   check is retried).

The marker need not be durable: if a crash loses it, the boot restarts the removed incarnation,
which its peers stop again (410), and the marker is written again. So the node's own disk state
is the markers plus etcd's data directories, and every decision is either etcd's own
(`NewServer`'s WAL check) or the cluster's (the member list).

**Why the member list, not a message from the client node.** The brief suggested that the client
node tell a joining node it was added (a file or a message). A file is not possible across nodes
in `DistLang` (a node's disk is its own); a message needs a channel of its own (a control
listener on each member node, an acknowledgement and a retry, since the node may be down when it
is told) that the network extensions would have to model beside grpc's and net/http's. Polling
the cluster's member list uses only the client API both sides already use, survives crashes on
either side for free, and gives the same cluster string: with one change at a time, the list the
joiner reads while its member is unstarted is the list the add returned (a later change, the
learner's removal on a timeout, makes the join fail validation, or the member stop at once).

### The client node (`ClientNode(clients, ops)`, never crashes)

- `NKVClients` = 3 KV clients and one admin client, each `etcdstart.NewClients` of every slot's
  client address (etcd's default retries; dead addresses are skipped by gRPC's balancer);
- the **reconfiguration goroutine** (below), until the workload ends (an `atomic.Bool`);
- `lintest.Run(txnlin.Model(), apply, txnlin.Gen, CounterClock, clients, ops, 0)`, where `apply`
  picks a KV client at random and calls `txnlin.Apply` (as `partition.Apply` does): txnlin's
  workload, model and prophecies unchanged;
- panic if porcupine answers `Illegal`.

**The reconfiguration goroutine**, every 200-700ms (random): `MemberList` (linearizable); point the
KV and admin clients at the started voters' client addresses (`SetEndpoints`, plain host:ports:
what clientv3's `Sync` does, without the scheme, which `clientv3.New`'s spec premise excludes);
then one change, by etcd's rules:

- a learner exists: `MemberPromote` it (`ErrLearnerNotReady` until it caught up: retried next
  round); after `MaxPromoteTries` failed rounds (its node down, or still joining) `MemberRemove`
  it instead;
- otherwise, at random: `MemberAddAsLearner` of a free slot (one whose peer URL no member has) if
  there are fewer than `NSlots` voters, or `MemberRemove` of a random voter (the leader included)
  if there are more than `MinVoters` = 3.

One change at a time (each call returns after the change applied at the member that served it,
and the next round re-reads the list); at most one learner (etcd's `MaxLearners` default, 1). Every
error -- `ErrUnhealthy` (strict reconfiguration check: on by etcd's default, set here; it refuses a
change for 5s after any peer reconnected), `ErrLearnerNotReady`, `ErrMemberNotLearner`,
`ErrIDNotFound`, `ErrPeerURLExist` after an add that timed out but took effect, a timeout -- is
handled the same way: nothing, and the next round re-reads the list. So the goroutine never
inspects an error.

**Reconfigurations are not in the porcupine history.** txnlin's `Model` is the KV store; a
membership change does not change it (`Model.lean`'s `Step` on a member request leaves `kv`
unchanged), so recording them would add operations the model maps to no-ops and nothing to check.
The theorem still covers them: every `Member*` call takes its update over `etcdState` (top.md §1),
which the program's invariant must accept -- membership steps leave the KV part, the only part the
linearization log replays, unchanged.

### The member configuration

etcdstart's (`newServerMode`) fields, plus: `DataDir` per incarnation, `NewCluster` per start,
`StrictReconfigCheck: true` and `MaxLearners: 1` (etcd's defaults, which etcdstart's zero values
turn off: 0 learners would refuse every `MemberAddAsLearner`), snapshots every `SnapCount` = 10
applied entries with `SnapCatchUp` = 5 kept (a joining learner and a restarted member are caught up
by a snapshot as well as by entries). PreVote stays off (etcdstart's `NewServer` premise; etcd's
default is on).

## Goose-friendliness

Only what the existing examples use: `etcdserver.NewServer`, `Start`, `StopNotify`, `MemberID`;
`v3rpc.Server`; `etcdhttp.NewPeerHandler` (new: the examples serve `RaftHandler` alone); `net.Listen`, `http.Serve`, `grpc.Server.Serve`/`Stop`;
`clientv3`'s `New`, `MemberList`, `MemberAddAsLearner`, `MemberPromote`, `MemberRemove`,
`SetEndpoints`, and txnlin's `Apply`/`Gen`/`Model`; `os.OpenFile`, `File.Sync`, `File.Close` (the
calls the os model has); `wal.Exist` (bootstrap's own check); `time.Sleep`, `atomic.Bool`,
`primitive.RandomUint64`, string concatenation and a hand-written `itoa` (mvccrand's). No
reflection, `os/exec`, `fmt`, `strconv`, generics, `select` or `errors.Is`. The real-run harness
(`crashreconf_test.go`) is not translated.

What the proof will need that is new (for the network and K2 work):
- **K2's join case** with a cluster string from `MemberList` (top.md §3: "`etcdLb γ σ` with the
  member in `σ.members`"), and its restart case for a removed member (it stops; no further
  obligation).
- **Rebinding an address.** A slot's two addresses are bound again after every crash and after
  every re-join (restart3 serves an address once per run; a crash makes rebinding unavoidable).
- **`StopNotify`** (the server's `done`): a spec for "the server stopped, its backend closed".
- **`wal.Exist`** (names-only today) as part of the member's durable-state abstraction.
- **etcd's peer HTTP API beyond raft** (`etcdhttp.NewPeerHandler`): `GET /members` (a joiner's
  `GetClusterFromRemotePeers`), `GET /version` (`isCompatibleWithCluster`), `POST
  /members/promote/<id>` (a follower forwards `MemberPromote` to the leader), the lease routes. The
  net/http extension and the server batch must cover them.
- **A reused peer URL.** A slot's incarnations share its peer URL, which the server proof's
  premise excludes (`transportEffectsOk`, "the peer URLs address the members they name";
  `nonissues/etcd-rafthttp-misaddressed-403-member-removed.md`): a lagging member's message to the
  previous incarnation's id reaches the new one. See "Findings" and the open choices.

## The real-run harness (`crashreconf_test.go`)

`go test` runs each member node as a separate OS process: the test binary re-executed with
`CRASHRECONF_SLOT=i`, in a per-slot directory under the test's temp directory, whose `TestMain`
runs `MemberNode(i)` (with a logger to a file, `RunMember`). The client node runs in the test
process; its body is `RunClient`'s, with the workload driven by the test as `lintest.Run` drives
it (`runWorkload`: the same loop, plus a `-crashreconf.pace` pause before each operation, default
100ms, so that a round lasts long enough for reconfigurations) so that the history is kept. A
crasher goroutine kills a node picked at random every 2-6s (SIGKILL; a member, a joining or an
idle node), waits 100-800ms and starts it again on the same directory (its boot function reruns):
at most one node down at a time, never the client. Then porcupine's verdict. The test fails on
`Illegal` (the round's directory is kept: `history.json`, `porcupine.html`, every node's
`node.log`/`out.log`), on a node process that exited by itself (a panic, a fatal), and, in the
default single round, on `Unknown` (porcupine's timeout, 3 minutes), no kill or no membership
change. Defaults: 3 clients x 150 operations, one round of about 20s.

`-crashreconf.soak=DURATION` runs rounds (each a fresh cluster) until the duration is spent and
reports each round and the totals; other knobs: `-crashreconf.{clients,ops,pace,seed,killmin,
killmax,checktimeout,keep}`. The rounds' directories are under `$TMPDIR/crashreconf-*`, removed
unless kept.

**Process kills are not power losses.** SIGKILL keeps the page cache: what the harness exercises
is a process crash, not the disk model's crash (unsynced writes or directory entries lost:
`nonissues/etcd-member-dir-not-synced.md`), which `DistLang` will quantify over.

## Findings

1. **A member must serve etcd's whole peer handler, not only `RaftHandler`.** The first runs
   served `s.RaftHandler()` on the peer listener, as `etcdstart.NewMember`, cluster3 and restart3
   do: no learner ever joined (`bootstrapExistingClusterNoWAL`'s `GetClusterFromRemotePeers` reads
   the peers' `GET /members`, which got 404), and `MemberPromote` through a follower failed with
   `ErrIDNotFound` (the follower forwards it to the leader's `POST /members/promote/<id>`;
   `promoteMemberHTTP` reads the mux's 404 as "member not found"), alternating with
   `ErrLearnerNotReady` when the call reached the leader directly. `etcdhttp.NewPeerHandler` (what
   etcd's `embed` serves) fixes both. Not an etcd bug (a misdeployment), but the static-cluster
   examples' proofs never needed these routes, and a reconfiguring one does.
2. **rafthttp's pipeline handler panics on every `Process` error** (recovered by net/http: the
   nodes' `out.log` show `http: panic serving ...: cannot process message to mismatch member`,
   `rafthttp/http.go:162`). `Process` returns `*httptypes.HTTPError`, whose `WriteTo` returns an
   `error`, so it is not a `writerToResponse` (`WriteTo(w)` with no result) and the `errors.As`
   branch that would write the 403 is dead, upstream too (v3.7.2, main). Here it is reached by a
   lagging member's message to a slot's previous incarnation, at the peer URL the new one reuses.
   The repository already models the recovery (`notes/rafthttp-http-boundary.md`, item 5). But
   `nonissues/etcd-rafthttp-misaddressed-403-member-removed.md` says the misaddressed member
   "answers 403", which the sender reads as `errMemberRemoved`: through the pipeline it answers
   500 (the handler's `http.Error` before the panic), which `checkPostResponse` does not treat as
   critical. That nonissue's pipeline scenario looks unreachable as written (worth re-checking; its
   stream-handler side, 412 on `X-Raft-To`, is not critical either).
3. No `Illegal`, no node process that exited by itself, no commit lost
   (`issues/raft-commit-lost-with-entries-kept.md` needs a crash between a `Ready`'s entries and
   its `HardState` with two conf changes in one append; SIGKILL of a `WAL.Save` under 128 KiB
   cannot split it, and these appends are small).

## Results

2026-11-10, this machine (shared, 24 cores), pinned fork (etcd `a4d2bb17`, raft `565c2bd`), go1.27.3:

| run | rounds | Ok | Unknown | Illegal | ops (failed) | kills | adds / promotions / voter removals |
|---|---|---|---|---|---|---|---|
| `go test` (defaults: 3x150 ops, kills every 2-6s), 7 runs | 7 | 7 | 0 | 0 | 3150 (27) | 34 | 23 / 23 / 18 |
| soak 8m, defaults | 21 | 21 | 0 | 0 | 9450 (49) | 92 | 77 / 76 / 51 |
| soak 12m, kills every 1-3s, 3x250 ops | 12 | 10 | 2 | 0 | 9000 (69) | 187 | 34 / 31 / 26 |

A default round's workload takes 16-32s; `go test` took 18-28s, once 98s (a round with 10 failed
operations, whose check took 62s). Members joined in a round: up to 6
(including re-joins of retired slots), retired up to 5, snapshots sent to joining or restarted
members in every round, recovered handler panics (finding 2) in about half the rounds, no NewServer
or listen failure, no learner removed (every learner was promoted within `MaxPromoteTries`).

**Porcupine's cost is the limit.** The two `Unknown`s are porcupine's 3-minute timeout on rounds
with 9 and 10 failed operations (one other round with 9 checked in 51s, one with 10 in 62s): a
failed write stays pending in txnlin's model to the end of the history (as in partition's test),
so the check is exponential in the failed writes. The defaults keep a round near 0-5 failures
(each kill of the leader or of the member serving a call fails about one call per client); a
longer or more aggressive soak needs many short rounds, not long ones.

## Open choices

1. **How a joiner learns it was added**: the member list (here) or a message from the client node
   (the brief's suggestion; a channel the network extensions would also model, with an ack).
2. **Reusing a slot's peer URL** across incarnations (here: realistic, an operator re-adding a
   machine) breaks the server proof's premise that peer URLs address the members they name; the
   alternative is fresh addresses per incarnation (the client picks `(slot, k)` ports; the node
   adopts the `k` it is listed with), which keeps the premise at the cost of unbounded ports.
3. **The member configuration** is this package's own `serverConfig` (etcdstart's plus
   `NewCluster`, a per-incarnation `DataDir`, `StrictReconfigCheck`, `MaxLearners: 1`); it could
   move into `etcdstart` (an exported config builder) so that it is proved once. PreVote stays off
   (etcdstart's premise) although etcd's default is on.
4. **Reconfigurations outside the porcupine history** (here), or recorded as model no-ops.
5. **The workload's size** in the theorem is a parameter (`ClientNode(clients, ops)`); the real
   run's pacing (`-crashreconf.pace`) is the harness's, not the program's.
