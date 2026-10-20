# Plan: the three-member cluster under network partitions (`examples/linkv3p`)

Status: S0–S3b done (2026-10-20, branch `linkv3p`, worktree `/shared/etcd-grove-pt`; STATUS
"Partitions, S0", "S1/S2", "S3a", "S3b"): the Go program, its test and the translations; the two
transport axioms and the server's `CutPeer`/`MendPeer` proved; the example's functions proved and
linked; `Main` proved and the closed theorem `linkv3p_safe` closed, for every schedule. S1 needed
a change of design (D24 in decisions.md): a second `CutPeer` of a *remote* panics
(`issues/etcd-rafthttp-cutpeer-twice-remote-panic.md`), so the transport's ghost state now tracks
its remotes and the axioms take `id ∉ rs`; a new cluster's member has none (`bootOk`). S4 (the
gates and notes) is in STATUS's S3b entry.

## Goal

An end-to-end safety theorem for a three-member etcd cluster whose members get cut off from one
another during the run, with clients at every member: `linkv3p_safe`, the shape of `linkv3_safe`
(`Proof/github_com/mit_pdos/etcd_grove/examples/linkv3/Results.lean`) with one more input, the
partition schedule, universally quantified:

> For every `clients`, `ops` and every schedule `sched`, every real execution of `n` steps of
> `linkv3p`'s initialization followed by `Main(clients, ops, sched)` has no stuck thread, no
> thread ended in a panic (so porcupine never answers `Illegal`: the history of Puts and Gets,
> issued at all three members while the schedule cuts and mends the links between them, is
> linearizable against linkv's key-value model), and the main thread's result, if any, is `Ok`
> or `Unknown`.

(Since 2026-10-20 the workload is linkvtxn's, `notes/linkv3p-txn-plan.md`: gets, lists, puts,
deletes, transactions and compare-and-sets against the model of etcd's KV, on the same trust
base.)

On exactly `linkv3_safe`'s axioms plus two, rafthttp's `Transport.CutPeer` and `MendPeer`
(below). Safety only: that the majority side keeps serving is liveness, which this framework
does not state.

## What is already there, and what partitions mean for it

- **`linkv3_safe`** (D20, 2026-10-19): three members in one program, each serving its raft
  handler, a client to the first member only, linkv's workload (`linkv.Check`: `lintest.Run`,
  porcupine, linkv's model with failed puts pending). No partition is ever induced, and the
  members other than the first serve no client.
- **The network model already admits partitions.** `Transport.Start`'s axiom
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__Start.lean`, D21 M2) says of
  every sent message: "possibly lost (writers drop on error or a full buffer), never retried",
  delivered at most once if `once`, otherwise with its persistent part duplicable (`Net.lean`,
  `NetPayload`). A partition is a stretch of the execution in which every message between two
  members is lost. So every execution of a partitioned cluster is already one `linkv3_safe`
  quantifies over, and the raft proof (CheckQuorum and PreVote on, 2026-10-17; elections, a
  leader's step-down, proposal forwarding with the once ticket, reject hints, read index) and the
  server's (the request path's every error return, `ReportUnreachable`, `Process`) are proved over
  that model. The no-snapshot mode (D21 M3) does not depend on delivery: the storage stays
  uncompacted under the step bound whatever the network does, so a member that fell behind
  catches up by entries, never by a snapshot.
- **What is missing is therefore not in the proofs but in the program and the statement:**
  1. the program never cuts a link, so nothing shows the theorem is not vacuous under partitions,
     and the Go test cannot exercise one;
  2. the clients are at one member, so the behaviour partitions threaten (a minority member
     answering a linearizable Get from a stale state, a Put acknowledged on both sides of a cut,
     a forwarded proposal applied twice) is never requested;
  3. a theorem that does not mention partitions does not tell its reader they are covered.
- **etcd's own partition mechanism exists and is tiny.** `EtcdServer.CutPeer(id)` and
  `MendPeer(id)` (`server/etcdserver/server.go`) type-assert `s.r.transport` to
  `*rafthttp.Transport` and call its `CutPeer`/`MendPeer`, which `Pause`/`Resume` the peer: a
  paused peer's `send` drops every outgoing message, and its stream readers' `decodeLoop` drops
  every message received on them. etcd's integration tests partition a cluster exactly so
  (`tests/framework/integration/cluster.go`, `InjectPartition`/`RecoverPartition`: cut in both
  directions). Both effects are "lost" in the network model, so the two transport methods are
  axioms that assert nothing beyond returning. The server's `srvNetMember γn s id`
  (`InvRaftHandler.lean`, given by `NewServer.spec`) already exposes what the type assertion
  needs: `rnTransportAddr (srvRAddr s) ↦□ transportIface t ∗ transportStarted γn t`.
- **Out of scope** (as before, STATUS "Open work", "Out of scope for now"): crashes and
  durability (no crash semantics; persist-before-send is not stated), liveness, and partitions
  between a client and its member (a client's gRPC call simply fails; optional, see S0).

## Design

**D-P1. Partitions by etcd's `CutPeer`/`MendPeer`, not by a proxy.** A reverse proxy between the
members would keep etcd untouched but would add its own code to verify, over `net`'s axioms, and
would be our mechanism, not etcd's. `CutPeer`/`MendPeer` are what etcd's tests use, so the
theorem covers the partitions etcd's own integration tests inject. Cost: two trust-boundary
axioms on the names-only transport (S1) and two small server proofs (S2).

**D-P2. The schedule is an input of `Main`, universally quantified.** A step is a delay, cut or
mend, and two member indices; the partitioner goroutine sleeps the delay and applies the step in
both directions (as `InjectPartition` does); an index out of range is skipped, so the theorem
needs no hypothesis on `sched`. The empty schedule is `linkv3`; a schedule may never mend. A
randomized schedule (steps drawn with `primitive.RandomUint64` as `Gen` draws operations) would be
the same proof (nothing in the spec depends on the steps' values); the test can draw its schedule
at random and print it. `time.Sleep`'s spec is `True → True` (Perennial), so the delays cost
nothing in the proof.

**D-P3. Clients at every member; each operation picks a member at random.** `lintest.Run` calls
`apply(input)` without the worker's id, so the new `Apply(clis, input)` picks `clis[RandomUint64()
% 3]` and calls `linkv.Apply`. Every member serves gRPC (`v3rpc.Server`, `net.Listen`, `Serve`
move into `startMember`), one `clientv3.New` per member with `MaxUnaryRetries: 1`. The at-most-once
Put (D21 M6) and the read-index Get are then requested at followers and at members on the
minority side of a cut: that is the test of the raft and server proofs this example adds.

**D-P4. A new package `examples/linkv3p`, linkv and linkv3 untouched.** It imports linkv for
`Model`, `Gen`, `Apply`, so their proofs carry over, as linkv3's do; its own `Apply` (the pick),
`Check`, `startMember`, `partitioner`, `Main`. Generalizing linkv's `Check` to a slice of clients
would change `linkv_safe`'s and `linkv3_safe`'s program.

**D-P5. Nontriviality is shown by the Go test, not the theorem.** The theorem is the same
`Ok ∨ Unknown`. `TestMainRun` runs a schedule that isolates one member, mends, then isolates
another, and checks: `Ok`; the puts took effect (as linkv3's test); a client connected after `Main`
to each member sees a raft term past the first election's (a re-election happened); the leader
changed. Expect failed operations on the minority side (`ReqTimeout` is `5s + 2 ·
ElectionTicks · TickMs = 7s`), so the test takes a minute or so; `go test -race`.

## Stages

### S0. The Go program and its test (`examples/linkv3p`)

- `go.mod` as linkv3's (putget's replaces, raft at the fork's `c8217eb9`); names `linkv3p-1..3`,
  token `linkv3p`, six fresh ports (peer `127.0.0.1:2384{1,2,3}`, client `2383{1,2,3}`; no other
  example's).
- `startMember`: linkv3's plus `gs := v3rpc.Server(s, nil, nil)`, `net.Listen` at the client
  address, `go gs.Serve(l)`; returns the server.
- `type Step struct { Delay time.Duration; Cut bool; A, B int }`; `partitioner(srvs
  []*etcdserver.EtcdServer, sched []Step)`: for each step, `time.Sleep`, skip if `A`/`B` out of
  range or equal, else `srvs[A].CutPeer(srvs[B].MemberID())` and the reverse (`MendPeer` for a
  mend).
- `Apply(clis []*clientv3.Client, input any) any`: the pick, then `linkv.Apply`. `Check(clis,
  clients, ops, timeout)`: `lintest.Run(linkv.Model(), apply, linkv.Gen, lintest.CounterClock(),
  ...)`.
- `Main(clients, ops int, sched []Step) porcupine.CheckResult`: three `startMember`s, three
  `clientv3.New`s, `go partitioner(srvs, sched)`, `Check`, panic on `Illegal`.
- Tests: `TestMemberIDs` (the ids' low 16 bits; prints `bootstrap`'s order for `BootFacts`),
  `TestMainRun` (D-P5), and a `TestNoPartition` with the empty schedule.
- Translation: project `linkv3p` in `etc/goose.py` (as `linkv3`'s entry); etcd's configuration
  gains `EtcdServer.CutPeer`/`MendPeer` with bodies (the type assertion is a Goose `TypeAssert2`;
  rafthttp stays names-only, its `CutPeer`/`MendPeer` names reached). `etc/goose.py --check`.
  Check first that the pinned translator takes the type assertion in these two bodies (a scratch
  copy, as D21 M2 did).

### S1. The transport's two axioms (trust boundary, +2) -- done, as amended by D24

`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__{CutPeer,MendPeer}.lean`:
`{{ isPkgInit rafthttp ∗ transportStarted γn t ∗ transportRemotes t rs ∗ ⌜id ∉ rs⌝ }} t.CutPeer(id)
{{ RET #(); True }}`, likewise `MendPeer`; `Proof/.../Transport__{CutPeer,MendPeer}.lean`: `axiom`.
The docstrings say why they are true of `transport.go`/`peer.go`/`stream.go` at the pin: `t.mu.RLock`
and the two map lookups never panic on a started transport; on the peer, `Pause` sets `paused` and
pauses the two stream readers, after which `send` returns without sending and `decodeLoop`
discards what it decodes; `Resume` clears them; both idempotent; nothing is resent. Every message
so dropped is one `Transport.Start`'s promise already allows to be lost, so the network model is
unchanged. **The amendment** (D24): `id` must not be a remote, since a remote's second `Pause`
panics (`issues/etcd-rafthttp-cutpeer-twice-remote-panic.md`); `transportLive γn t rs` tracks the
ids `AddRemote` was called with (`Start` at `[]`, `AddPeer` keeps it), given up for
`transportStarted γn t ∗ transportRemotes t rs` (`InvBoot.lean`); `Start`/`AddRemote`/`AddPeer`
restated. Linked in `etc/link-lean-first-server.txt` (axioms, as `Transport__Start`'s).

### S2. `EtcdServer.CutPeer`/`MendPeer` proved (server) -- done

`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__{CutPeer,MendPeer}.lean`:
`{{ isPkgInit etcdserver ∗ srvNetMember γn s mid }} s.CutPeer(id) {{ RET #(); True }}`. Proof:
`srvNetMember` gives the read-only transport field, `transportStarted γn t` and (D24)
`transportRemotes t []`, from `bootOk`'s new `rms = []` (a new cluster's bootstrap has no remote;
`NewServer`'s `AddRemote` loop is dead); the type assertion succeeds with `t` (`wp_auto` on
`transportIface t`) and S1's axiom applies at `rs = []`. `srvNetMember` has to reach the example:
`NewServer.spec` gives it (D21 M5) and putget3's `startMember` proof drops it after `RaftHandler`,
so linkv3p's `startMember` returns it beside `memberUp` (S3a). Linked (`etc/gen-link.py --server`).

### S3a. The example's Lean skeleton -- done

As planned below, with these particulars: `newClient` (the Go program's helper) has its own spec
and proof; `startMember`'s success is `memberServed` (the member's views, its thread token in
`srvGoRes`, `srvNetMember`, etcd's `Put`/`Range` at its client address), not putget3's `memberUp`;
the per-client premises are bundled as `clientOk`; `cluster3_alloc` gives the `etcdKV` at the
*first* member's names (the names' order is `bootstrap`'s for linkv3p) and the other two members'
state variable and workload equal to the first's, for `linkvInv_congr`; `partitioner`'s spec takes
any list of servers, each with `∃ id, srvNetMember`, and any list of steps.

`Proof/github_com/mit_pdos/etcd_grove/examples/linkv3p/`: `Defs` (names, six addresses, `cfgOk`
at the token, `BootFacts` in `bootstrap`'s order from `TestMemberIDs`, `premises`), `Alloc`
(linkv3's `cluster3_alloc` at the new names), `startMember` (linkv3's proof plus linkv3's `Main`
steps for `v3rpc.Server`/`Listen`/`Serve`/`etcd_kv_started`, now per member: the post carries
`memberUp` and etcd's `Put`/`Range` registered at the member's client address,
`isGrpcRpc clientAddrᵢ … (etcdPutSpec Eᵢ ρᵢ.rd cid midᵢ)`), `Init.lean`/`PkgTable.lean`
(`etc/gen-init.py`, a `PROGRAMS` entry), the `--linkv3p` mode of `etc/gen-link.py`
(`etc/link-lean-first-linkv3p.txt`).

- **`Apply`'s and `Check`'s specs**: linkv's with a list of three clients, each with linkv's
  per-client premises at its member (`isNewClient`, `clientKVOnce`, the two `isGrpcRpc`), and one
  `linkvInv γ k` with `k` every member's KV names: `linkvInv γ γk` reads `γk.st` (through `etcdKV`)
  and `γk.wl`, which the three members' read names share (`etcdKV_congr`, `kvInv_congr`,
  `NewServerAlloc.lean`), so a `linkvInv_congr` lemma (`st` and `wl` equal) states the invariant
  at one member's names for all three. `Apply`'s proof: the pick, then linkv's `Apply.spec` at the
  picked member's `(E, γr, mid)`. `Check`'s proof is linkv's with the new closure.
- **`partitioner`'s spec**: `{{ srvs ↦*□ [s₁, s₂, s₃] ∗ [∗] srvNetMember γn sᵢ idᵢ ∗ sched read-only
  }} … {{ True }}`, a loop over `Sleep` and S2's results, forked with `wp_fork` as `Serve` is.

### S3b. `Main`, the closed theorem, the collection -- done

As planned, with one particular: the closed theorem runs from a fresh state, which holds no
slice, so its program builds the schedule as the slice literal of the quantified list of steps
(`schedLit`: `pure_wp_array_lit_full`, Perennial's one-step lemma for an array literal of values,
and `arrayLiteralSize_vals`, the literal's size is the list's length) before calling `Main`;
nothing but the list's length below `2^63` is assumed of it. The client's watch environment, a
parameter of `clientv3.New`'s spec, is a dummy (`noWatch`): the clients never watch.

`Main.spec` as linkv3's with `sched` and six `netAddrFree`; proof: linkv3's with three serves and
three `New`s, the fork of the partitioner, `linkvInv_alloc_boot`, `Check`. `Adequacy.lean`
(`linkv3p_adequate`: `goose_adequacy_start` with six addresses) and `Results.lean`
(`linkv3p_safe`, `#print axioms`). `etc/tcb-collections/linkv3p.txt`: expected linkv3's 467 plus
the two of S1. The decisive check of the design is that **no raft or server proof changes**
beyond S2: if one did need delivery, it would show here as a stuck proof.

### S4. Gates and notes

`lake build`; `GOTOOLCHAIN=go1.27.1 etc/goose.py --check`; `etc/gen-link.py` for `--server` and
`--linkv3p` (unchanged after linking); `etc/gen-init.py --check`; `etc/tcb-report.py --check`
(+2) and every collection; `go test -race` in `examples/linkv3p`. STATUS entry; a decisions.md
entry recording D-P1–D-P5 and the argument that `Pause`/`Resume` are within the network model.

## Risks and open points

1. **Goose and the type assertion** in `CutPeer`/`MendPeer` (S0, resolved): the pinned translator
   takes it (`TypeAssert2`, as in `applyEntryNormal`'s and the client's); the two bodies are
   translated.
2. **`srvNetMember` reaching the example** (S2, checked): putget3's `memberUp`
   (`Spec/.../putget3/startMember.lean`) does not carry it; its proof has it from `NewServer.spec`
   (it hands it to `RaftHandler`) and drops it. linkv3p's `startMember` returns it beside
   `memberUp` (persistent, so free).
3. **`linkvInv` at three members' names** (S3a): the congruence lemma assumes the three members'
   `KVNames` share `st` and `wl`, which D21 M4's allocation gives (`cluster3_alloc`'s names); if
   another component of `KVNames` is read by `linkvInv`, state the invariant at the cluster's KV
   names instead.
4. **The test's duration**: failed operations wait `ReqTimeout`; keep the schedule's cuts short
   (a few seconds) and `ops` small, or lower `clients`.
5. **Nothing here strengthens the trusted transport model**; it only uses what it already says.
   If the user wants the model's loss to be *visible* in the statement, a follow-up could
   restate `Transport.Start`'s axiom with an explicit adversary (a ghost "link state" the
   schedule sets, and `Send` dropping when the link is down); that would be a restatement, not
   new trust, and the theorem would then mention which links were cut.
