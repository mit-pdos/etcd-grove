# Plan: the partitioned three-member cluster over the KV workload (`examples/linkv3p` × linkvtxn)

Status: done (2026-10-20, branch `linkv3p-txn`, worktree `/shared/etcd-grove-lt`):
`linkv3p_safe` is closed over linkvtxn's workload, its trust base exactly
`etc/tcb-collections/linkv3p.txt` (463 axioms, no `sorry`).

## Goal

`linkv3p_safe` (`Proof/github_com/mit_pdos/etcd_grove/examples/linkv3p/Results.lean`, the partition
plan's S3b) says porcupine never answers `Illegal` for a history of **Puts and Gets** issued at all
three members of a cluster whose links a schedule cuts and mends. Re-close it over **linkvtxn's
workload** (`examples/linkvtxn`, the linkv-txn plan): gets, lists, puts, deletes, multi-operation
transactions and compare-and-sets, robustness's `EtcdPutDeleteLease` traffic without leases and
stale reads, checked against the model of etcd's KV (`linkv/TxnModel.lean`, since 2026-10-22 `linkvtxn/TxnModel.lean`: D34):

> For every `clients`, `ops` and every schedule `sched`, every real execution of `n` steps of
> `linkv3p`'s initialization followed by `Main(clients, ops, sched)` has no stuck thread, no thread
> ended in a panic (so the history of KV operations issued at all three members while the schedule
> cuts and mends their links is linearizable against etcd's KV model), and the main thread's
> result, if any, is `Ok` or `Unknown`.

**Target: on exactly `linkv3p_safe`'s present axioms.** `linkvtxn_safe` rests on exactly
`linkv_safe`'s (`etc/tcb-collections/linkvtxn.txt` equals `linkv.txt`), so swapping the workload
should add none; `etc/tcb-collections/linkv3p.txt` must not change.

Why this one (and not `linkv3` first): it is where the KV API's harder cases are exercised. A
member behind the leader, or a leader cut off by a partition, is where a read could be stale, a
failed delete could take effect after its client gave up, and a transaction could straddle a
leader change. It is also where `issues/etcd-txn-empty-serializable.md` (a compare-only `Txn`
skipping the read index) could actually return a stale answer; the workload keeps such
transactions out (`GenIn`), as `linkvtxn_safe` does.

## In place, not a new example

`linkv3p` switches workload in place (its Go `Apply`/`Check` call package `linkvtxn` instead of
`linkv`), rather than a fourth example `linkv3ptxn`:

- linkvtxn's workload includes linkv's (Puts and Gets are two of its six kinds), so the new
  theorem implies what the old one said;
- everything partition-specific is reused unchanged: `startMember`, `newClient`, `partitioner`,
  the transport axioms, the allocation (`cluster3_alloc`), `Main`'s structure;
- the plain Put/Get examples stay: `linkv` (one member) and `linkv3` (three members, no
  partitions) keep linkv's workload, as the simplest end-to-end results.

The cost: `linkv3p_safe`'s statement keeps its shape but its meaning grows, and the result already
pushed is re-proved. If the old Put/Get partition theorem is wanted beside the new one, the
alternative is a copy (`examples/linkv3ptxn`), roughly doubling `linkv3p`'s 2.7k lines of proof;
not proposed.

## What is already there

- **The workload's proofs are member-generic.** `linkvtxn.Apply.spec` takes one client's premises:
  `isNewClient`, `clientKVOnce`, etcd's `Put`, `Range`, `DeleteRange` and `Txn` registered at its
  endpoint (`etcdTxnSpec E γr γr`), and `linkvtxn.linkvInv γ γr.kv`. Nothing in it says which member
  the endpoint serves.
- **Every member already gets all four registrations.** `startMember` calls
  `client.etcd_kv_started`, which gives `Put`, `Range`, `DeleteRange` and `Txn` (at
  `etcdTxnSpec E ρ.rd ρ.rd`); it keeps the first two and drops the others
  (`startMember.lean`: `with ⟨Hserv, -, #HPut, #HRange, -, -⟩`).
- **The server's read side is member-generic too.** A range's and a read-only transaction's read
  update fires after the read index at whichever member serves the request (`rangeReplyOk`'s and
  `txnReplied`'s `readLogOk`, D21's cluster-level request path); `linkv3p` already runs linkv's
  linearizable Gets at every member.
- **One invariant for three members.** `linkv3p`'s `clientOk` holds linkv's invariant at each
  member's KV names, which agree with the first member's in the state variable and the workload
  (`linkvInv_congr`, `Alloc.lean`, D21 M4). linkvtxn's invariant has the same shape (`etcdKV γk σ`
  inside, `γk.wl.writes` outside), so the same congruence holds of it.

## Stages

### P0. The Go program

`examples/linkv3p/linkv3p.go`: import `examples/linkvtxn` instead of `examples/linkv`; `Apply` is
`linkvtxn.Apply(clis[i], input)`, `Check` runs `lintest.Run(linkvtxn.Model(), apply, linkvtxn.Gen,
...)`; the panic message and the package header updated. `go.mod`: the `linkvtxn` replace and
require in place of linkv's (linkvtxn's own `go.mod` requires `go.etcd.io/etcd/tests/v3` for its
differential test only: check `go mod tidy` does not drag it into linkv3p's build, or keep it out
with the `replace`). `linkv3p_test.go`'s `TestMainRun` (with partition schedules) must pass, and
in reasonable time with the heavier workload; `go test -race`.

Re-translate (`etc/goose.py --project linkv3p`; its `Project` comment names linkv: update it), then
`etc/gen-init.py` (linkv3p's closure now has linkvtxn instead of linkv: `Init.lean`,
`PkgTable.lean` regenerated).

### P1. The members' registrations and `clientOk`

- `memberServed` (`Defs.lean`) keeps `DeleteRange` and `Txn` too; `startMember`'s proof keeps them
  from `etcd_kv_started` (the two `-` become hypotheses); `Main`'s destructurings of the three
  members' results follow.
- `clientOk` becomes linkvtxn's `Apply.spec` premises: the four registrations and
  `linkvtxn.linkvInv γ γr.kv` (`γ : linkvtxn.LinkvNames`).

Done (2026-10-20). Two things moved here: `Base.lean` imports linkvtxn's `Base` (P0 missed it: the
package table's `isPkgInit` of linkvtxn needs it), and `linkvInv_congr` (P2's first bullet) is
ported now, since `startMember` imports `Alloc`. `Defs`, `Alloc`, `startMember` and `PkgTable`
build.

### P2. The invariant at the cluster's start

- `linkvInv_congr` for `linkvtxn.linkvInv` (the same three lines: `linkvInvBody` mentions `γk`
  only through `etcdKV`).
- `Main` allocates the invariant with `linkvtxn.linkvInv_alloc_boot` (`linkvtxn/Boot.lean`: the
  first member's start state, the empty store at revision `1`, good and the model's initial state)
  in place of linkv's, the library state at `linkvState γ (linkv.pInit TS)`.

Done (2026-10-20). `Check.spec`'s statement moved here (its proof stays P3's): `Main` imports it, and
it had to take the new `clientOk` and the library state the allocation gives
(`linkvtxn.linkvState γ (linkv.pInit linkvtxn.TS)`). With it, `Main`'s proof builds unchanged
beyond P1's destructurings and the allocation, so P4's `Main` bullet is done too.

### P3. `Apply` and `Check`

- `linkv3p.Apply.spec`: linkvtxn's triple (`linkvtxn.linkvInOk`, `linkvtxn.linkvState`,
  `linkvtxnS`, mask `linkvtxn.linkvE`) over the client slice; the proof as now, applying
  `linkvtxn.Apply.spec` with the two extra registrations.
- `linkv3p.Check.spec`/proof: `Run` at `linkv.PSet MS MI`, `linkvtxnS`, linkvtxn's `Model` and
  `Gen` (as `linkvtxn/Check.lean`), the clock and the mask lemmas at linkv3p's namespaces.
- `etc/link-lean-first-linkv3p.txt`: `linkvtxn_Apply: @`, `linkvtxn_Model: @`, `linkvtxn_Gen: @`
  in place of linkv's; `etc/gen-link.py --linkv3p` opens `linkvtxn` instead of `linkv`.

Done (2026-10-20). `Apply.spec` also imports linkvtxn's `Calls` (for `linkvInOk`). The full
`lake build` passes; `tcb-report --collection etc/tcb-collections/linkv3p.txt --check` matches
(463 axioms, 0 sorries), as does `--check` against `etc/tcb-baseline.txt`.

### P4. `Main` and the closed theorem

- `Main`'s proof: P1's destructurings, P2's allocation, `Check`'s new spec; the rest unchanged.
- `Adequacy.lean`, `Results.lean`: the statements unchanged in shape; their headers say what the
  workload is now.
- Gates: `lake build`; every `gen-link.py` mode; `gen-init.py --check`; `goose.py --check`;
  `tcb-report.py --check` (521 axioms, 2 sorries) and every collection, **`linkv3p.txt` unchanged**
  (the target); `verified-code.py` (linkv3p's functions verified, linkvtxn's reached).
  STATUS, `decisions.md` (why in place), `partition-plan.md`'s goal paragraph updated.

## Risks and open questions

- **The read path at a member that is behind.** The server's specs are member-generic and
  `linkv3p` already relies on them for Gets; lists use the same `Range`, and a read-only `Txn`
  takes the same read index (`etcd_txnHandlerOk`'s read-only case). Expected: no new server
  proof. If a read-only transaction's path at a follower turns out to differ (it should not: the
  read index is cluster-level since D21), that is the one place new server work could appear.
- **The test's running time.** Transactions and lists are heavier than Puts and Gets, and
  partitions make some calls time out (one attempt each); `TestMainRun`'s sizes may need tuning
  for CI. The theorem quantifies over `clients` and `ops`; only the test's constants change.
- **The model under partitions.** Nothing changes in it: failed writes are pending and may take
  effect late (a cut-off member's proposal committed after the client's error), exactly the case
  `PendModel.lean`'s closure covers; failed reads constrain nothing.

## Sizing (rough)

Small. P0 is a few lines of Go and the regenerations; P1–P4 are edits of existing proofs (most of
`linkv3p`'s 2.7k lines unchanged: `startMember`, `partitioner`, `newClient`, `Alloc`, most of
`Main`), with no new spec of etcd's code. The one real unknown is the risk above, which an early
build of P3 against the unchanged server specs settles.
