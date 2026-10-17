# etcd-io/raft#37: Allow applying entries on durable remote quorum

- PR: https://github.com/etcd-io/raft/pull/37 (tbg, open, a prototype "not with an intention to
  merge"), head `f353149418c6e01e4c7e34e7c1f35a3d8ad013e9`, base on upstream `main` `f261acac4`.
- Verified at: `mit-pdos/etcd-grove` branch `pr-raft-37-goose-lean`, commit `b0e4435b4`. That is
  the PR's non-test diff applied onto the pinned raft fork `509271dac` (raft v3.7 + the read-index
  fix, protobuf-go v2 raftpb).
- This repository: branch `pr-verify/raft-37` (off `lean` `51547df02`).

## Verdict

**Inside the verified scope the PR changes nothing, and that is proved.** The proofs cover a
`RawNode` with synchronous storage writes (`AsyncStorageWrites` unset). There:

- `validate` forces the new option off;
- `applyUnstableEntries()` is `true` as before;
- every existing spec of the changed functions and their callers still holds;
- the trust base is unchanged.

The one spec change is `Config.validate`'s new error case, which appears as a new conjunct of
its precondition `ConfigValid`. Each caller of `NewRawNode` up to the exported results either
already passes it as a premise or discharges it (the example's literal config).

**The feature itself is not verified.** The feature is applying committed entries that are not
yet durable locally, in async mode, and asynchronous storage writes are outside the proof. A
manual review of the async path found no safety problem: an entry handed out for application is
committed, so it is never truncated or replaced (`maybeAppend` panics on a conflict at or below
`committed`, and `restore` refuses one).

It did find two hazards the PR leaves undocumented. Both are shown by Go tests at the PR head:

- **The applied index can pass the node's durable last index.** Restarting with that
  `Config.Applied` panics, and `MemoryStorage.CreateSnapshot`/`Compact` at the applied index
  panic.
- **Followers apply unstable entries too.** The option's doc says "on the leader".

The reviewer also found a related restart panic that predates the PR, in plain async mode. It is
recorded in `issues/`.

## Applying the PR

- **Conflict:** only `rafttest/interaction_env_handler_add_nodes.go`, a test harness that is not
  translated. The PR's new `case` is added after the base's extra cases (`prevote`,
  `checkquorum`, ...).
- **Rewritten:** the PR's `testdata/async_storage_writes_apply_nonlocally_committed.txt`, put in
  the base's datadriven output format with `-rewrite`. The base prints `ok` for a quiet
  `stabilize` where the PR's base printed `ok (quiet)`, and prints `Responses:[...]` on several
  lines. The two versions differ in no other way, and the same entries and messages come out.
- **Re-translation:** `etc/goose.py --project raft --src raft=~/etcd-pr/raft-37` regenerated the
  translation. The diff is the new `validate` branch, the new `NewRawNode` store, the new
  `applyUnstableEntries` body and the two struct fields. `etc/goose.py --check` fails on this
  branch by design, because the pin is left alone.
- **Tests:** `go build ./...` and `go test ./...` pass in the fork worktree.

The verified code differs from the PR only in the protobuf-go v2 style the fork already has. The
PR touches no message code.

## Changed functions

Changed types: `Config` gains `AsyncStorageWritesNonLocalQuorum`, and `RawNode` gains
`asyncStorageWritesNonLocalQuorum`. Neither field is constrained by any invariant.

| Function | Kind | Before (`lean`) | After | Outcome |
|---|---|---|---|---|
| `Config.validate` | behavior change: a new error | verified | verified | new spec: one more conjunct in the precondition `ConfigValid`. Incompatible in form, so callers were checked (below) |
| `NewRawNode` | behavior change: records the new field | verified | verified | old spec re-proved, unchanged |
| `RawNode.applyUnstableEntries` | behavior change | translated (no spec; inlined in its three callers' proofs) | translated, inlined | the callers' proofs: with `asyncStorageWrites = false` it short-circuits to `true` |
| `RawNode.readyWithoutAccept` (caller) | unchanged code | verified | verified | old spec re-proved (one `wp_auto`) |
| `RawNode.HasReady` (caller) | unchanged code | verified | verified | old spec re-proved (one `wp_auto`) |
| `RawNode.acceptReady` (caller) | unchanged code | verified | verified | old spec re-proved (one `wp_auto`) |
| `rafttest.handleAddNodes` | test harness | not translated | not translated | out of scope |

`etc/verified-code.py --functions --package go.etcd.io/raft/v3` reports the same states before and
after: 260 of 327 functions verified, all sorry-free. The script reads the Go source at the pin,
so it does not count the PR's dozen added lines.

### `Config.validate`

- **Old spec:** with `ConfigValid cv`, `validate` returns `nil` and preserves the fields in
  `ConfigPreserved`.
- **New spec:** the same, with `ConfigValid` extended by `cv.AsyncStorageWrites' = true ∨
  cv.AsyncStorageWritesNonLocalQuorum' = false`. That is the negation of the Go check, and the
  conjunct is in `Spec/go_etcd_io/raft/v3/Config__validate.lean`.
- **Proof:** `Proof/go_etcd_io/raft/v3/Config__validate.lean`.

`ConfigPreserved` does not mention the new field. `validate` does not write it, and no proof
needs its value after `validate`.

### `RawNode` state

`rawNodeOwn` (`Proof/go_etcd_io/raft/v3/InvRawnode.lean`) gains a points-to for
`asyncStorageWritesNonLocalQuorum`, with no constraint, plus load and store `AccessStrict`
instances. The field is read only when `asyncStorageWrites` is set, and every `RawNode`
invariant has `asyncStorageWrites' = false`. Nothing else in the package reads either field
(`node.go` reads only `asyncStorageWrites`).

## Callers of the changed spec (step 6)

Before the change, `ConfigValid` appeared in the following places. Each one now reads the
extended definition:

- **Premises, unchanged in text:** the specs of `newRaft`, `NewRawNode`, `RestartNode`,
  `StartNode` and `setupNode`; the etcd server's `bootstrappedRaft.newRaftNode` spec
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedRaft__newRaftNode.lean`); and
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/NodeStart.lean`.
- **Discharged:** `nodeConfig_valid` in `Proof/github_com/mit_pdos/etcd_grove/examples/register/Main.lean`.
  Its literal config gains `AsyncStorageWritesNonLocalQuorum' := false`, and the existing
  `simp; decide` proves the new conjunct.

Every one of these premises also requires `AsyncStorageWrites' = false`, so the new conjunct
amounts to "the option is unset", which is what etcd's `raftConfig` leaves it. The chain ends at
exported results:

- `server_raft_node_start`;
- the register example's `register_cluster_safe`.

A full `lake build` passes: 5104 jobs, every `Link`/`Results`.

## Trust base (step 7)

- `etc/tcb-report.py --check`: the trust base matches `etc/tcb-baseline.txt` (229 axioms, 12
  `sorry`s). No axiom or `sorry` was added or removed.
- New collection `etc/tcb-collections/pr-raft-37.txt`: 49 roots (`validate`, `newRaft`,
  `NewRawNode`, `Ready`/`readyWithoutAccept`/`HasReady`/`acceptReady`,
  `StartNode`/`RestartNode`/`setupNode`, the server's `newRaftNode`, the register example).
  - They rest on 13 of this repository's existing axioms.
  - 48 of the 49 reach no `sorry`. The exception is `register_cluster_safe`, which reaches the 10
    package-initialisation `sorry`s it already reached on `lean`.
- No postulate was added.

## Findings (step 8)

The tests are in `notes/pr-verify/raft-37/` (see its `README.md`).

1. **With the option, the applied index can pass the node's durable log, and restart then
   panics** (in the PR; a hazard, not a safety bug).
   - **Setup:** a leader whose append thread stalls proposes entry 12; nodes 2 and 3 persist it,
     and the leader applies it.
   - **State:** its durable log ends at 11 and its durable commit is 11.
   - **Restart:** `NewRawNode` with `Config.Applied = 12` panics with "applied(12) is out of
     range [prevApplied(10), committed(11)]".
   - **Test:** `TestNonLocalQuorumRestartAboveDurableLog`.

   Restarting with a lower `Applied` re-delivers entries the state machine already holds. The
   part that is new with the option is "applied above the durable last index". Plain async mode
   already allows applied above the durable commit (finding 4).
2. **Applying above the local last index breaks snapshotting and compacting at the applied index**
   (reviewer; in the PR). `MemoryStorage.CreateSnapshot(12)` panics with "snapshot 12 is out of
   bound lastindex(11)", and `Compact(12)` panics too. The test is
   `TestReviewNLQSnapshotAboveDurableLog`. The PR's description touches on this ("log
   truncation via a side effect of applying an entry"), but its API doc does not state the
   constraint.
3. **The option is not limited to the leader** (in the PR; documentation).
   - **The doc** says "AsyncStorageWritesNonLocalQuorum, on the leader, emits entries ...".
   - **The code:** `applyUnstableEntries` holds on every node.
   - **Test:** `TestNonLocalQuorumFollowerAppliesUnstable` shows a follower with a stalled disk
     applying an entry that is only in its unstable log.
   - **Safety:** it is safe, because a follower's `committed` only covers entries matching the
     leader's log. But the doc is inaccurate, and finding 1 applies to followers too.
4. **Plain `AsyncStorageWrites` can apply past the durable commit, and restart with that
   `Applied` panics** (existing code, reviewer).
   - **How:** the `HardState` and the committed entries go to different threads, which may run
     "in any order" (`doc.go`).
   - **What it breaks:** `Config.Applied`'s documentation does not say it must not exceed the
     durable `HardState.Commit`.
   - **Recorded** in `issues/raft-async-applied-above-durable-commit.md`, with a reproduction
     against the pinned fork (`issues/raft-async-applied-above-durable-commit/`).

No bug was found in this repository's specs or proofs.

The reviewer confirmed the following, and it has no open points:

- the new conjunct is exactly the Go check;
- the in-scope proofs changed nothing else;
- the async path is safe with respect to truncation, `stableTo`, `acceptApplying`/`appliedTo`
  and the size limits.

## Draft review comment (for the user to edit and post)

> I looked at this with synchronous writes and with async writes. With `AsyncStorageWrites` off,
> `validate` rejects the new option and `applyUnstableEntries()` is unchanged, so there is no
> behavior change there. With it on, I didn't find a safety problem: entries are only handed out
> once committed, and committed entries are never truncated. A few things the API should
> probably say, though:
>
> 1. With the option set, a node can apply an entry its own disk doesn't have yet. If it crashes
>    then, the state machine's applied index is above the durable raft log. Restarting with
>    `Config.Applied` set to it panics in `NewRawNode` ("applied(12) is out of range
>    [prevApplied(10), committed(11)]"), and restarting with a lower one re-delivers applied
>    entries.
> 2. For the same reason, `MemoryStorage.CreateSnapshot(applied)` / `Compact(applied)` panic,
>    because the index is past `LastIndex()`. Applications that snapshot at the applied index
>    need to clamp to the durable log.
> 3. The doc comment says "on the leader", but followers with a lagging disk also apply entries
>    from their unstable log (safe, since they're committed, but with the same restart caveat).
>
> Item 1 is partly pre-existing: with plain async writes the applied index can already pass the
> durable `HardState.Commit` (the append and apply threads are unordered), so the same restart
> panic exists today. It might be worth documenting on `Config.Applied` either way.
>
> I have tests for all three if useful.
