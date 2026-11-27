# Review of option (D): restart restores raft's position from the backend

For coordinator-E / etcd-grove-03, 2026-11-27. The review read the fork `goose-lean-discardfix-ttlkeys-keepfix`
(`/shared/etcd-fork-keepfix`, head a453b08a1 on the pin 30df685e4) and raft v3.7.0 from the module cache.
Line numbers are at a453b08a1. A WAL-level prototype test is kept at `/shared/tmp/coord-03/optD_wal_test.go`.
It ran in package `server/storage/wal` at 30df685e4 and passes. The scratch worktree has been removed.

## Verdict

(D) is sound in principle, and it closes the gap at its root. The gap exists only after a restart: at
run time, raft's in-memory `committed` is at least the backend's `ci`, because only committed entries
are applied. raft's `restore` (`raft.go:1861`) already refuses every snapshot at or below `committed`. If
restart sets `committed = ci`, the keep guard has nothing left to do. It also makes the premise of the
existing restart contract true by construction: that contract says the backend prefix ends at or below
the recovered commit (`notes/snapguard-removal-plan.md`).

**But (D) as written ("snapshot record, then a HardState with Commit = ci") is wrong on this fork in one
case, and needs three fixes:**

1. **Split it into two branches.** The fork's `ReadAll` treats a start snapshot record that lies above
   the commit in force at that record as a snapshot raft received. It then drops every entry above it
   (`wal.go:565-569`, `:663-666`, from ce3dbc097). (D) writes the record before its HardState, so the
   WAL's entries in `(ci, L]` are lost on the next read (`L` is the WAL's last index). I confirmed this in
   the prototype. Those entries may have been acknowledged to a leader, so dropping them is a raft
   safety violation. The fix: when the WAL already holds the committed entry at `ci`, write no snapshot
   record and only raise the commit. See "Exact values".
2. **Do not trust the backend's term key as it is.** `cindex` keeps the index and the term in two
   separate atomics (`cindex.go:112-121`). `applyEntryNormal` sets them outside the batch-tx lock: the
   deferred `SetConsistentIndex` at `server.go:2037`, taken for every entry that applies with no txn,
   including the empty first entry of each term. Meanwhile the backend's periodic commit runs
   `UnsafeSave` → `UnsafeUpdateConsistentIndex` (`hooks.go:46`, `schema/cindex.go:69-94`), which loads
   the two atomics separately. So a commit can persist the new index with the old term, or the old index
   with the new term, exactly at a term boundary. A crash within 100 ms of that keeps the torn pair.
   Make the pair a single atomic (one mutex, or a pointer to an `{index, term}` struct) before (D) relies
   on it.
3. **Call `w.Sync()` explicitly after the HardState.** `WAL.Save` syncs only when `raft.MustSync` says
   so (`wal.go:1349`, `:1376`), and a change to `Commit` alone does not count. The snapshot record syncs
   itself (`SaveSnapshot` → `w.sync()`, `wal.go:1423`).

With those three fixes, (D) works and the keep guard (8aa40fd5c/47d6cdeeb + a453b08a1) can be
reverted.

## 1. The term at ci

- **Where it comes from.** It is the meta key `term` (`schema/bucket.go:88`). It is written by
  `unsafeUpdateConsistentIndex` from `ci.term` when that term is greater than 0 (`schema/cindex.go:89-94`).
  `ci.term` is the entry's term, never the applier's: `SetConsistentApplyingIndex(e.Index, e.Term)`
  (`server.go:1998`), then the post-lock hook (`server.go:2540-2542`), the empty or no-txn path
  (`:2037`), or a failed conf change (`:2103`). A backend installed from a leader snapshot carries the
  leader's `(ci, term)` pair. `etcdutl` restore writes `(commit, term)` consistently
  (`v3_snapshot.go:584`).
- **When it can differ from term(ci).**
  - (a) The torn pair described in fix 2.
  - (b) `term = 0` on a pre-3.5 backend, or on one that never stored a term. `createMergedSnapshotMessage`
    already falls back for this case (`snapshot_merge.go:52-54`).
  - (c) None otherwise. Committed entries are immutable.
- **What a wrong term does.**
  - **Too low** (new index, old term). The leader's `MsgApp` with `prev = (ci, term(ci))` is rejected.
    Probes below `ci` come back as acknowledgements of `committed` (raft's
    `m.Index < committed` branch). So the leader loops: it acknowledges, sends, and is rejected again. It
    gets out only through a snapshot above `ci`. This is a liveness failure, not a safety one.
  - **Too high** (old index `ci-1`, new term). The node advertises `lastTerm` above its real last term.
    That breaks the invariant `lastTerm ≤ the real log's term` on which the up-to-date check rests. In
    this shape (understated by one index, at a term boundary) a majority holding the committed entry
    `ci` still refuses its vote, but I would not want to prove that special case.
- **Rule for (D).** Require `term_be > 0` and an atomic pair (fix 2). When `ci ≤ L`, also compare with
  the WAL entry's term (next section).

## 2 and 3. Exact values to write

Let `(Term_w, Vote_w, Commit_w)` be the WAL's HardState, `L` the WAL's last index, `t` the backend
term, and `CS` = `confStateFromMembers` of the backend's members, which bootstrap already uses
(`bootstrap.go:133-141`). Run (D) only when `ci > Commit_w`. Otherwise raft already refuses every
snapshot at or below `ci`.

**Branch A: `ci ≤ L` and the WAL entry at `ci` has term `t`.** Write `HardState{Term_w, Vote_w,
Commit: ci}`, then `Sync`. Write no snapshot record.
- By Log Matching, the WAL prefix through `ci` is the committed log, so raising the commit over it is
  sound.
- `loadState` accepts it: `committed ≤ ci ≤ L` (`raft.go:2038`).
- `Term_w` is already at least the term of every WAL entry.
- The entries in `(ci, L]` are kept, as they must be.
- Entries `≤ ci` are still replayed v2-only, as today. That is harmless: membership comes from the
  backend (`cluster.go:255-262`).
- This is upstream's `--force-new-cluster` fix (`bootstrap.go:683-694`, raft#300) with a term check
  added.

**Branch B: `ci > L`, or the WAL entry at `ci` has another term (a divergent tail the crash kept).**
Write, in this order:
1. `SaveSnapshot{Index: ci, Term: t, ConfState: CS}` (it syncs itself);
2. `Save(HardState{Term: max(Term_w, t), Vote: Term_w ≥ t ? Vote_w : 0, Commit: ci}, nil)`;
3. `Sync()`.

Why these values:
- **Commit = ci.** raft's log becomes the empty log at `ci`, with `committed = applied = firstIndex - 1 =
  ci` (`log.go:93-96`).
- **Term must be at least `t`.** raft never checks it: `loadState` copies `Term` and `Vote` blindly. But
  with `lastTerm = t > r.Term`, a campaign at `Term_w + 1 ≤ t` can win a second election in term `t`.
  Followers of term `t` have `Vote = None`, and after a restart their `lead` is `None` too, so they can
  grant the vote. The result is two leaders in one term.
- **Raising the term with Vote = 0 is safe.** The node did receive a message from term `t` or later
  (it applied an entry of term `t`). A vote it actually sent was saved before it was sent, so `Term_w`
  would already be at least `t`.
- **Keep `Vote_w` whenever `Term_w ≥ t`.** Otherwise the node could vote twice in `Term_w`.
- **ConfState.** Etcd uses only v1 conf changes, so members give voters and learners exactly
  (`bootstrap.go:163-180`). Members and `ci` are written in the same batch tx under the apply lock. Use
  the members, not the meta `confState` key: the keep guard's gap can leave that key stale.
- **Entries.** The fork's `ReadAll` drops every WAL entry at the new start record. That is right here:
  all of them are at or below `L < ci`, or they extend a divergent entry at `ci` and so can never be
  committed.
- **Membership above L.** The entries in `(L, ci]` were never in this WAL. The backend holds their
  effects, and raft's configuration (`CS`) and the backend agree at `ci`.

**After the write,** reopen through `openWALFromSnapshot` at the new start, or recompute the same
values. That way raft's `MemoryStorage` (`bootstrap.go:795-806`) is exactly what disk will give back.
`RecoverSnapshotBackend` then skips loading a snapshot backend (`storage/backend.go:118`, because
`ci ≥ index`), and the `kvindex < snapshot` check (`bootstrap.go:543`) passes.

## 4. Crash points (prototype: `TestOptDBackendAhead`, `TestOptDCrashBeforeState`, `TestOptDEntriesAboveCi`)

| Crash after | Next restart reads | Outcome |
|---|---|---|
| nothing written | old snapshot and old HardState | (D) runs again |
| B: snapshot record (synced), no HardState | `ValidSnapshotEntries` filters the record out (`ci > Commit_w`, `wal.go:972-980`); `ReadAll` from the old start ignores a record that is not the start | as before (D); (D) runs again (tested) |
| B: snapshot record + torn HardState record | as the previous row: the torn tail is repaired or cut and the last valid state is `Commit_w` | (D) runs again |
| B: both records, unsynced, or partly on disk | the same two rows, depending on how much survived | idempotent |
| B: both synced | start `ci`, commit `ci`, no entries | done (tested); the next restart skips (D) because `ci ≤ Commit` |
| A: HardState not durable | old HardState | (D) runs again |
| A: HardState durable | commit `ci`, entries kept | done (tested) |

The order matters. In B the HardState must not come first: a commit `ci > L` with no record makes
`loadState` panic (`commit out of range`). In A no record is written at all. `MemoryStorage` is in
memory only, so a crash there loses nothing.

**The torn-Save fix (49bf5160f).** It cuts trailing entry records before (D) writes, because (D) runs
after the write-mode `ReadAll`. So (D)'s records cannot turn an interrupted Save's tail into "followed by
a record". Keep (D) after `ReadAll` on the same `*WAL`.

## 5. Leader snapshots at or below ci afterwards

- `restore` returns false for `Index ≤ committed = ci` (`raft.go:1861`).
- `handleSnapshot` then replies `MsgAppResp{Index: committed}`. The prototype checks this: a snapshot at
  6 is refused and `MsgAppResp` 7 is sent without a reject.
- The leader takes it as `Match = ci` and probes from `ci + 1`.
- If the leader's log is compacted past `ci + 1`, it sends another merged snapshot at `max(applied,
  ci_L)`. Its apply loop catches up to its commit (which is at least `ci`), so the loop ends with a
  snapshot above `ci`. This is a liveness delay only, and the same holds on today's code.
- Each refused snapshot leaves its received `.snap.db` file behind. `ReleaseSnapDBs` removes it at the
  next snapshot.
- At run time, raft's `committed` never falls below `ci`, so the refusal holds for the whole process.

## 6. Other users of the WAL snapshot index

- `ep` (`server.go:807-814`): `appliedi`, `appliedt`, `diskSnapshotIndex`, `memorySnapshotIndex`,
  `confState` and `replayConf` become `ci`, `t` and `CS`, which is consistent. The first applied
  `Ready` starts at `ci + 1`.
- `replayTerms` (`snapshot_terms.go`) covers only entries. With branch B it is empty and
  `createMergedSnapshotMessage` takes the backend branch, where `ci == snapi`, so no override happens.
  Use the atomic pair there too.
- Snapshot trigger (`appliedi - snapi > SnapshotCount`), `CreateSnapshot` (returns `ErrSnapOutOfDate`
  when the index is at or below the snapshot) and `raftStorage.Compact` (`ErrCompacted`) are all fine:
  they behave the same as after a normal restart from a WAL snapshot record.
- This fork writes no `.snap` files (`storage.go:59-70`). Nothing else assumes a v2 snapshot exists at
  the WAL snapshot's index. The only snapshot backend file opened is `<index>.snap.db`, and only when
  `index > ci`, which never happens here.
- WAL purge (`ReleaseLockTo`) is unchanged. `SaveSnapshot` raises `enti` to `ci`, so later files are named
  above it (`wal.go:1409`).
- Not new: a member that was removed in `(L, ci]` gets a `CS` without itself. Bootstrap already builds
  `CS` from the members.

## 7. (D) versus (C), persist-before-apply

- **(C) alone** moves `applyAll`'s `<-notifyc` (`server.go:995`) before the apply, with the matching
  change in `raft.go:276-319`. It gives `ci ≤ L`, and the WAL entry at `ci` is the applied one. But it
  does not give `ci ≤ Commit_w`: a commit-only HardState is never fsynced. So the restart still sees
  snapshots `k ∈ (Commit_w, ci]`. raft then refuses them only through `restore`'s `matchTerm`
  fast-forward (`raft.go:1911-1918`), and the proof would have to carry that path.
- **(C) plus branch A** (raise the commit to `ci` at boot, checked against the WAL's own entry term)
  needs no backend term and no snapshot record. Its only crash case is one HardState write, and it
  establishes the existing restart premise `ci ≤ recovered commit`.
- **(D) in full** needs:
  - a cindex invariant tying the persisted term to `term(ci)` of the committed log. Today
    `InvCindex.lean:134` has `ciTermAddr ↦ t` with `t` free, and the Go race shows the code does not
    maintain such a pair;
  - members-to-ConfState equality at `ci`;
  - a two-record crash argument that goes through the fork's `ReadAll` record semantics.

My estimate is that **(C) plus branch A is the smaller proof**. Its cost is a latency cost: a follower,
and also the leader, which self-acknowledges before its fsync, applies only after the fsync. (D) plus
the atomic pair avoids that cost, at the price of the backend-term ghost.

## Upstream-relevant observations

- **The torn `(consistent_index, term)` pair** (`cindex.go:112-121` against the unlocked
  `SetConsistentIndex` at `server.go:2037`) is upstream code. It is a candidate `nonissues/` entry, or an
  `issues/` entry if a test reaches it: the term is read by snapshot creation and `etcdutl`.
- **Branch A is a natural upstream fix for #22028** (ci above the HardState commit): `max(Commit, ci)`
  on every restart, not only with `--force-new-cluster`, once the WAL entry's term has been checked
  against the backend's term.
- **Raising the commit at boot is a separate change from upstream `ReadAll`.** Upstream `ReadAll` does
  not drop entries at a snapshot record; the fork does (ce3dbc097). Any port of branch B has to state
  which `ReadAll` it assumes.
