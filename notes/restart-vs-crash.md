# Process restart vs machine crash: what the "restart = crash after sync" assumption hides

**Date:** 2026-11-06. **Status:** analysis (read-only), for the decision in `notes/fs-semantics-v2.md`,
"Restarts are machine crashes". Code read: etcd at `/tmp/fkd-review/etcd` (`ce3dbc0`, the fork's
`goose-lean` line), raft v3.7.0 and bbolt v1.5.0 from the Go module cache. Line numbers are of those
trees (`wal.go` is `server/storage/wal/wal.go`, `raft.go` without a directory is raft's).

## Summary

The assumption is needed for etcd, and etcd is (narrowly) buggy without it. etcd syncs nothing at
boot: `wal.Open`/`ReadAll` read the last segment from the page cache, never fsync it or the WAL
directory, and `ReadAll` sets the WAL's notion of the saved hard state (`w.state`) and raft's
storage from what it read. Within the last segment this is mostly harmless, because every later
`fdatasync` of the segment writes generation 1's dirty pages too, and generation 1's unsynced data
can only be in that segment (`cut` syncs the old tail before it switches, `wal.go:814-818`). It goes
wrong where generation 2 acts on what it read before its first sync of that segment, or acts on
another file. Three such paths exist. (1) **Acks without a sync**: a restarted follower answers a
`MsgApp` whose entries it already "has" (read from the page cache) with a `MsgAppResp`, and raft's
`MustSync` is false because nothing new is appended, so `wal.Save` returns without `fdatasync`.
The leader then counts entries that are not durable on that follower: after a power loss the
follower has lost entries below the leader's `Match` (raft then panics on the next heartbeat,
"tocommit out of range", and an entry committed on that ack can be lost with one more failure).
(2) **Purge on a non-durable snapshot record**: generation 2 opens the WAL at the newest snapshot
record it sees, which can be page-cache-only; it locks only the segments from there on, and the
purge loop deletes the older ones; a power loss then leaves a WAL whose durable snapshot records
point into deleted segments, and the member cannot start. (3) **bbolt page reuse on a non-durable
commit**: bbolt opens at a meta page that may be page-cache-only and its first commit reuses pages
that commit freed; a power loss during that commit's `fdatasync` can leave the older (durable) meta
pointing at overwritten pages, a corrupt database. Under a strict POSIX directory model (the one
our model uses: a file `fsync` commits no name), the unsynced renames of `wal.Create` and `cut` are
a fourth path; on ext4/xfs the global journal makes it harmless. All windows are short (from the
restart to the next sync, bounded in practice by writeback, ~30 s by default) and need a kill at a
specific point followed by a power loss, so these are real but narrow. With the assumption (a
restart only after a machine restart, or after `sync(2)` of what the old process left dirty) none of
them can happen, and the model's choice is sound for etcd; without it the proofs would be proving
something false.

## General patterns

Setting: generation 1 (G1) leaves dirty state D (file data not yet `fdatasync`ed, metadata
operations not yet committed by the journal) and dies; the kernel keeps running; generation 2 (G2)
starts on the page cache, which shows D; later, before D is written back, the machine loses power,
and generation 3 (G3) starts on the disk.

Under machine crashes only, every generation starts on a disk state, and anything a generation
reads is as durable as the disk it read. Under a process restart, G2 reads D but D is not durable.
A behaviour is correct under every machine crash but wrong under restart-then-power-loss exactly
when **G2 makes an externally visible or persistent commitment that depends on D, and makes it
durable (or visible) before D itself is durable**. Conditions:

1. G2 reads D (directly, or through a derived decision: an offset, a choice of file, an index).
2. G2 treats it as durable: it does not issue a sync that would cover D before the commitment. A
   sync that covers D is: `fsync`/`fdatasync` of the file D lives in (it writes *all* dirty pages of
   the file, G1's included); for a directory entry, `fsync` of its directory (on ext4/xfs, any
   journal commit after it: a later `fsync` of anything that forces a commit, or the 5 s periodic
   commit).
3. The commitment is one of: a message or reply (ack, vote, client reply), a write to *another*
   file made durable (or visible to others), a deletion/overwrite/reuse of something D's
   durability would have kept needed, or a metadata change that becomes durable on its own.
4. A power loss between the commitment and D's durability; the disk then holds the commitment
   without D, a state no crash-only history produces.

Distinct patterns:

- **P1, read-then-acknowledge.** G2 reads a record G1 wrote but did not sync and acknowledges it
  (to a client, a peer, a quorum) without syncing, typically because "nothing changed" (the record
  is already there, the protocol says the write is a no-op). The ack implied durability.
- **P2, cross-file dependency.** G2 writes and syncs file B whose contents refer to or presume D in
  file A (an index into A, a checkpoint that "includes" A's records, a manifest naming A's state)
  but never syncs A. Same-file dependencies are safe because one `fdatasync` writes all of the file.
- **P3, deletion or reuse justified by D.** G2 frees, deletes, truncates or overwrites something
  because D supersedes it (an older segment or snapshot purged because a newer checkpoint is in D;
  pages reused because D's commit freed them; a log compacted because D records the snapshot). The
  freeing reaches the disk (journal commit, writeback of the overwrite) before D. The overwrite case
  needs no metadata: two dirty pages of one file reach the disk in any order before the flush.
- **P4, unsynced directory entries.** G1 created or renamed a file or directory and died before
  `fsync` of the parent; G2 resolves the name, finds it, and builds on the file (writes and
  `fdatasync`s it). `fdatasync` of the file does not persist its name (POSIX; our model), so a power
  loss can leave G2's synced data under the old name or no name. On ext4/xfs a journal commit after
  the rename (the next `fsync` that commits, or 5 s) makes it durable, ordered before later ops.
- **P5, "already done, skip".** G2 checks for the result of a step (a file exists, a marker is
  set, a record is present) and skips the step, including its sync. Special case of P1/P4: the
  check must be "exists *durably*", so the skip path must still sync. (etcd already fixed one:
  `SaveDBFrom`, below.)
- **P6, repair or truncation of a tail seen only in the page cache.** G2 decides from the page cache
  where the valid prefix ends and truncates/zeroes the rest. Safe if the repair `fsync`s the file
  (that writes D and the truncation together) before anything depends on the repaired state;
  unsafe if the repair is left dirty and G2 then acts on the repaired state elsewhere (P2/P3).
- **P7, zero/preallocation assumptions.** G2 assumes "beyond my last valid record the file reads
  zero" from the page cache; the disk can hold an older or partial version there. Safe when the
  reader on the disk state (G3) tolerates any mix of versions of unsynced sectors, which a
  crash-only design must already tolerate; only harmful when combined with P1-P3.
- **P8, locks and process-held state.** Locks held by an fd (`flock`, OFD locks) vanish with G1 in
  both models; what changes is that G2 reconstructs *which* files to lock from D. If locks protect
  files from a purger, the lock set derived from D can release files the durable state still needs
  (a P3 instance).
- **P9, protocol state recovered from D.** G2's "previous persisted state" (raft's `HardState`,
  a sequence or ID counter, a fencing epoch) is taken from D, so G2's later "did it change? then
  sync" check compares against a non-durable baseline and skips syncs (P1's mechanism). A counter
  read from D and reissued after a power loss reuses values.

**The converse class** (safe under a process restart, wrong under a machine crash) is everything
that relies on the page cache or on the kernel staying up: no syncs at all (`--unsafe-no-fsync`),
ordering writes across files without syncs, state in tmpfs or `/dev/shm`, `CLOCK_MONOTONIC` or
boot-time-based values across generations, child processes or other processes' fds outliving the
program. A crash-correct proof covers none of these as safe, so it does not matter here.

## etcd WAL analysis

Facts used throughout:

- `Save` (`wal.go:1017-1059`) returns without writing anything when the hard state is empty and
  there are no entries (`:1022`), and syncs only when `raft.MustSync(st, w.state, len(ents))`
  (`:1032`, raft `rawnode.go:191-198`: entries, or a changed term or vote). A commit-only change
  is written and not synced.
- `ReadAll` sets `w.state` to the hard state it read (`wal.go:596`), and the server loads raft's
  `MemoryStorage` with that hard state and the entries read (`bootstrap.go`, `MemoryStorage`), so
  raft's `prevHardSt` and its "stable" log are G1's page cache.
- The follower raft loop sends its messages after `storage.Save` returns (`etcdserver/raft.go:264`,
  `:329`); the leader sends in parallel (`:250`).
- G1's unsynced WAL data is only ever in the last segment (or in a not-yet-renamed `N.tmp`): `cut`
  truncates and `fdatasync`s the old tail before it opens the next file (`wal.go:814-818`), and every
  other write is to the tail.

### Q1: does G2 read page-cache-only records at Open/ReadAll and rely on their durability?

Yes. `openAtIndex`/`ReadAll` (`wal.go:369-617`) read through the page cache; there is no `fsync` or
`fdatasync` at open (only `fileutil.OpenDir` of the WAL directory, `:356`, kept for `cut`).
`ReadAll`'s tail handling (`:580-585`, `ZeroToEnd`) truncates and re-extends the tail beyond the
last valid record, also unsynced. Nothing at boot syncs: `bootstrapWALFromSnapshot` saves only for
`--force-new-cluster` (`bootstrap.go:640-646`, a `Save` with entries, which does sync). The first
sync after a restart is the first `Save` with entries or a term/vote change, or a `SaveSnapshot`.

What G2 does with the records before that sync:

**(a) Acks of entries it read: P1/P9, real risk.** Raft's follower path acknowledges without
appending in two cases: `handleAppendEntries` answers `MsgAppResp{Index: committed}` when the
message is below the commit index (`raft.go:1796-1798`), and `maybeAppend` returns
`lastnewi = prev + len(entries)` and acks it when the entries match the log, appending nothing
(`log.go:109-131`, `raft.go:1800-1802`). With nothing appended and the term and vote unchanged,
`MustSync` is false and `wal.Save` does not sync (a commit advance is saved unsynced), and the
follower then sends the ack (`etcdserver/raft.go:264`, `:329`).

Execution (3 voters L, F, G; G lagging or down):
1. L appends entry *i* (term *t*), sends `MsgApp[i]` to F. F (G1) writes *i* into its last segment
   (`encoder.flush` in `wal.sync`, `wal.go:892-896`) and is killed before `Fdatasync` (`:903`). No
   ack was sent.
2. F restarts (G2) with *i* in its log, read from the page cache. L had F in `StateReplicate`
   with `Next = i+1`. On F's next heartbeat response, L calls `sendAppend` (`raft.go:1596-1597`)
   with `sendIfEmpty`: if L has nothing past *i*, the `MsgApp` is `{Index: i, LogTerm: t, Entries:
   []}` (`raft.go:618-660`); if the transport reported F unreachable, L probes from `Match+1` and
   resends *i*. Either way F matches, appends nothing, and acks *i* without a sync.
3. L sets `Match(F) = i` and commits *i* on {L, F}; the client is answered.
4. Power loss at F before F's next sync (an idle follower may see only heartbeats and commit-only
   saves for a long time; the kernel's writeback, ~30 s by default, bounds the window).
5. G3 on F: *i* is gone (and any other unsynced records of G1).

Broken: raft's invariant that a follower's acked prefix is durable. Consequences: L's heartbeats
carry `commit = min(Match, committed) ≥ i` and F's `commitTo` panics, "tocommit(i) is out of range
[lastIndex(...)]. Was the raft log corrupted, truncated, or lost?" (the panic of etcd #10219), so F
crash-loops until L steps down; and *i*, acknowledged to the client, is on L alone: if L is then
lost, F and G elect a leader without it (a lost acknowledged write). Mitigated only by F's next
`fdatasync` of the segment (any new entry), which covers *i* (same file). Not reachable under
machine crashes: G1's entries reach raft's storage on restart only if they were on disk.

**(b) Re-granting a vote: P9, theoretical.** G1 writes `HardState{term t, vote X}` and dies before
syncing (its `MsgVoteResp` is sent after the sync, so it was never sent). G2 has `Vote = X` from the
page cache; a repeated `MsgVote` from X at term *t* is granted (`raft.go:1214`, `r.Vote ==
m.From`) with the hard state unchanged, so `Save` returns at `wal.go:1022` without a sync. After a
power loss, G3 is at term ≤ t with no vote and can vote for Y at *t*: two votes in one term.
Needs X's `MsgVote` delivered twice (a candidate sends one per term; rafthttp streams do not
retransmit), so only under a duplicating network. G2 rejecting other candidates at *t*, or acting
on the restored term, is safe (rejections promise nothing); G2 campaigning bumps the term and syncs.

**(c) Applying committed entries: not a new risk.** G2 applies entries up to the hard state's commit
(read from the page cache) to bbolt, whose commits are synced. These entries are committed in the
cluster (the commit index came from a leader), so applying them is right even if F's copy is lost;
the resulting state, bbolt's consistent index above the WAL's durable last index, is already
reachable under machine crashes (raft v3.7 without async storage writes hands out committed
entries before they are stable, and the server applies in parallel with `Save`,
`etcdserver/raft.go:238-264`), and the boot code handles it (`bootstrap.go:627-640`'s comment for
the `--force-new-cluster` case; the apply loop skips entries at or below the consistent index).

### Q2: does `Repair` truncate the page-cache tail and sync?

Yes, safely (P6 mitigated). `Repair` (`repair.go:32-106`) decodes the last file through the page
cache, copies it to `.broken`, truncates at the last good offset (`:86`) and `fsync`s the file
(`:92`), which writes G1's dirty pages and the truncation together; it is called before the WAL is
used (`bootstrap.go:689`). The `.broken` copy is not synced (it is diagnostic). `ReadAll`'s
`ZeroToEnd` (`wal.go:580-585`) is not synced, but nothing depends on it before the next
`fdatasync` of the same file, which writes it; a power loss before then leaves a disk state the
decoder must already handle after a crash (zeros, a torn record, or G1/G2 sectors beyond the first
hole, all unacknowledged). P7 is therefore harmless here.

### Q3: does `cut` create/rename segments whose entries are not fsynced before later state depends on them?

`cut` (`wal.go:807-889`) syncs the new file's header (`:851`), renames `N.tmp` to the segment name
(`:860`) and `fsync`s the WAL directory (`:864`) before it appends anything that matters. A kill
between `:860` and `:864` is P4: G2 finds the renamed segment (`readWALNames` through the dentry
cache), opens the WAL with it as the tail, appends and `fdatasync`s entries into it and acks them,
and never `fsync`s the directory before its own next `cut` (64 MB later). Under POSIX (and our
model, where a file `fsync` commits no name), a power loss leaves the segment as `N.tmp` (ignored,
`util.go:306-321`) or the previous name: G3's WAL ends at the previous segment, losing every entry
and hard state G2 synced and acked there (lost acked entries, a term/vote regression). Under
machine crashes the same kill point is harmless (G2' sees no new segment; the old tail was synced
and truncated). On ext4 (`data=ordered`) and xfs it is mitigated: the rename is journaled before
G2's writes, the journal commits in order, and G2's first `fdatasync` into the preallocated
(unwritten-extent) segment forces a commit that carries the rename; the periodic 5 s commit does
too. So: real under the strict model, impossible on ext4/xfs in practice.

### Q4: the WAL directory rename in `wal.Create`

`Create` (`wal.go:102-241`) builds `member/wal.tmp`, renames it to `member/wal` (`:185`, `:306`) and
`fsync`s the parent (`:225`). A kill between them is P4 again: G2 sees `member/wal` (`haveWAL`,
`bootstrap.go:77`) and restarts the member from it, then participates in raft (votes, acks, all
synced into files of that directory and its own `cut`s `fsync` the WAL directory, not its parent).
Under the strict model a power loss loses the rename; G3 sees no WAL, and `Create` would
`RemoveAll` the stale `wal.tmp` (`:113-117`) and bootstrap a fresh log: everything G2 voted and
acked is forgotten. Mitigated on ext4/xfs as for `cut` (any later journal commit carries the
rename). Under machine crashes harmless (G2' sees no WAL and creates it again).

### Q5: does `ReleaseLockTo`/purge delete files based on state that may not be durable?

Yes, at boot: P3/P8, real risk. In one run, segments are unlocked only by `ReleaseLockTo`
(`wal.go:926-967`), called by `storage.Release` after `SaveSnapshot`, which syncs (`wal.go:1082`,
`etcdserver/server.go` `snapshot`; for a received snapshot, after `storage.Sync`,
`etcdserver/raft.go:279`). The purge loop (`server.go:538`, `:613`; `fileutil/purge.go:60-95`)
deletes the oldest `.wal` files beyond `--max-wals` (default 5) that it can lock. At boot, the lock
set is derived from the page cache instead: `recoverSnapshot` takes the newest snapshot record
`ValidSnapshotEntries` sees with index ≤ the last hard state's commit (`bootstrap.go:449-466`,
`wal.go:630-717`), both possibly page-cache-only, and `openAtIndex` locks only the segments from
that snapshot's segment on (`wal.go:374`, `:430-439`). Earlier segments are unlocked from the
start, and the purge loop runs as soon as the server starts.

Execution:
1. G1 takes snapshot S (index *s*): `KV().Commit()`, then `SaveSnapshot` writes the record and is
   killed during its `fdatasync` (`wal.go:1082`; a slow `fdatasync` is exactly when a liveness probe
   kills etcd). G1 never released the locks below S; the previous durable snapshot is S₀.
2. G2 sees S's record (page cache), opens the WAL at S, locks from S's segment on; the purge loop
   deletes the oldest unlocked segments while more than 5 remain, including the one holding S₀'s
   index when more than five segments (320 MB of WAL) were written between S₀ and S (large
   values, or a long snapshot interval). The unlinks are journaled; the journal commits within 5 s.
3. Power loss before G2 syncs its tail (an idle follower; or before writeback of S's record).
4. G3: the newest durable snapshot record is S₀ (or none, if its record was in a deleted
   segment); `selectWALFiles` finds no segment at or below S₀'s index (`wal.go:414-417`), or
   `ValidSnapshotEntries` finds no record, and `openWALFromSnapshot` exits with "failed to open
   WAL" (`bootstrap.go:677`).

Broken: "the WAL holds every segment from its newest durable snapshot on". The member cannot start
and must be removed and re-added; if several members went through it (a fleet-wide restart, then a
rack power loss), the cluster needs a restore from backup. Under machine crashes it cannot happen:
segments are unlocked only after the snapshot record that supersedes them is synced.

### Q6: received snapshots and the snapshot database

`SaveDBFrom` (`etcdserver/api/snap/db.go:37-95`) already handles a process restart: when the
`<index>.snap.db` file exists it `fsync`s the snap directory again before reporting success
(`:57-64`, "A prior SaveDBFrom can have renamed this file and crashed before syncing the
directory"), a P5 fix. At boot, `RecoverSnapshotBackend` (`storage/backend.go:106-121`) renames the
snapshot database over the backend when bbolt's consistent index is below the snapshot record's
index, which can be page-cache-only (as in Q5). After a power loss, G3 can have the backend at S_r
and a WAL without S_r's record: bbolt ahead of the WAL, the state of Q1(c), which the boot code
already admits. Probably tolerated; not proved here.

### Q7: what etcd does after a restart before serving

Nothing that syncs: no `fsync` of the WAL tail or directory, of `member/` or of `snap/`; the raft
node restarts from the restored hard state and log, and the first `Ready` after a restart carries
no hard state change, so no `Save` syncs. Raft's `MustSync` is the only gate and it compares with
the page-cache baseline (P9). Purge starts immediately (Q5). A one-line fix closes every path above
except bbolt's: `fdatasync` the WAL tail (and `fsync` the WAL directory and its parent) at the end
of `ReadAll` (or in `openWALFromSnapshot`) before raft starts; bbolt needs a `db.Sync()` after
`Open` (below).

### Summary table

| path | pattern | outcome without the assumption | assessment |
|---|---|---|---|
| ack of entries already in the log (`raft.go:1796-1802`, `wal.go:1022/1032`) | P1, P9 | acked entry lost; follower panics on heartbeat; committed entry lost with one more failure | real, narrow |
| repeated vote at the same term (`raft.go:1214`) | P9 | double vote | theoretical (needs duplicated `MsgVote`) |
| purge below a page-cache snapshot record (`wal.go:430-439`, `purge.go`) | P3, P8 | member cannot start | real, narrow |
| `cut` rename before dir `fsync` (`wal.go:860-864`) | P4 | acked entries lost, term/vote regression | real under the model; mitigated on ext4/xfs |
| `Create` rename before parent `fsync` (`wal.go:185-225`) | P4 | member's raft state forgotten | real under the model; mitigated on ext4/xfs |
| `Repair` (`repair.go:86-92`), `ZeroToEnd` (`wal.go:580-585`) | P6, P7 | none | mitigated (same-file sync) |
| applying committed entries at boot | P2 | bbolt ahead of WAL | already reachable by crashes |
| `RecoverSnapshotBackend` at boot | P2 | bbolt ahead of WAL | probably tolerated |

## bbolt

bbolt is one file. A commit (`tx.go:170-280`) writes the dirty pages (`write`, `:520-575`),
`fdatasync`s, writes the meta page (`writeMeta`, `:595-623`) and `fdatasync`s. `Open` reads both
meta pages through the mmap (the page cache) and uses the valid one with the higher txid
(`db.go:1141-1162`); the freelist is read from that meta's freelist page (`db.go:422-436`), and a
written freelist holds the free *and pending* pages (`internal/freelist/shared.go:205-213`,
`:287`), i.e. the pages tx *n* freed are free to the next process.

**Same-file coverage works for most of it:** G2's first commit `fdatasync`s the file, writing G1's
meta page *n* along with G2's pages, so after that sync everything is consistent.

**Page reuse on a non-durable commit: P3, real, narrow.** G1 commits tx *n* and is killed between
`writeMeta`'s `writeAt` and its `fdatasync` (`tx.go:606-615`): tx *n*'s pages are durable, meta *n*
is dirty. G2 opens at meta *n*, and its first write transaction (etcd commits at boot, then every
100 ms) allocates pages tx *n* freed, which belong to tree *n−1* only, and overwrites them; those
writes and meta *n* are dirty pages of one file, and a power loss before the flush that ends G2's
`fdatasync` can persist the overwrites without meta *n* (pages reach the device in any order before
the flush). G3 opens at meta *n−1*, whose checksum is valid and whose tree has overwritten pages:
a corrupt database (a panic or wrong data in etcd). Under machine crashes it cannot happen: if
meta *n* is not on disk, G2' opens at *n−1* and its freelist does not contain tree *n−1*'s pages.
Window: G2's first commit within writeback of meta *n* (~30 s), and a power loss during its
`fdatasync`. Fix: `db.Sync()` (an `fdatasync`) right after `Open` and before the first write
transaction.

## Other etcd components touched

- **Consistent index (`storage/schema`, `cindex`).** G2 reads it from bbolt's page cache and skips
  applying entries at or below it. After a power loss bbolt may be behind it again (meta *n−1*):
  G3 re-applies from the WAL or the leader, the ordinary crash case. No new pattern.
- **Snapshot directory.** `bootstrapSnapshot` removes `tmp*` files and legacy `.snap` files
  (`bootstrap.go:210-253`) without syncs: deletions of nothing that durable state needs. The
  `.snap.db` purge (`server.go:611`, count-based) and `ReleaseSnapDBs` (after a synced snapshot)
  depend on no page-cache record.
- **Defragmentation at boot** (`maybeDefragBackend`, `backend.go` `defrag`): copies tree *n* (whose
  pages are durable) into a synced temporary database and renames it over the old one (`:588`)
  without a directory `fsync`; that is a crash-model question (not analysed), not a restart one.
- **File locks** (`fileutil/lock_linux.go`, OFD locks): released at process death in both models;
  their only restart-specific effect is Q5.

## Conclusions and recommended assumption wording

1. The assumption is needed for etcd's WAL (Q1(a), Q5, and Q3/Q4 under our model's directory
   semantics) and for bbolt (page reuse). etcd as written is wrong under a process restart
   followed by a power loss in narrow windows; the windows close at G2's first sync of the WAL tail
   (resp. bbolt's first commit) or at writeback, so they are seconds to tens of seconds after a
   kill at specific points. None of these is reachable under machine crashes alone.
2. The proofs should keep "restart = machine crash" only as a stated environment assumption. Under
   it every path above is excluded (after `sync(2)` the disk equals the page cache and the journal
   is committed, so G2's reads are durable).
3. Recommended wording (for `Impl.lean`'s "Restarts" header and the adequacy statement):

   > **Restarts.** A program generation starts only on a durable state: after a machine restart,
   > or after the previous generation's process has exited (left the kernel) and a `sync(2)`
   > (or `syncfs(2)` of the roots' filesystem) has completed with no writeback error, issued after
   > that exit. A supervisor that restarts the program without this sync is outside the
   > theorem: etcd's WAL and bbolt both have executions that are correct under every machine crash
   > and wrong under a process restart followed later by a power loss
   > (`notes/restart-vs-crash.md`).

   The `sync` must follow the old process's exit (writes in flight at the kill land first), must
   cover metadata (`sync`/`syncfs`, not per-file `fdatasync`), and must report no error (a failed
   writeback leaves pages clean and not durable, which the model's F1 "no failed writeback" already
   excludes).
4. Alternatives, if the assumption is to be discharged instead: in etcd, `fdatasync` the WAL tail
   and `fsync` the WAL directory and its parent at the end of the WAL's boot (before raft starts and
   before the purge loop); in bbolt, `Sync()` after `Open`. With those, a process restart becomes
   equivalent to a machine crash for these paths, and V6 of `notes/fs-semantics-v2.md` could be
   modelled and proved. These are upstream changes (the fork or upstream), and per CLAUDE.md the
   findings (Q1(a), Q5, bbolt) would each get a `nonissues/` or `issues/` file once a test reaches
   them; this note does not add them.

## The WAL's size flag on a crash image (out_size C3, 2026-11-12)

`srvFiles … true` (the WAL's entry records are of bounded size) is argued for a graceful stop in one
process only: every `Save` of that incarnation succeeded (a failed `Save` ends in `lg.Fatal`,
`raft.go:258`, `:265`). A crash image is not a `srvFiles`; a future cross-process or crash restart (a
`walRecs_crash`-style token, or `srvFiles` taken from an on-disk image) cannot inherit `true` from it,
since a failed `Save`'s partial records are on disk with `walSaveOk` false. It needs its own sizing
argument (for instance: a partial record is torn and `ReadAll`/`Repair` drops it, or each record that
reaches disk was written by a successful `saveEntry` of a sized object).
