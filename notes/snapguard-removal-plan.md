# Removing the merged snapshot's index guard (plan, 2026-11-20)

Goal (the user's): delete `&& m.GetSnapshot().GetMetadata().GetIndex() <= ep.appliedi` from
`applyAll`'s `msgSnapC` branch (fork commit 633036387, `goose-lean-snapguard`; `notes/decisions.md`,
"The merged snapshot's index guard") by proving what it stands in for:

> **(I)** a `MsgSnap` `m` that `applyAll` of batch `i` reads from `msgSnapC` with
> `m.Term == apply.raftTerm` has `m.Snapshot.Metadata.Index <= ep.appliedi` (after batch `i`'s
> snapshot and entries are applied).

The guard is not acceptable as a resolution (the user, 2026-11-20): dropping the message and reporting
a failed snapshot turns an unproven safety obligation into a liveness hole. The replay-window
deferral of 6e8f0c004 (`ep.appliedi < ConsistentIndex()`) stays; it is a different question (below).

## (I) holds: the argument, against the fork's code at d3feef9bc and raft d2c16c558

Notation: Ready `k` is the `k`-th `Ready` the raft goroutine (`raftNode.start`) takes; it sends batch
`k` to `applyc` before it processes Ready `k`'s messages, so a `MsgSnap` of Ready `j` enters
`msgSnapC` after batch `j` is queued. The apply thread runs the batches in order (FIFO scheduler), and
may lag: batch `i < j` may read Ready `j`'s message. `raftTerm_k` is the term of the last non-empty
`HardState` of Readys `<= k`. `apl` is `ep.appliedi`: monotone (`applySnapshot` panics on a snapshot
not past it; entries move it forward), at boot the storage snapshot's index (`server.go:808`), and after
batch `k` at least every snapshot of Readys `<= k` (`applySnapshot` sets it, line 1183).

`m` (term `T = raftTerm_i`, in Ready `j`) carries `raftLog.snapshot()` (`log.go:293`), read when the
leader of `T` generated it:

1. **the unstable snapshot** `S`, restored (`raft.restore`, only in `StateFollower`, from a `MsgSnap`
   of the leader of the follower's term `T_r`) and not yet stable. `S` is in the first Ready computed
   after the restore, `h`. If `h <= i`, batch `i` applied it. If `h > i`, Ready `i` was computed before
   the restore, so `T = raftTerm_i <= T_r`, and `m` (generated after the restore, at term `T`) has
   `T >= T_r`: `T = T_r`, and the node would be leader of a term in which it followed another leader
   (election safety: impossible).
2. **the storage snapshot**, put there by
   - `CreateSnapshot(ep.appliedi, …)` (the apply thread, `server.go:2143`): at most `apl` then, so at
     most `apl` now; or the boot snapshot (`bootstrap.go:744`): at most the initial `apl`;
   - `ApplySnapshot(raftSnap)` of Ready `h`'s snapshot (the raft goroutine, `raft.go:287`), before
     `m` was generated: as in 1 with that `h`.

So **(I) is true**: no counterexample, nothing for `issues/`. The term check is what makes it true
(without it, case 1/2 with `T > T_r` is a real stale merge: `issues/etcd-merged-snapshot-stale-term.md`).

## What a proof needs (none of it exists today)

Today `rnSnapMsg` (`InvRaftNode.lean`) knows nothing of `m`'s snapshot index (`SentMsgShape`: `< 2^61`);
raft's storage contract bounds the stored snapshot only by the node's commit (`DL = nodeCommitLb`),
which may be past `apl` (the apply thread lags). Three pieces:

- **R1 (raft API: the snapshot's source).** For each `MsgSnap` a `Ready` hands out (in `msgOut` /
  `sentMsg`'s companion, or a new persistent `snapMsgSrc` beside `rnSnapMsg`'s `sentMsg`): its snapshot
  is either one `Storage.Snapshot()` returned (a client-chosen persistent tag, a new field of the
  storage contract's `Snapshot` post, default `True` for the clients that do not care), or the
  unstable snapshot restored at a term `T_r`, handed out in a `Ready` no later than this one, with
  a token `restoredAt T_r`. Raft internals: `raftLog.snapshot`'s spec (two cases already, U8 v2) to
  carry the tag / `ksn`'s restore term into `maybeSendSnapshot`'s message ghost.
- **R2 (raft API: terms).** `restoredAt T_r` is exclusive with "this node sent a `MsgSnap` of term
  `T_r`" (election safety: the restore's sender was `T_r`'s leader, `isMessage .snap`'s sender log of
  `T`'s leader), and a snapshot `Ready`'s `restoredAt T_r` has `T_r >=` every earlier `Ready`'s
  hard-state term (the driver's `hardState`, monotone).
- **R3 (server).** The storage tag for `srvStor`'s `MemoryStorage`: `CreateSnapshot` by the apply
  thread tags with `apl`'s monotone lower bound (`ep.appliedi`'s authority, the apply thread's);
  `ApplySnapshot` by the raft goroutine tags with "Ready `h`'s snapshot" (the batch index `h` in the
  `sspscConsumer γ.ap` list); boot with the initial `apl`. `rnSnapMsg` gets the Ready index `j` and R1's
  source; batches record `(raftTerm_k, snapshot index_k)` (already in the `toApply` list). At the merge
  in batch `i`: case `j <= i` or `h <= i`, `apl >=` that snapshot; otherwise R2 refutes `T = raftTerm_i`.
  Then `srv_merged_sent`'s `hle` comes from (I) instead of the guard, and the fork drops the clause.

Size: R1/R2 change raft's exported API (`etc/api/raft.txt`'s interfaces, the storage contract every
raft client instantiates, `RaftTla`'s generated copies) and raft's send path proofs; R3 changes
`InvRaftNode`/`InvRaftLoop`/`InvApplyAll`, the raft goroutine's proof (`raftNode.start`) and
`applyAll`. Estimated several sessions; it was option (D) of the 2026-10-31 decision ("term-tagged ghost
state across the raft loop, the storage and the apply thread"), plus (A) (a raft API law on where a
`MsgSnap`'s snapshot comes from). Not started: waiting for the user's go-ahead on the API change.

Not an alternative: weakening `sentMsg_replaceSnapshot`'s premise to the leader log's base of `T`
(`isMessage_snap_recontent` uses `m.index <= ai` only to put `ai` above that base): bounding that base
by `apl` needs the same term and ordering reasoning (the base moves by the same restores and
compactions).

## The replay-window deferral (6e8f0c004): same flavour, but bounded

Inside `ep.appliedi < ConsistentIndex()` the merge is skipped and the snapshot reported failed. The
window closes: after a restart raft re-delivers the committed entries from the storage snapshot up to
at least the backend's consistent index (they are in the WAL: the consistent index was applied from
them), so the apply thread passes `ConsistentIndex()` and later `MsgSnap`s are merged. The leader
retries after `ReportSnapshot(…, SnapshotFailure)` (the follower's progress goes to `StateProbe`, then a
new `MsgSnap`), so this is a delay, not a permanent liveness hole. The proper fix is to send what the
backend holds: merge at the backend's own index, i.e. label the merged snapshot with
`ConsistentIndex()`, its term (`ConsistentApplyingTerm`/the backend's term key) and the conf state at
that index, instead of `(appliedt, appliedi, ep.confState)`; then nothing is deferred. Not done here.
