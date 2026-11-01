# Plan: watches across a compaction (spec-first; 2026-11-01: survey, the user's decisions; next W0, the Draft)

**Goal.** A compacting server serves watches, and a watch whose next revision was compacted ends
the way etcd ends it: the watchable store sends the watcher one response with `CompactRevision` set
and drops it (`watcherGroup.chooseAll`, `watcher_group.go:255-262`), the server's send loop forwards
it as canceled (`v3rpc/watch.go:455`, `canceled := wresp.CompactRevision != 0`), and the client's
watch channel delivers it and closes (`WatchResponse.Err()` is `ErrCompacted`, `client/v3/watch.go:127`;
`serveSubstream` returns on `Err() != nil`). M2 left this out on purpose (`notes/m2-plan.md`, decision
2: "no watches"; `notes/m2-storage-plan.md`, review round 1's **F1**, the user's: "no watchers in
compaction mode", a client-side premise). This plan lifts F1.

## Survey (2026-11-01)

**The client's `watcher.Watch.spec` already admits it.** A response is one of
`watchStateRespOk`'s arms (`client/v3/WatchStateDefs.lean:121`), and `watchErr`
(`cache/v3/InvEtcd.lean:867`) counts `CompactRevision ≠ 0` as an error. So the client-facing
statement need not change for soundness; what blocks a compacting server is below it.

**Where compaction is excluded today** (each one a premise or a frozen fact, not a missing proof
branch):
- *mvcc, the create token*: `storeWatchParams`'s `T := watchTok γ ∗ noCompactor γ.st`
  (`mvcc/InvWatchStore.lean:1718`), so `watch` registers a watcher only on a store that never
  compacts; the store's lock body keeps `wsWatchFrozen` ("no watcher, or the store frozen",
  `:1451`), which `syncWatchers`' non-empty branch turns into `crevFrozen` for `rangeEvents`
  (`Spec/.../mvcc/rangeEvents.lean:42` takes `crevFrozen`).
- *mvcc, the responses*: `chooseAll`'s spec requires every member at or above `compactRev`
  (`Spec/.../mvcc/watcherGroup__chooseAll.lean:35`), so its compaction branch is excluded;
  `watcher.send` fixes `CompactRevision = 0` (`Spec/.../mvcc/watcher__send.lean:56`), and the
  channel's response predicate too (`InvWatchStore.lean:456`); `cancelWatcher`'s `wa.compacted`
  arm is unreachable.
- *v3rpc*: `mvccResp` builds every forwarded response with `canceled := false`, `compactRev := 0`
  (`v3rpc/InvWatchStream.lean:199`, "mvcc's responses never carry a compaction"); `sendLoop`'s proof
  uses it (`serverWatchStream__sendLoop.lean:927`).
- *client*: the member facts carry the fact for the create token (`watchMemberFacts`,
  `client/v3/InvWatch.lean:472`; `InvClientNewResult.lean:56`), so `isClientWatcher` exists only
  over a non-compacting member.

**Go checked for soundness of the lifted statement** (what `syncWatchers` reads after a compaction):
- `syncWatchers` holds `revMu.RLock` while it reads `currentRev` and `compactMainRev` and chooses, so
  the two are a consistent pair; a watcher with `minRev < compactRev` gets the compaction response
  (or, if its channel is full, is skipped and retried), every other chosen one reads `rangeEvents`
  from `minRev ≥ compactRev`.
- Compaction keeps every revision at or above the compaction revision in the key bucket, the
  tombstone at exactly that revision included: the store's `kvindex.Compact` uses
  `keyIndex.compact` (`index.go:216`), which keeps it; only `keyIndex.keep` (the hash's,
  `index.go:235`) skips it. So a watch from the compaction revision misses no event. (Checked, not a
  bug.)
- The one loss: a key deleted and re-put within the compaction revision (a transaction): one of the
  two changes at that revision is gone, so a watch from it would see one event where the model has
  two. That is `issues/etcd-compaction-delete-then-put.md`, the compaction arm's `NoDelPutAt`
  premise already; the watch side inherits the premise, no new one.
- The scheduled compaction's backend deletes run in batches after `compactMainRev` moves: they only
  remove revisions below it (the kept set), so `rangeEvents` from `minRev ≥ compactMainRev` is
  unaffected by a job in flight. The mvcc compaction model (`compactRight`, `crevLb`,
  `storeReaderC`, `rangeOutcomeC`) has this for ranges; `rangeEvents` needs the same for the key
  bucket's event scan.

**Sizes** (the proofs that change): `syncWatchers` 1191 lines, `watchableStore.watch` 1277,
`cancelWatcher` 872, `watcher.send` 802, `moveVictims` 770, `chooseAll` 213, `choose` 170,
`rangeEvents` 124, `InvWatchStore` 1857, `InvWatchGroup` 957, `SyncWatchersLemmas` 822; v3rpc's
`sendLoop` 2103; on the client, `watchGRPCStream.run` and `serveSubstream` only if they use
`compactRev = 0` of a forwarded response (to check in the Draft).

## Design, by the principles

- **One spec per function, compaction as state** (`compaction-in-place.md`): no compaction-mode
  copy of any watch spec. The create token loses `noCompactor`; `wsWatchFrozen` goes; `syncWatchers`
  reads the store's compaction revision under `revMu` with a lower bound the store's compaction
  model gives (`crevLb`-style), and a never-compacting store is the case where the compaction branch
  never fires. `noCompactor` stays only where something else still needs it (to check: the restore
  path, `watchableStore.Restore`, is the snapshot track's and is left alone).
- **mvcc's response gains one arm**: the channel's response predicate (`InvWatchStore.lean:456`)
  admits, besides today's, a compaction response `⟨id, CompactRevision := c, no events⟩` with
  `minRev < c` (the watcher's next revision compacted) and `c ≤` the store's revision, after which
  the watcher gets nothing more. `chooseAll`'s premise becomes its loop's real precondition (the
  restore case only), `watcher.send` keeps `CompactRevision = 0` (it is only called for events).
- **v3rpc forwards it** as `canceled := compactRev ≠ 0` (what `sendLoop` does), `mvccResp` over the
  response's `compactRev`; `watchDn` unchanged in shape.
- **The client's `Watch.spec` unchanged** (the response is `watchStateRespOk`'s error arm). Margin,
  stated in its docstring: the code also says the compaction revision `c` with `cursor + 1 < c`
  (the watch's next revision was compacted) and `c` at most the state's revision; the spec says
  only "an error". Strengthening it is question 2.

## Questions for the user (answered 2026-11-01: 1 lift F1, 2 (a) keep "an error", 3 (a) extend compactkv; all the recommended)

1. **Lift F1** ("no watchers in compaction mode", your 2026-10-30 decision for M2's storage side)?
   It was a scope restriction, not a design: the create token's `noCompactor` and the member facts'
   copy go, and every watch proof handles compaction. *Recommended: yes* (it is what this track is).
2. **The client's `Watch.spec`: keep "an error", or strengthen to say the compaction revision?**
   (a) Keep it (the margin in the docstring); no client proof changes. (b) Add to the error arm, for
   `CompactRevision ≠ 0`: `cursor + 1 < c ≤ σ.rev` (the watch missed revisions `cursor + 1 .. c - 1`
   at most; a client like the cache re-lists from `c`). No client proof uses it today.
   *Recommended: (a)* now, (b) when a client needs it (the cache's re-list).
3. **The end-to-end example**: (a) extend `compactkv` with a watch after the rounds (from the last
   compaction's revision: in a run it gets the last round's put; from revision 2: in a run it ends
   with `ErrCompacted`; `Main` panics only on a wrong event), or (b) a new example `watchcmp`
   (`watchkv`'s workload on a compacting member). *Recommended: (a)*, one program and theorem fewer.

## The Draft's review round 1 (2026-11-01) and the user's decision on its premise

Candidate 2 (scratch, the spec skill's practice) repairs round 1's findings: `rangeEvents` was
false at `minRev = c` when revision `c` changes one key twice (compaction keeps only the later
change; `issues/etcd-compaction-delete-then-put.md`, its second symptom), `chooseAll`'s
`0 ≤ compactRev` was unsatisfiable on a never-compacted store, the channel invariant had no arm for
a compaction response, `choose`'s copy branch leaves compacted members in the source group
(`issues/etcd-watch-compacted-resent.md`), the examples' and the cache's `cm = false` premises go
with F1 (the exported `cache/v3/Results.lean`'s `hoff`: weaker premises), and the client's `run`
uses `canceled = false` of forwarded responses. The user first chose the fact "revision `c` changes each key at most
once" as a premise of `store.Compact`; review round 2 showed it unprovable at the server (a
revision can put a key and then delete it through gRPC at the fork pin, `checkIntervals`' sibling
bug, `issues/etcd-txn-check-intervals-sibling.md`, with this consequence reproduced). **The user's
decision (2026-11-01, superseding): the watch-create token carries, gated by the mode, "no sealed
revision writes a key twice" (`mvcc.noDupKeys`), in place of `noCompactor`**; the store keeps "no
watcher, or (in compaction mode) no duplicate keys"; `store.Compact` unchanged; the non-compacting
examples untouched; the compacting example proves it from its workload. (The candidate in between
said the client's `srvNoDupKeys` was an existing premise: it is an unused definition.)

## Stages (after the questions; each leaves the build green, committed, no push)

- **W0, the Draft**: the changed statements (mvcc's response arm, the create token, `rangeEvents`
  and `syncWatchers` over a compaction lower bound, `chooseAll`'s premise, `mvccResp`), in a scratch
  candidate for review (the spec skill; a `spec-reviewer` round), then a Probe of the riskiest
  proof (`syncWatchers`' compaction branch).
- **W1, mvcc**: the store's invariants and `chooseAll`/`choose`/`syncWatchers`/`rangeEvents`/
  `cancelWatcher`/`moveVictims`/`watch` over the new response arm and token.
- **W2, v3rpc**: `mvccResp`, `sendLoop`; the create token through `upOk`/`watchUp`.
- **W3, client**: the member facts without `noCompactor`; `run`/`serveSubstream` if they need it;
  `isClientWatcher` over a compacting member; `common.kv_served`'s watch registration in compaction
  mode.
- **W4, the example** (question 3), its collection, `STATUS.md`.

**Overlap with other work**: none of these files is on the snapshot branches (`snap-j8a-*`: the
apply side and `NewServer`); `watchableStore.Restore` is theirs and stays as it is. The bounds track
(`bounds-*`) works on lock and reader-slot counts: check `syncWatchers`' reader slot before W1.
