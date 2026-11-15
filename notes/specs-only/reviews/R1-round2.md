# R1 (raft's node API): round 2 (provability and completeness)

Reviewer: round-2 agent, 2026-11-09. Commit under review: `627da340d6` (the round-1 repairs; R1's
files are unchanged in the working tree since). Read: the round-1 reports, the "Round 1 repairs"
section of `batch-R1.md`, the diff `339fd9675a..627da340d6` of R1's files, `Model.lean`, `Api.lean`
and the changed specs, the snippets `examples/specreq/raftnode/`, the `req/` notes,
`nonissues/etcd-replay-snapshot-confstate-ahead.md`, `issues/etcd-merged-snapshot-stale-term.md`,
the pinned Go (`.lake/src/raft`, `.lake/src/server/etcdserver`), W0's `SpecPlan/Spec/context/Api.lean`, and
the old paper proof `specs-ref/notes/reconfiguration-safety.md`. I built nothing. `gofmt -l` on the
snippets is clean.

## Verdict

**Not done.** Of the 13 round-1 first-tier findings, 12 are fixed and the fixes hold against the
Go code. The 13th, provability F1 (`msgSent_replaceSnap`), is fixed only for the double commit it
described: the repair dropped the term premise, which reopens a known etcd bug. The repairs also
introduced one new first-tier defect (N1, the view after a snapshot) and expose one missing callee
law (N3, `ctx.Done()`). Each has a local fix.

## First tier

### N1 (new). After a snapshot, `Advance` puts the view at an `a` the client cannot know

Files: `node__Advance.lean:59`, `RawNode__Advance.lean:46`. The snapshot arm is
`∃ a m, nodeConf n γ ⟨a, m⟩ ∗ ⌜s.index ≤ a ∧ s.conf.Is m⌝`.

**Why the client is stuck.** `a` is raft's proof's choice. No law lets the client pin it or move it:
`nodeConf_confAt` (Api.lean:650) only reads the view, and `snapValid_committed` gives its own
unrelated `∃ a`. What the client does next depends on `a`:

- `node.ApplyConfChange.spec` for an entry below the view requires a no-op (`m' = v.membership`).
- `node.Advance.spec` requires the entries above the view that were not applied to be decided skip.

So:

- **`readyloop.go:ReqReadyLoop` is no longer provable.**
  - **The snippet.** After installing a snapshot it applies every later conf entry
    (`applied = snapshot index`, then `ApplyConfChange` on each `decide(e)`).
  - **The counterexample.** The cluster commits "add 4" at index `s.index+1` and "remove 4" at
    `s.index+2`. The configuration at `s.index+2` equals the one at `s.index`. Raft may return the
    view at `a = s.index+2`. The loop's `ApplyConfChange(add 4)` is then below the view and not a
    no-op, so its precondition is false.
  - This holds even if every snapshot of the cluster is made at its own index. In round 1, with
    the view at `uint.nat s.index`, the snippet was provable. This is a regression.
- **etcd (2d) is not served.** etcd skips the replayed entries at or below the consistent index of
  the database it installed (`server.go:2034-2053`). It needs the view at that index, which the
  sender's snapshot was made at (`createMergedSnapshotMessage`, server.go:1014: `ep.confState` at
  `ci`, `dbsnap` at `ci`). The spec cannot give it.

**Fix: the client names the point.** In the snapshot arm, return

```lean
∀ a m, confAt γ a m -∗ ⌜uint.nat s.index ≤ a ∧ s.conf.Is m⌝ -∗ |={⊤}=> nodeConf n γ ⟨a, m⟩
```

or the same as a law over a `nodeConfSnap n γ s` token.

- The client knows `a` from its own invariant over `snapsMade`, where the snapshot's data records
  it.
- For raft, this is the same obligation as `RestartNode`'s free `a` (req item 8).
- `ReqReadyLoop` then needs one more `Assumes`: "every snapshot of the cluster is made at its own
  index's configuration (`snap_make` with `a = |l|`)". Re-applying after a snapshot is wrong
  otherwise; the nonissue says so itself.
- **Alternative.** A pure snapshot-to-point record `snapPoint γ s a`, made at `snap_make`, with
  agreement, returned by `Advance` beside the view. It costs one more predicate.

### N2 (F1, partly fixed). `msgSent_replaceSnap` admits a snapshot of a term above the message's: the known `issues/etcd-merged-snapshot-stale-term.md`

File: Api.lean:750-754.

**What the repair did.** It replaced the old premise "the new snapshot is committed at the
message's term" (specs-ref `sentMsg_replaceSnapshot_impl`: `committedAtTerm γ N st.msg.Term' c`)
by `isNode n γ m.src ∗ deliveredLb n γ l ∗ ⌜s'.index ≤ |l|⌝`.

**Round 1's double commit is excluded.** I checked two cases:

- While the sender still leads at `m.term`, its delivered log is a prefix of its own log.
- Once it has left `m.term`, it ignores the follower's acknowledgement at `m.term`, since
  `stepLeader` counts only responses of its current term.

**But `deliveredLb` may be taken after the sender stepped down.** By then its delivered log
includes entries committed at later terms. That is exactly the issue's scenario, which it
reproduces with real raft and etcd loops:

1. A leader at `t` steps down while saving a Ready.
2. It applies entries of term `t'' > t`.
3. It sends its queued term-`t` `MsgSnap` with that content.
4. A follower at term `t` installs a log whose last term exceeds its own term.
5. With a gap of two terms, a leader of the term in between can panic (`need non-empty snapshot`;
   the issue's `stale_term_gap2_ack_test.go`).

The law lets a client build that message with `msgSent`, so `node.Step.spec`'s "no panic" is false
alongside it. The issue is `blocks-proof: yes`. The fork's fix (`server.go:1013`:
`m.GetTerm() == apply.raftTerm`) is exactly the guard the dropped premise expressed.

**Fix.** Add `uint.nat s'.term ≤ uint.nat m.term` (or the round-0 shape: `s'` within a log
committed while the sender was at `m.term`).

- etcd meets it through the fork's guard: `appliedt ≤ raftTerm = m.Term`. 2d needs a fact that
  the applied entries' terms are at most the node's current term; say so in req for 2d.
- Add the same to `ReqSendSnapshot`'s `Assumes` (transport.go:37).
- Update req item 10.

### N3 (new, follows from F5's repair). The node specs take `Context.ctxOk`, but W0's context API has no `Done()` law

Files: `SpecPlan/Spec/context/Api.lean:73-105`. The API has only `Err`, `ErrDone`, `TODO` and `Background`.

**Where it is needed.** `node.stepWithWaitOption` selects on `<-ctx.Done()` and then returns
`ctx.Err()` (node.go:519-520, 535-536, 545-546). Its proof needs:

- a triple for `Done()` under `ctxOk`: a channel, or `nil` for a context never done;
- that a receive on it gives `ctxDone ctx`;
- that a `nil` channel never fires in a `select`.

**Gap.** Neither the context API nor any `req/` note has these. So `node.step*.spec` and every
`node.*` spec with a context are unprovable from their callee vocabulary. (The header of
`SpecPlan/Spec/context/Api.lean` names `Done()` as part of the bundle, but exports no law for it.)

**Fix.** A `req` entry for W0: `Done.spec` and a receive law.

## The 13 round-1 findings, checked

| finding | status | evidence |
|---|---|---|
| P-F1 replaceSnap | **partly** (N2) | Api.lean:750 |
| P-F2 masks | fixed. `⊤` on the six storage updates. The consumers (`MemoryStorage.*.spec`, AU at `⊤`) take them directly; raft opens `γ.ns` inside. | Api.lean:790-837 |
| P-F3 stored snapshot valid | fixed: `σ.snap.isEmpty ∨ snapValid γ σ.snap` in `RestartNode`/`NewRawNode` (and R2's `newRaft`). etcd's restored snapshot (index `si`, configuration at `ci ≥ si`, `bootstrap.go:107-116`, `ci ≥ si` by `recoverSnapshot` :489-497) meets the generalized `snap_make`, from the old snapshot's `snapValid_committed`. | RestartNode.lean |
| P-F4 boot bytes | fixed: `BootLog` fixes `e = ⟨1, EntryConfChange, bootEntryData p.1 p.2⟩`, with non-empty contexts. Matches `RawNode.Bootstrap` (bootstrap.go: `proto.Marshal(&ConfChange{Type: AddNode.Enum(), NodeId, Context})`, a proto2 `bytes` field, so `nil` and empty differ). etcd's contexts are JSON. | Model.lean:468-482 |
| P-F5 contexts | fixed in the statements (`ctxOk`, `nodeErr n ctx`'s `ctxDone ctx ∗ isCtxErr err`): the snippets' `ctx.Err() == nil` checks follow by `ErrDone.spec`, and rafthttp's `TODO()` by `TODO.spec`. The proofs still lack a callee law (N3). | Api.lean:411-420 |
| P-F6 Stop twice | fixed: `running : Bool`. A stopped node's `Stop` finds `done` closed (node.go `Stop`'s select; `stop` unbuffered, its receiver gone). | node__Stop.lean |
| P-F7 storage contract | fixed. `Entries`: `ErrCompacted` iff `lo ≤ off`, else non-empty (storage.go:150-161: `lo > off ∧ hi ≤ last+1` gives `len(ents) > 1`). `Term`: `j ≤ last` supplied by raft (log.go:401-405, and unstable entries follow the stable ones). `MemoryStorage.Term`: `i < off + 2^63` (storage.go:177). `Append`: `k + |es| < 2^64` (storage.go:302). | Api.lean:358-390 |
| C-F1 restart `a` | fixed in the statement; the obligation on raft is discussed below | RestartNode.lean |
| C-F2 empty V2 | fixed; the law is sound (below) | Api.lean:614 |
| C-F3 replay snapshot | fixed in `snap_make`/`snapValid`, but its consumer at `Advance` is not usable (N1) | Api.lean:690 |
| C-F4 read law | fixed: `stor_read` (second-tier remark R3) | Api.lean:825 |
| C-F5 status progress | fixed: `statusOwn_progress` (third-tier remarks) | Api.lean:868 |
| C-F6 double Stop snippet | fixed (P-F6) | restart.go |

## The obligation on raft's core (req items 8-10)

**Go level: no panic.**

- `newRaft` restores whatever `ConfState` the storage reports (raft.go:472-479), so a
  configuration ahead of the log is accepted. `confchange.Restore` with `LastIndex` sets `Next`
  past the stored log.
- `appliedSnap` (raft.go:766-788, the fork's fix) switches to the snapshot's configuration at
  `Advance` in the same way.
- `switchToConfig` (raft.go:1980-2030) only does extra work at a leader.
- `restore` (raft.go:1876-1943) refuses a snapshot that does not list the recipient. With a
  configuration ahead, the recipient may have been removed in `(s.index, a]`. Raft then answers
  with its commit index, and the leader retries: a liveness matter only. That is
  `nonissues/raft-snapshot-without-recipient-livelock.md`'s pattern.
- The campaign guard (`hasUnappliedConfChanges`) scans `(applied, commit]` of the node's own log,
  which is unaffected.

**Protocol level: plausibly true, but outside the old proof's invariants.** The paper proof
(`specs-ref/notes/reconfiguration-safety.md`) relies on:

- **Cfg:** `applied ≤ a ≤ commit`, the configuration being the fold of the node's *own* log up to
  `a`;
- **I2:** the configuration at a campaign is the fold of `F0.take k`;
- **`W(n)`:** witnesses only up to the node's commit;
- **section 7's far case:** `j_c ≥ j_m + 2` uses "the candidate's configuration's conf entries are
  all `≤ k_c`".

A node whose configuration index exceeds its commit (a restart at etcd's `ci`, or a node that
installed a configuration-ahead snapshot) breaks all four. I found no counterexample. The argument
that seems to close it is that **a node cannot win before it holds the committed prefix through
its configuration's last conf entry `p`**:

1. Some commit fact covers `p`. By the commit fact's "at most one conf entry above its
   configuration index", its quorum's configuration is adjacent to `C_a`, so its quorum meets every
   candidate quorum.
2. If the campaign term `T` is at most that fact's term, the overlapping voter has a durable term
   at least as high (acks are sent after persistence, `msgsAfterAppend`) or a newer last log term,
   and refuses.
3. Otherwise, adjacent-case leader completeness puts the entry in the candidate's log.

After that the candidate's configuration is the fold of its own log, and the old cases apply with
`a` in place of `k_c` and global witnesses for the positions in `(commit, a]`.

This is a real new case for R2 (I am uncertain it closes with no further repair). The open
questions 6/7 to the user are the right place for it. Item 8 should carry this sketch, so that R2
does not rediscover it.

**Item 2 of `req/go_etcd_io_raft_v3.md` is stale.** It still says "`a` in
`[max σ.off Applied, σ.hs.commit]`" and contradicts item 8; R2's `newRaft.spec` already follows
item 8. Fix the text.

## New laws

- **`committedLb_emptyV2`** (Api.lean:614): sound.
  - Its sources are raft's auto-leave (`appliedTo` when joint with `AutoLeave`, after
    `pendingConfIndex`, so no conf entry lies between the tracker's point and the new entry) and a
    client's leave, which `stepLeader` refuses at a non-joint tracker (replaced by an empty normal
    entry).
  - Both checks hold under `ConfigOk` (validation on) at every node.
  - It stays true with configuration-ahead leaders, given the argument above.
  - `ReqEntryTypes` is provable: V2 entries with data come from proposals (`committedOps`), and
    empty ones contradict the client's non-joint `confAt` facts.
- **`confAt_valid`**, **`confAt_committed`**: sound. Every `confAt` is minted by `cluster_alloc`
  (valid by its premises, committed by `committedLb boot`) or by `confAt_decided`/`confAt_skipped`
  on committed entries, with `applyChange_valid`.
- **`stor_read`** (Api.lean:825-830): sound and usable.
  - `off ≤ snap.index` comes from `StorageHolds` at the start and is kept by `stor_compact`'s
    `i ≤ snap.index`, by install, and by `createSnapshot`.
  - The snapshot is valid because the install comes from `msgSent_snap` and the create from the
    client's `snapValid` (with `σ.off > s.index` the create is a no-op).
  - `ReqReadAttached` needs two reads: the first read's `storSnapLb n σ1.snap.index` is the second
    read's `j`, which gives `first - 1 ≤ snap index`.
- **`statusOwn_progress`** (Api.lean:868): usable by `ReqStatusProgress` (`range`, index, `.Match`).
- **`msgSent_replaceSnap`'s premise**: N2.

## Second tier

- **R1. `ReqDeliver` now calls `proto.Clone` on a `*Message`** (transport.go:27). The only Clone
  requests are for `Snapshot`/`ConfState` (`req/..._raftpb.md:26, 60`). Add: Clone of
  `msgPts p dq m` gives a fresh `msgPts p' (own 1) m`.
- **R2. `memStor`'s realization omits the unlocked write `ms.callStats.initialState++`**
  (storage.go:130). That field must be wholly `memStor`'s. No locked method touches it, but the
  stated realization puts everything else in the lock invariant.
- **R3. `stor_read` guarantees `appliedLb n σ.off`, but between `readyStor_install` and `Advance`
  the storage's `off` is the new snapshot's index while raft's `applied` is still below it**
  (`appliedSnap` runs only at `Advance`, raft.go:766-769).
  - It is harmless: `stor_compact` and `stor_createSnapshot` at such an index are no-ops, and raft
    reads no storage entry below a pending snapshot.
  - But `appliedLb` cannot be "a lower bound of `raftLog.applied`" as the header says
    (Api.lean:70-75). Restate it as "applied, or the index of an installed snapshot", or drop the
    conjunct (no snippet uses it).
- **R4. `ReqRestartDurable`'s Assumes** ("the configuration at its snapshot") should say that the
  stored snapshot is empty or made by `snap_make` (P-F3's premise).
- **R5. The ReqReadyLoop `Assumes` after N1**: the same-index snapshot assumption (see N1).

## Third tier

- `statusOwn_progress`'s docstring says "`Inflights` cleared"; Go clones them (status.go:48).
- `Status.Progress` is `nil` when the node does not lead (status.go:71-72).
  `ownMap nil (own 1) ∅` must hold for the law: uncertain how Perennial's `ownMap` treats a nil
  map. Note it for the realization.
- `nonissues/etcd-replay-snapshot-confstate-ahead.md` says the merged message's configuration is
  the applied index's "once the replay is over". During the replay the merged snapshot also
  carries `c`'s configuration (server.go:1014), consistently with its database at `c`. Reword.
- `BootLog`'s non-empty contexts are a scope restriction (Go accepts `nil`). It is marked in the
  docstring; an `Option` context in `peersPts` would lift it.

## Snippets (round 2)

| snippet | status |
|---|---|
| `propose.go` (both) | provable |
| `readindex.go` | provable |
| `readyloop.go:ReqReadyLoop` | **not provable (N1)** |
| `readyloop.go:ReqMustSync` | provable |
| `readyloop.go:ReqDisrupt` | provable (from the statements; raft's own proof needs N3) |
| `confchange.go` (all four) | provable |
| `storage.go` (`ReqBootstrapFromWAL`, `ReqReadAttached`, `ReqStatusProgress`, `ReqSnapshotCompact`) | provable (presence from 3h) |
| `restart.go` (all four) | provable (R4) |
| `transport.go:ReqDeliver` | provable with R1 |
| `transport.go:ReqSendSnapshot` | **provable only through a law that is unsound (N2)**; needs the term premise in its `Assumes` |

## Locality and abstraction

Nothing new. The repairs add no implementation vocabulary. `deliveredLb`/`isNode` in
`msgSent_replaceSnap` are client-visible. `bootEntryData` is 3h's wire model, opaque.

## Go bugs

None new.

- N2 is the known `issues/etcd-merged-snapshot-stale-term.md`. The verified fork fixes it at
  server.go:1013; the spec must not readmit it.
- The configuration-ahead snapshot stays a `nonissues/` entry.

## Targets ranked by need of revision

1. **`node__Advance.lean`, `RawNode__Advance.lean`**: N1. **`ReqReadyLoop`**: N1, R5.
2. **`Api.lean` `msgSent_replaceSnap`**: N2. **`ReqSendSnapshot`**: N2. **req item 10**.
3. **`req/` for W0's context**: N3. **The raftpb req**: R1.
4. **`req/go_etcd_io_raft_v3.md`**: items 2 and 8 (the stale bound, the argument sketch).
5. **`Api.lean` header**: R2, R3. **`restart.go`**: R4. **Docstrings**: third tier.
6. **The rest of the round-1 repairs**: sound as checked.
