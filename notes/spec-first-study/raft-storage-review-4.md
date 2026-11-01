# Review 4: candidate 17 rev 2 (raft's storage contract as range ownership)

Reviewed at `raft-unified` 6657289b28, worktree `raft-spec-review`, read-only. Go: `.lake/go-src/raft`
(509271dac) and a2's `appliedSnap` (`Proof/go_etcd_io/raft/v3/raft__appliedSnap.lean:75, 141, 170`);
etcd: `.lake/go-src/etcd/server/etcdserver/{raft.go,server.go}`, with the fork's `raftAdvancedC` wait
(`Code/go_etcd_io/etcd/server/v3/etcdserver.lean:2545-2546`: the snapshot runs after the wait).

## Verdict

Nothing blocks raft's own proof. I re-ran every step of §4 against the Go and found no counterexample
to P0-P3, F, C, G or T. Review 3's findings are all addressed (table at the end).

One finding is unprovable as stated, on the client side:
- **M1.** etcd cannot meet `Compact`'s precondition after it installs a snapshot.

Three are Tier B:
- **M2.** `ApplySnapshot` must be tied to the window it is lent. Its success needs a frozen witness at
  `CreateSnapshot`.
- **M3.** `storCompacted_bound` cannot be a plain entailment, because `storCompacted` is γ-free.
- **M4.** `nodeAppliedLb` is never introduced, and the bound at `c = 0` needs it at 0.

The rest is wording and small simplifications.

## What is good

- **The Ready/Advance resource flow is consistent with `node.run`** (`node.go:435-446`). The batch goes
  out at `readyc <- rd` (accept). It comes back at `<-advancec`, and `rn.Advance` runs in the same arm.
  Inside that rendezvous raft holds everything. That is where `stableTo`, then `appliedSnap`, run
  (`raft.go:1197-1203`).
- **P0-P3 survive every case of `truncateAndAppend`** (`log_unstable.go:200-222`) while a batch is out.
  I checked three traces:
  1. *Default-case truncation inside the batch.* Batch `[5..9]`t2 is out and a t3 `MsgApp` truncates at
     7. Then `oip := min(10,7) = 7`, and P1 becomes `[..4]++[5,6] <+: π`. At `Advance` the term check or
     `maybeTerm` drops `stableTo` (`raft.go:1166-1180`; `log_unstable.go:139-158`). The next Ready has
     `k = 7` and lends `[7,10)` with `storEnd 10`, and `Append` truncates 9.
  2. *`fromIndex < offset` truncation while out.* Here `offset := oip := fromIndex ≤ k`, so reads stay
     below `k`. At the next Ready raft owns `[f+1, k)` and the returned batch at `own 1`: `a = []`,
     because `k+|a| ≤ applying+1 < fromIndex`. So it can lend from `fromIndex ≥ committed+1 > f`.
  3. *The ABA case from `rawnode.go:281-311`.* In sync mode the term attached at accept
     (`rawnode.go:272`) drops it.
- **`appliedSnap` and a2's `lastIndex`** (`raft__appliedSnap.lean:170`) behave correctly in all four
  cases:
  - *`stableTo` took.* `uents = []` and there is no snapshot. `LastIndex` reads storage, and raft holds
    `storEnd (s+1+|es|)` from the `Advance` pre.
  - *Term changed while the snapshot Ready was out.* `stableTo` is skipped and `appliedSnap` still runs
    (`raft.go:1175-1179`). Then `uents ≠ []`, and the answer comes from unstable.
  - *Entries appended after accept.* The response's `Index` is 0 (`rawnode.go:274`), so `uents ≠ []`
    and the answer comes from unstable.
  - *Superseded.* The snapshot `s2` is still pending, so the answer comes from unstable.

  After the superseded case, `c = f = applied = applying = s < committed`, `oip = s2+1`, and (F) holds.
- **The reads (§2) cover every storage read raft makes.**
  - `term` reads `FirstIndex`, then `LastIndex`, then `Term(i)`, with `fi-1 ≤ i < offset`
    (`log.go:391-405`).
  - `slice` reads `Entries(lo, min(hi, offset))` with `lo ≥ fi` (`log.go:500-514, 555-557`).
  - `snapshot` reads storage only with no snapshot pending (`log.go:293-297`).
  - `LastIndex` is called only with `uents = []` and no snapshot (`log.go:311-319`; P0, P3).
  - `MemoryStorage`'s `ErrUnavailable` branches (`storage.go:157-159, 177-179`) are unreachable under
    the preconditions, and `cap = len` (`storage.go:165`).
- **The index arithmetic is now one convention, and it checks out.**
  - `j + |ceBelow| ≤ k` and `k + |a| ≤ applying + 1` hold.
  - The snapshot `Advance` pre (`s`, `s+1`, `storEnd (s+1+|es|)`) and `storEnd st 1` at start
    (last index 0) are consistent.
  - The `Term`/`Entries` compaction posts hold: `i < offset ⇒ c ≥ i+1` and `lo ≤ offset ⇒ c ≥ lo`
    (`storage.go:150, 174`).
  - On review 3's `StartNode` trace, `f = n ≤ applying = n < oip = n+1` holds.
- **`applied = applying` outside the window, in sync mode.** I checked `acceptApplying` and
  `stepsOnAdvance`'s `MsgStorageApplyResp` (`rawnode.go:423-435`; `raft.go:1205-1208`) and the snapshot
  case (`raft.go:737-740, 766-769`). So `ceBelow` always starts at `f+1`, and `F` stays contiguous
  (N5 is sound).
- **N2 is right.** It covers `hup`'s scan and a leader's `lastIndex` while a heartbeat-only Ready is out.

## Findings

### Tier A (unprovable as stated)

**M1. etcd's `Compact(x)` can target an index below an installed snapshot, where the apply thread holds
no frozen entry.**

*Principle.* C2 says "`Compact(x)` only with `storLog st x □ [e]`". Review 3 proposed that form and
missed this gap.

*Evidence.*
- `compacti = snapi − SnapshotCatchUpEntries` (default 5000), or 1 (`server.go:2146-2150`).
- `snapshotIfNeededAndCompactRaftLog` compacts after every snapshot (`server.go:1210-1219`). A memory
  snapshot is taken every `memorySnapshotCount = 100` entries (`server.go:116, 1225-1227`).
- `applySnapshot` sets `memorySnapshotIndex` to `s` (`server.go:1143`).

*Trace.*
1. A follower that is far behind (or a new member, fresh boot) installs a leader snapshot at `s = 20000`.
2. Its storage is compacted to 20000. It never held entries 15001..20000.
3. 101 entries later the apply thread takes a snapshot at 20101 and calls `Compact(15101)`.
4. `MemoryStorage` answers `ErrCompacted` (`storage.go:272-273`), and etcd ignores it
   (`server.go:2151-2155`).
5. But the contract's pre needs `storLog st 15101 □ [e]`. No one has it: the snapshot `Advance` returns
   only the dummy at `s` and the range from `s+1`.

With a small cluster the same thing happens at `compacti = 1`: a member that joined through a snapshot
at `s ≤ 5000` calls `Compact(1)`.

*Caller.* etcd's apply thread (§7). kvreconf is fine: it compacts in `[FirstIndex, min(applied, snap)]`
(`kv.go:409-422`), which is above every install.

*Restatement.*

```lean
Compact(x):  (storLog st x □ [e] ∨ storCompacted st x) ∗ nodeAppliedLb γ id x ∗ ⌜x ≤ stored snapshot (lb)⌝
```

The second disjunct is the no-op: `x ≤ offset` gives `ErrCompacted`. The client keeps `storCompacted st s`
from the snapshot `Advance` (it is persistent). Say in §7 that etcd hands it to the apply thread.

### Tier B (must be stated for the obligations/§6 to be provable)

**M2. `ApplySnapshot` must be tied to the window it is lent, and its success needs a frozen witness at
`CreateSnapshot`.**

*Evidence.* Obligation 3 reads: "`ApplySnapshot` only with the whole owned log above the frozen prefix
(`own 1`), `storEnd` and `snapGiven`". That does not say which `snapGiven`, or which snapshot.
`MemoryStorage.ApplySnapshot` rewrites everything above `s` whenever `msIndex < s`
(`storage.go:230-236`).

- *(a) A stale `snapGiven`.* `snapGiven` is persistent, so a client can use an old `snapGiven s_old`
  (and its valid `sv_old`) inside a later snapshot window `[f+1, …)` where `s_old ≤ f`. The
  implementation cannot rule out `msIndex < s_old` from what it is given. It would then truncate frozen
  entries in `(s_old, f]`, so it cannot prove "frozen ⇒ present or compacted".
- *(b) A different snapshot.* With `snapGiven s` and some other valid `sv'` at `s' > s`, the compaction
  point becomes `s'`, and `storCompacted_bound` has no witness for it.
- *(c) Success.* The client needs success to produce the snapshot `Advance` pre (`storCompacted st s`,
  the dummy). That needs `msIndex < s`. readySnap gives `⌜applying < s⌝`, which is raft-internal. The
  client cannot use it, and etcd's stored snapshot is shared.

*Caller.* `MemoryStorage`'s proof (§6); kvreconf and etcd at `ApplySnapshot` (`kv.go:355`,
`raft.go:277`), which ignore its error.

*Restatement.*
- readySnap (some) gives `⌜f < s⌝`, where `f+1` is the start of the lent range, instead of
  `⌜applying < s⌝`.
- `ApplySnapshot(sv)` takes `storLog st j (own 1) old ∗ storEnd st (j+|old|) ∗ ⌜j ≤ sv.Index⌝ ∗
  snapGiven γ id sv.Index ∗ snapshotValid γ sv`, and always succeeds.
- `CreateSnapshot(i)` takes the frozen entry `storLog st i □ [e]` (as `Compact` does), not just any
  `storLog` at `i`.

Then the implementation's invariant "the stored snapshot's index carries a frozen ghost entry" gives
`msIndex < j ≤ s`. A frozen entry at `msIndex ≥ j` would contradict `own 1` on `[j, end)`. Both clients
can freeze before `CreateSnapshot`:
- kvreconf mid-Ready freezes the delivered part of its batch (the `Advance` pre allows it).
- etcd snapshots after `Advance`, from the frozen delivered prefix.

**M3. `storCompacted_bound` cannot be an entailment from a γ-free `storCompacted`.**

*Evidence.* §1 says `storCompacted : Storage → Nat → IProp GF` is "γ-free". §2 states
`storCompacted st c ⊢ ∃ k, ⌜c ≤ k⌝ ∗ (nodeAppliedLb γ id k ∨ snapGiven γ id k)`. The justification
lives with the implementation (from what `Compact`/`ApplySnapshot` were given). Getting it from a
γ-free lower bound means opening an invariant that `isStorage γ id st` holds.

*Caller.* Raft, at every `ErrCompacted` it must refute: `nextCommittedEnts`, `hasUnappliedConfChanges`,
`lastEntryID`.

*Restatement.* `isStorage γ id st ⊢ □ (storCompacted st c ={↑storN}=∗ ∃ k, ⌜c ≤ k⌝ ∗ (…))`. Raft uses it
inside WPs with the full mask, so this is free. The alternative is to put the disjunction in the
`ErrCompacted` posts directly.

**M4. `nodeAppliedLb` is used but never introduced.**

*Evidence.* It appears in obligation 3, `storCompacted_bound`, `node.Advance post` and §7. It is not in
§1, not in §2, and not in the repository (`grep` over `Spec/` and `Proof/` finds nothing).
`storCompacted_zero` plus the bound needs `nodeAppliedLb γ id 0` (or `snapGiven 0`) from nothing.

*Restatement.* Declare it with raft's API vocabulary:
- `nodeAppliedLb γ id k`, persistent;
- `nodeAppliedLb_mono`;
- `⊢ nodeAppliedLb γ id 0`.

Raft's internal law is "`nodeAppliedLb γ id k` → `k ≤ applied`" (the authority on `applied`, which
`appliedTo` never lowers: `log.go:333`).

### Tier C (wording, small simplifications)

- **C1. No law gives an empty range.**
  - Raft's initial invariant needs `storLog st 1 (own 1) []`: the start pre gives only
    `storLog st 0 □ [e₀] ∗ storEnd st 1`.
  - So does the snapshot `Advance` with `es = []`.
  - `storLog_app` with `a = []` produces only an empty piece at the same index and fraction.
  - Add `storLog_nil : ⊢ storLog st k dq []`.
- **C2. P1 should be stated as holding with no snapshot pending**, as `LogPersistOk` is
  (`InvRaftlog.lean:495-513`). With one pending, `sents` (`c+1 … offset−1 = s2`) is not in storage. The
  text already says "π arbitrary" then, but P1 is stated unconditionally.
- **C3. §4 "Compaction" bullet.**
  - `hasUnappliedConfChanges` scans from `applied + 1`, not `applying + 1` (`raft.go:1002`). While a
    Ready is out, `applied < applying`, and `hup` can run then.
  - The argument is unchanged: it needs `c ≤ applied`, which (C) gives.
  - Add `lastEntryID` (`log.go:380-383`, which panics on any error) to the readers that (C) protects:
    `term(last)` hitting `ErrCompacted` would need `c > last ≥ applied`.
- **C4. State the `Advance` pre's bound in the client's terms.** `k + |a| ≤ applying + 1` uses `applying`,
  which is raft-internal. Say "`a` lies within the Ready's `CommittedEntries`" instead. The client knows
  their indices.
- **C5. The `Advance` post's frozen hand-out is derivable.** The client already has `ceBelow` (from
  accept). It can freeze the delivered part of its own batch before returning it, and keep the
  persistent copy. Dropping the post's `storLog st j' □ …` loses nothing. Keep it only as a convenience.
- **C6. `maybeSendSnapshot`'s `IsEmptySnap` argument** also rests on two raft invariants:
  - `pr.Next ≥ 1`, for the `entries` path: `fi−1 ≥ lo = pr.Next`;
  - `pr.Next ≤ lastIndex+1`, for the `ErrUnavailable` path (review 3).

  Name both in §4.

## Clients (§6, §7)

- **kvreconf** works with M2 and M4.
  - Its `ApplySnapshot` succeeds: `msIndex ≤ f < s`.
  - `CreateSnapshot` during the apply loop needs a frozen entry. It freezes the delivered entries of its
    batch first, which `Advance`'s `□ a` allows.
  - `maybeCompact` stays above every install.
- **etcd** works with M1, M2 and M3.
  - `CreateSnapshot` running concurrently with the next Ready's `ApplySnapshot` returns
    `ErrSnapOutOfDate` (`server.go:2104-2107`).
  - `compactRaftLog` then still runs (`server.go:1218`). Its `x ≤ appliedi < msIndex` comes from the
    `OutOfDate` lower bound (§6).

## Previous findings

| finding (review 3) | status at rev 2 |
|---|---|
| N1 anchor at `c`, exact `storEnd` | addressed |
| N2 empty Ready lends nothing | addressed |
| N3 one index convention | addressed (checked above) |
| N4 two-piece reads / `Advance` | addressed |
| N5 F grows at accept | addressed |
| N6 snapshot `Advance` gives `nodeAppliedLb s`, superseded case | addressed |
| N7 `snapGiven` | addressed (sealed, persistent, (G)); see M3 for its use in the bound |
| N8 P0 | addressed |
| C1-C4 | addressed. C2's "frozen entry at `x` only" is incomplete for etcd: M1 |
| §5 `lastEntryID` remark | addressed |
| review 2 (all) | addressed per review 3's table, and B1/B7 by N4 |

## Go bugs

None new. M1 is not a bug: `MemoryStorage` answers `ErrCompacted`, and etcd ignores it.

## Ranking (need of revision)

1. **§2 obligations / §6 write specs:** M1 (`Compact` pre for etcd), M2 (`ApplySnapshot`'s window and
   success; `CreateSnapshot` frozen).
2. **§2 laws:** M3 (`storCompacted_bound` behind a fancy update); M4 (`nodeAppliedLb` declared, with
   its law at 0).
3. **§3:** readySnap (some) `⌜f < s⌝` (M2); the `Advance` pre's bound in client terms (C4); optionally
   drop the post's frozen hand-out (C5).
4. **§4 text:** C2, C3, C6.
5. **§1:** `storLog_nil` (C1).
