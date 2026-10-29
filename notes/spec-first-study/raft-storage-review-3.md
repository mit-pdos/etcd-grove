# Review 3: candidate 17 rev 1 (raft's storage contract as range ownership)

Reviewed at `raft-unified` 6657289b28, worktree `raft-spec-review`, read-only. The Go is
`.lake/go-src/raft` at 509271dac. For a2's `appliedSnap` I used
`Proof/go_etcd_io/raft/v3/raft__appliedSnap.lean` (stableSnapTo :75, appliedTo :141, lastIndex
:170, confchange.Restore :181). The etcd checkout lacks fix 1; the translation has the
`raftAdvancedC` wait (`Code/go_etcd_io/etcd/server/v3/etcdserver.lean:2546, 3077`).

## Verdict

Rev 1 fixes most of review 2: the agreement invariant (P1-P3), index 0, the frozen committed
entries handed out below `k`, B2, B3, B5, B6, `FirstIndex`, and the term-only agreement at the
compaction point. The direction is provable. But four things in the text as written cannot be
proved:

1. **After a snapshot, nothing can start at index 0** (N1). `LastIndex`'s pre, `F` and P1 are
   anchored at 0. After `ApplySnapshot`, raft holds no `storLog` for `[|F_old|, s)`, and the
   storage's ghost there holds stale values. a2's `appliedSnap` calls `LastIndex` exactly then.
2. **A `Ready` with no entries hands out `storEnd`** (N2). That contradicts P3, and it makes
   `LastIndex` unprovable while the `Ready` is out. A leader's heartbeat `Ready` reaches this.
3. **The arithmetic is off by one** (N3). The 0-based `F` (A3) was combined with review 2's
   1-based bounds. `|F| < offsetInProgress`, `|F| ≤ committed` and `|F| < k` are false on the
   first `Advance` after `StartNode`.
4. **Uniform-`dq` ranges cannot express B1 or B7** (N4). `storLog_app` splits and joins only at
   one fraction, so "joined from mixed fractions" does not follow from the laws. Also,
   `Advance`'s free `dq` lets the client hand back an uncommitted tail frozen.

None of these needs a new idea. Restatements follow. With them, every step of §4 goes through
(checked below).

## What is good

- **P1-P3 are today's `LogPersistOk`** (`InvRaftlog.lean:508-513`), restated over `π`, and they
  carry every case of `truncateAndAppend` (`log_unstable.go:200-222`):
  - The append case leaves P1 alone.
  - `fromIndex ≤ offset` shortens `sents` to a prefix of itself.
  - The default case lowers `offsetInProgress`.
  - `F` is never touched: `append` panics on `fromIndex ≤ committed` (`log.go:137-139`), so
    `fromIndex ≥ committed+1 ≥ |F|`.
- **The ignored acknowledgements all reduce to P1/P2.** I checked four causes:
  - Truncation, by Log Matching.
  - A `restore`: either `last ≤ s` and it is structural (`log_unstable.go:145-148`), or
    `matchTerm(s)` failed and Log Matching applies (`raft.go:1904-1913`).
  - A term change while the `Ready` is out. The `MsgStorageAppendResp` carries the term from
    accept (`rawnode.go:272`), and `Step` skips `stableTo` for a lower term (`raft.go:1166-1180`).
    P2 then still gives `π = sents ++ uents`, and the next acknowledgement moves them stable.
  - `stableSnapTo` against a superseded snapshot (`log_unstable.go:185-190`). Here `appliedTo(s)`
    still runs, and `committed = s2 > s` keeps it from panicking.
- **Raft reads no storage while a snapshot is pending.** Every reader answers from `unstable`
  first (`log.go:300-320, 391-403, 555-557`; `log_unstable.go:79-96`). This also covers a
  `restore` during a snapshot `Ready` (`raft.go:1852` replaces `s` by `s2 > committed ≥ s`).
- **Freezing at accept is sound** (A4). At accept, the `Ready`'s committed entries below `k`
  are in `π` by P1 (a snapshot `Ready` has `ce = []`, `log.go:225-227`), and committed entries
  are never rewritten. Freezing the delivered entries at or above `k` at `Advance` is sound too,
  even after a `restore`. They are a prefix of the returned batch `es`, which raft recorded as
  committed at accept. P1 is not needed for them.
- **Every case of the `Term`/`Entries`/`FirstIndex`/`Snapshot` posts matches `MemoryStorage`:**
  - `ErrCompacted` iff `i < c` / `lo ≤ c` (`storage.go:148-151, 173-176`).
  - `ErrUnavailable` is unreachable, because the pre covers `i` / `hi-1` and `lo < hi`. With only
    the dummy, `lo < hi ≤ offset+1` forces `lo ≤ offset` (`storage.go:157-159`).
  - `cap = len` (`storage.go:164`), which `extend` relies on (`log.go:547`).
  - `FirstIndex` gives `storCompacted (fi-1)`. Every `ErrCompacted` that reaches
    `maybeSendSnapshot` therefore carries `storCompacted c` with `c ≥ 1`, so `IsEmptySnap` cannot
    fire (`raft.go:680-682`). The `ErrUnavailable` path still rests on `pr.Next ≤ lastIndex+1`.
- **(C) with the rendezvous clause is exactly what the readers need.** Inside `rn.Advance`, only
  the self-addressed messages run. They reach `maybeSendAppend`, whose `ErrCompacted` is
  handled. `nextCommittedEnts` runs only in `readyWithoutAccept`, and
  `hasUnappliedConfChanges` only in `hup`. Neither runs in the window.
- **The design is simpler than today's.** §Removed lists the hand-out, absorb and floor laws,
  the loan and `StorState`, and they are really gone.

## Findings

### Tier A (unprovable as stated)

**N1. After a snapshot, `F`, P1 and `LastIndex`'s pre cannot be anchored at index 0.**

*Evidence.* The snapshot `Advance` pre returns only `storCompacted st s ∗ storLog st s □ [⟨s,t⟩]
∗ storLog st (s+1) (own 1) es ∗ storEnd` (§3). The client spent its own-1 range
`[|F_old|, P)` in `ApplySnapshot`, which rewrites the whole log (`storage.go:235-236`). The
ghost at `[|F_old|, s)` keeps the old, possibly uncommitted contents (they are "compacted"), and
nobody returns a piece there. §4's "F := the snapshot's committed prefix" would need
`storLog st 0 □ F_new` with `|F_new| = s+1`. Raft has no resource for it, and the ghost does not
hold the committed values.

*Trace.*
1. A follower has `F = [0..10]` and gets `MsgSnap` with `s = 100`.
2. The client applies the snapshot `Ready` (`ApplySnapshot`, `Append([])`) and calls `Advance`.
3. `rn.Advance` steps `MsgStorageAppendResp`. Its `Index` is 0, since there were no unstable
   entries (`rawnode.go:274`). Its `Snapshot` field leads to `appliedSnap`
   (`raft.go:1197-1203`).
4. `appliedSnap` runs `stableSnapTo(100)`, then `appliedTo`, then `lastIndex()`
   (`raft__appliedSnap.lean:75, 141, 170`). With no unstable entries and no snapshot, that is
   `storage.LastIndex()` (`log.go:311-319`).
5. The pre `storLog st 0 dq0 F ∗ storLog st |F| dq1 U ∗ storEnd st (|F|+|U|)` needs `[11, 100)`,
   which raft does not hold.

The same gap breaks P1 (`sents <+: π` from 0) and (F) (`F <+: π`) after every snapshot. The
current proof avoids it by indexing relative to the compaction point `σ.prev`
(`InvRaftlog.lean:413-431, 525-529`).

*Caller affected:* `raft.appliedSnap` (a2), `raftLog.lastIndex` everywhere after a snapshot,
and §4's `LastIndex` argument.

*Restatement.*
- `storEnd st e` means "the storage's last index is `e-1`", exactly. `MemoryStorage` keeps this:
  `Append` holds the tail up to `storEnd`, `Compact(x)` needs `x ≤ lastIndex`, and
  `ApplySnapshot` resets the end to `s+1`. Then
  `{{ storEnd st e }} st.LastIndex() {{ i, RET (i, nil); storEnd st e ∗ ⌜uint.nat i + 1 = e⌝ }}`.
  This is also N5's simplification.
- Relativize raft's invariant to the compaction point `c` it holds (`storCompacted st c`):
  - raft holds `storLog st c □ F ∗ storLog st (c+|F|) (own 1) (π.drop …) ∗ storEnd st |π|`;
  - P1/P2 hold over `[c+1, …)`, with (T) at `c`.
  - Before any snapshot, `c = 0` and `F[0] = e₀`.
  - After a snapshot, `F := [⟨s,t⟩]` and `c := s`. Raft drops the pieces below.
- Alternatively, have `ApplySnapshot` rewrite the ghost of `[|F_old|, s)` to the committed
  entries of `snapshotValid`'s `l` and return them `□`. That keeps the 0-anchoring, but it costs
  the implementation a conversion `LogEntry → EntryM` and the client a bigger post. I recommend
  relativizing.

**N2. A `Ready` without entries must hand out nothing. As written it hands out `storEnd`, which
contradicts P3 and blocks `LastIndex` while the `Ready` is out.**

*Evidence.* `readySnap (none)` hands out `storLog st k (own 1) old ∗ storEnd st (k+|old|)`
unconditionally, and `node.Advance` takes it back unconditionally (§3). P3 says "`uents = []` →
nothing out".

*Trace.*
1. A leader has `uents = []`. A tick produces a `Ready` with only heartbeats (`es = []`).
2. `readyc <- rd` runs `acceptReady` and hands out `storEnd st |π|` (`node.go:435-443`).
3. `run` keeps serving `recvc` while the `Ready` is out (`node.go:394-400`). A
   `MsgHeartbeatResp` arrives, and `stepLeader` calls `r.raftLog.lastIndex()`
   (`raft.go:1588`). That is `storage.LastIndex()`, since `uents = []` and there is no snapshot.
4. Raft no longer holds `storEnd`.

This is the most frequent `Ready` there is.

*Restatement.* "If `es = []` (no snapshot), the `Ready` hands out no log resources and `Advance`
takes none back." Equivalently, the hand-out is over `es ≠ []`.

This is consistent with the one reachable case where `es = []` but `uents ≠ []` (the term change
of "What is good"):
- `offsetInProgress = offset + |uents|` and P2 give `π = sents ++ uents`.
- The next `stableTo(lastEntryID)` (`rawnode.go:355-357`) succeeds on entries that are already
  in `π`.
- `LastIndex` is not called while `uents ≠ []`.

State it in §3 and in P3. kvreconf's `Append([])` needs no resource: it returns before taking the
lock (`storage.go:300-302`).

**N3. With `F` starting at index 0 (A3), (F)'s and `readySnap`'s bounds are off by one, and false
in the common case.**

*Evidence.* `|F|` now counts index 0, so `|F| = (last frozen index) + 1`. Review 2's bounds were
1-based: `|F| < offsetInProgress`, `|F| ≤ committed`, `|F| < k`.

*Trace 1 (`StartNode`).*
1. `Bootstrap` appends `1..n` and sets `committed = n` (`bootstrap.go:69-74`).
2. The first `Ready` carries entries `1..n` and committed entries `1..n` (sync mode,
   `maxAppliableIndex = committed`, `log.go:267-273`).
3. At `Advance`, `F := [0..n]`, so `|F| = n+1`. `stableTo(n)` sets
   `offset = offsetInProgress = n+1` (`log_unstable.go:159-162`).
4. Then `|F| < offsetInProgress` reads `n+1 < n+1`, and `|F| ≤ committed` reads `n+1 ≤ n`. Both
   are false.

*Trace 2 (single voter).*
1. Entry 5 is appended, and the self `MsgAppResp` commits it in `rn.Advance`.
2. The next `Ready` has `k = 6` (for a new entry 6), and its committed entry 5 is below `k`.
3. Freezing it gives `|F| = 6 = k`. `readySnap`'s `|F| < k` is false.

The current proof has the strict bound on `applying`: `applying < inprogress`
(`InvRaftlog.lean:661`).

*Restatement.*
- Use `|F| ≤ offsetInProgress`, `|F| ≤ committed + 1` and `|F| ≤ k`. They hold:
  - A truncation keeps `offsetInProgress ≥ fromIndex > committed`.
  - `restore` sets `offsetInProgress = s+1 > committed`.
  - `stableTo` takes a max.
- Better: write the frozen prefix's end as an index, `f = |F| - 1 ≤ applying < offsetInProgress`.
- Use one convention throughout. §3 mixes `|F|` (0-based) with `|st.delivered|` (an index) in
  `nodeAppliedLb γ id |st.delivered|` and `|st.delivered| < sv.Index`.

**N4. Uniform-`dq` ranges cannot express B1 or B7, and `Advance`'s free `dq` is unsound for raft.**

*Evidence.*
- `storLog_app` splits and joins at one `dq` (§1).
- No law joins `storLog st k □ a ∗ storLog st (k+|a|) (own 1) b` into one `storLog st k dq
  (a ++ b)`. With `DFrac`, `□` and `own 1` have no common `dq`.
- So the `Entries` note "may be joined from mixed fractions" (B7) does not follow. Yet
  `nextCommittedEnts` (`log.go:229-239`) and `maybeSendAppend` (`raft.go:640`) issue one
  `storage.Entries` across `F` and raft's own tail (`log.go:513-514`).
- `node.Advance pre (no snapshot): storLog st k dq es` lets the client choose `dq = □` for the
  whole batch, uncommitted tail included, or `own ½`, keeping half.
  - Raft then cannot produce `storLog st k (own 1) old` at the next `Ready`, and the client
    cannot `Append` to truncate.
  - Example: batch `[5..9]`, `committed = 7`, returned all `□`. A new leader truncates at 8. The
    next `Ready` must hand out `[8, 10)` at `own 1`.
- B1 asked for `□` on the delivered prefix only.

*Restatement.*
- Reads take two pieces, as `LastIndex` already does:
  `{{ storLog st k dq1 a ∗ storLog st (k+|a|) dq2 b ∗ ⌜k ≤ lo < hi ≤ k+|a|+|b|⌝ }} st.Entries(lo, hi, max)`.
  Do the same for `Term`, or keep `Term` single-piece, since one index lies in one piece.
- `node.Advance` (no snapshot) takes
  `storLog st k □ a ∗ storLog st (k+|a|) (own 1) b ∗ storEnd st (k+|es|)`, with `es = a ++ b` and
  `k + |a| ≤ applying + 1`. `a = []` is allowed.
- Drop the "mixed fractions" remark.

### Tier B (must be stated)

**N5. `F` must grow at accept, and `j` must be named.**

`acceptReady` freezes `ceBelow`, but §4 updates `F` only at `Advance`. In between, raft holds
`□` where its invariant says `storLog st |F| (own 1) …`.

*Restatement:* "at accept, `F := F ++ ceBelow` (`j = |F|`)". It is a frozen committed prefix, and
`|F| ≤ k` (N3).

**N6. A snapshot `Ready`'s `delivered` after `Advance`.**

`node.Advance post` gives `nodeAppliedLb γ id |st.delivered|`. After a snapshot `Ready`, this
must be `sv.Index`:
- `rn.Advance` runs `appliedTo(s)`, after `stableSnapTo(s)` (`raft.go:766-769`, and a2's order).
- kvreconf's `maybeCompact` after an install compacts up to `min(r.index, snapIndex) = s`
  (`kv.go:409-422`), and needs `nodeAppliedLb s`.

Also say what the post gives when a `restore` superseded the `Ready`'s snapshot:
- `stableSnapTo` is ignored, and `applied := s`, not `s2`.
- The client gets `nodeAppliedLb s`, and (C) holds with `c = s`.

**N7. `snapGiven` is used but never introduced.** It appears in `storCompacted_bound`,
`readySnap (some)` and obligation 3, but not in §1 or §3's vocabulary. Give its kind
(persistent), its index and its law. Raft needs `snapGiven γ id k ⊢ k ≤ applied`, unless a
snapshot is pending or the `Advance` rendezvous is open.

**N8. P0 is implicit.** The `LastIndex` argument ("`uents = []` → P2's premise") needs
`offset ≤ offsetInProgress ≤ offset + |uents|`. State it with P1-P3. It is preserved by
`acceptInProgress`, the truncation cases, `stableTo`'s max and `restore`
(`log_unstable.go:122-130, 159-162, 192-221`).

### Tier C (simplicity)

- **C1. `LastIndex` needs only `storEnd`,** given N1's exact meaning. The `F`/`U` split in its
  pre is the main thing that tied the contract to 0-anchoring.
- **C2. `Compact(x)` needs only `storLog st x □ [e]`**, plus `nodeAppliedLb x` and `x ≤` the
  stored snapshot, not the discarded range "up to `x`".
  - Below `x`, every reader gets `ErrCompacted`. The only content that must not change later is
    the term at `x`. An own-1 holder below `x` is harmless: `Append` skips compacted indices
    (`storage.go:310-312`).
  - If you keep "up to `x`", phrase it as `storCompacted st j ∗ storLog st j □ es` with
    `j + |es| = x + 1`. etcd's apply thread does not know the current compaction point when it
    calls `Compact`, and the frozen pieces it holds have a gap below a snapshot.
- **C3. `storLog_excl` is derivable** from `storLog_agree`, `storLog_frac` and `storLog_valid`.
  It is harmless to keep as a stated law.
- **C4. §4's (C) restates part of `storCompacted_bound`.** Say only "raft holds `storCompacted
  st c`, `c ≤ f`", and derive "`c ≤ applied`, or in the window `≤ delivered`" from the bound and
  N7's law at each use. Then (C) carries no second copy of the bound.

## Clients (§6, §7)

- **kvreconf works with N2-N4 and N6.**
  - A mid-`Ready` `CreateSnapshot(r.index)` (`kv.go:366-369`) gets its term from one of three
    places: the frozen `ceBelow` when `r.index < k`; its own-1 batch range otherwise (reading
    needs no freezing); or the frozen delivered prefix after `Advance`.
  - `ApplySnapshot` succeeds, since `sv.Index > applying ≥ snapIndex` (B2, `storage.go:229-232`).
  - `maybeCompact` (`kv.go:409-422`) gets `storCompacted (fi-1)` from `FirstIndex`, and needs N6
    after an install.
- **etcd works, with fix 1.**
  - The apply thread's `CreateSnapshot(appliedi)` (`server.go:2102`) can race the raft
    goroutine's `ApplySnapshot` of the next `Ready` (`raft.go:277`). The race is benign:
    `ErrSnapOutOfDate` is checked before the index arithmetic (`storage.go:243-246`), and etcd
    returns on it (`server.go:2106`). The same holds for `Compact`'s `ErrCompacted`
    (`server.go:2154`).
  - So `MemoryStorage`'s `CreateSnapshot` spec must allow `ErrSnapOutOfDate` without the
    client knowing the stored index, and `Compact` must take C2's `storCompacted`-anchored form.
  - etcd's snapshots carry `nil` data. The client's `snapMade` must accept that. It is etcd's own
    obligation, not the contract's.

## §5 (asynchronous mode)

It is plausible, with B4 as stated. N2's rule carries over: a `MsgStorageAppend` with no entries
hands out nothing. One thing to add: the acknowledgement's `(index, term)` is `lastEntryID` at
`Ready` time, not the batch's last (`rawnode.go:355-357`). So with several batches out, an
acknowledgement can attest entries of an earlier batch whose own acknowledgement was dropped by
the term check. P1 over the list of batches must allow that.

## Review 2's findings

| finding | status at rev 1 |
|---|---|
| A1 | addressed: P1-P3 |
| A2 | addressed in substance, but the bounds are now off by one (N3) |
| A3 | addressed |
| A4 | addressed, except that `F` must also grow at accept (N5) |
| B1 | not expressible with uniform `dq` (N4) |
| B2 | addressed |
| B3 | addressed |
| B4 | addressed |
| B5 | addressed |
| B6 | addressed |
| B7 | not expressible: the laws do not give the mixed join (N4) |
| §V | addressed: `FirstIndex`, exclusivity, overlap agreement, (T) |
| C1, C3, C4 | addressed |
| C2 | moot: `storFrozen` is gone |

## Go bugs

None new. The cases above rely on already-recorded issues: `raft-compact-past-snapshot`,
`etcd-compact-past-raft-applied`, `raft-memorystorage-initialstate-unlocked`.

## Ranking (need of revision)

1. **§4's invariant:** N1 (re-anchor at the compaction point), N3, N8, C4.
2. **§3's `Ready`/`Advance` specs:** N2, N4's `Advance` pre, N5, N6.
3. **§2's read triples:** N1/C1 (`LastIndex` over `storEnd` alone), N4's two-piece
   `Entries`/`Term`.
4. **§1's vocabulary:** N7 (`snapGiven`), `storEnd`'s exact meaning, C3.
5. **§6/§7:** C2's `Compact` pre; etcd's racing `CreateSnapshot`.
6. **§5:** the `lastEntryID` remark.
