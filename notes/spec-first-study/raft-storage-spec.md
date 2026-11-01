# Raft storage contract (candidate 17 rev 3, user-approved 2026-10-29)

Status: draft, 2026-10-29, for the user. Scope: the `Storage` interface contract (what an
implementation, with its client, promises raft) and raft's own specs about storage. `MemoryStorage`'s
specs are out of scope (§6 says why they are feasible). `AsyncStorageWrites = false` is proved; §5 says
how the same resources cover the asynchronous mode.

## Direction (the user, 2026-10-29)

- Raft does not own the storage's state: the client may put in a snapshot or compact at any time.
- The log is owned by **ranges** that split and join, like slices, with a fraction (`dfrac`): raft owns
  the log except the part a `Ready` handed out whose acknowledgement has not come back; the client owns
  that part and may write anything there meanwhile, so long as it returns exactly the batch.
- A discarded fraction is the frozen committed prefix (no separate `storFrozen`).
- Snapshots are **valid** (not "certified": no authority).
- Ordinary, not logically atomic, triples.

## Changes

- **rev 1** (review 2, `raft-storage-review-2.md`): today's `LogPersistOk` agreement (P1-P3); index 0 a
  frozen entry; the `Ready`'s committed entries below `k` handed out frozen; B2, B3, B5, B6; `FirstIndex`
  from a compaction witness; `snapshotValid` without `N`.
- **rev 2** (review 3, `raft-storage-review-3.md`):
  - N1: `storEnd st e` means the last index is exactly `e − 1`, so `LastIndex` needs only `storEnd`;
    raft's resources are anchored at the compaction point `c` it holds, not at 0 (after a snapshot
    `c = s` and the pieces below are dropped);
  - N2: a `Ready` with no entries (and no snapshot) hands out nothing;
  - N3: one convention, indices: `c` the compaction point, `f` the frozen end, both indices;
    `f ≤ applying < offsetInProgress`;
  - N4: ranges join only at one fraction: reads and `Advance` take a frozen piece and an owned piece;
  - N5: the frozen prefix grows at accept; N6: after a snapshot `Ready`, `nodeAppliedLb s`, and the
    superseded case; N7: `snapGiven` defined, with its law; N8: P0 stated;
  - C1 `LastIndex` from `storEnd` alone; C2 `Compact(x)` needs only the frozen entry at `x`; C3
    `storLog_excl` dropped (derivable); C4 (C) no longer restates the bound.
- **rev 3** (review 4, `raft-storage-review-4.md`: nothing blocking raft's proof):
  - M1: `Compact(x)` also allowed at an already-compacted `x` (etcd compacts `appliedi − 5000` after an
    install, where it holds no frozen entry; the call answers `ErrCompacted`);
  - M2: a snapshot `Ready` states `f < s`; `ApplySnapshot` is tied to the lent window (`own 1` from `j`,
    `j ≤ s`) and always succeeds; `CreateSnapshot(i)` needs the frozen entry at `i`;
  - M3: `storCompacted_bound` is a law of `isStorage` under an update (the justification is behind the
    implementation's invariant); M4: `nodeAppliedLb` declared;
  - C: `storLog_nil`; (P1) only with no snapshot pending; the compaction readers corrected; `Advance`'s
    bound in client terms; `Advance`'s frozen hand-out dropped (the client already holds it); the
    `pr.Next` invariants named.

## 1. Vocabulary (fields of `class StorageModel`; each implementation provides them; γ-free)

```lean
/-- the storage's entries at indices k, k+1, …, k+|es|−1 are `es`, or compacted (at the compaction
point itself only the term is kept) -/
storLog       : Storage → Nat → DFrac → List EntryM → IProp GF
/-- the storage's last index is exactly `e − 1` (exclusive) -/
storEnd       : Storage → Nat → IProp GF
/-- the compaction point has reached `c` (persistent): `Term(i)` for `i < c` and `Entries(lo, …)` for
`lo ≤ c` answer `ErrCompacted`; `FirstIndex` answers at least `c + 1` -/
storCompacted : Storage → Nat → IProp GF

storLog_app        : storLog st k dq (a ++ b) ⊣⊢ storLog st k dq a ∗ storLog st (k + |a|) dq b
storLog_frac       : storLog st k (dq1 ⋅ dq2) es ⊣⊢ storLog st k dq1 es ∗ storLog st k dq2 es
storLog_valid      : storLog st k dq es ⊢ ⌜✓ dq⌝
storLog_agree      : storLog st k1 dq1 es1 ∗ storLog st k2 dq2 es2 ⊢ ⌜es1, es2 agree on their overlap⌝
storLog_persist    : storLog st k dq es ==∗ storLog st k □ es        -- gives up writing them
instance           : Persistent (storLog st k □ es)
storEnd_excl       : storEnd st e ∗ storEnd st e' ⊢ False
storLog_nil        : ⊢ storLog st k dq []
storCompacted_zero : ⊢ storCompacted st 0
storCompacted_mono : c' ≤ c → storCompacted st c ⊢ storCompacted st c'
```

`own 1` lets its holder write the range (an implementation's write specs take it); `□` is the frozen
committed prefix, which nobody writes again (only compaction removes it: the "or compacted" reading).

## 2. The contract `isStorage γ id st` (persistent)

```lean
def snapshotValid (γ : Cluster) (sv : SnapshotM) : IProp GF :=          -- exposed
  ∃ l m, isCommittedLogLb γ l ∗ confAt γ l.length m ∗ snapMade γ ⟨l.length, m, sv.Data'⟩ ∗
    ⌜l.length = uint.nat sv.Metadata'.Index' ∧ 0 < l.length ∧
      Option.map LogEntry.term l.getLast? = some sv.Metadata'.Term' ∧
      confStateIs sv.Metadata'.ConfState' m⌝
-- replaces `snapshotCert` and the registry `storCert`/`storageCertLink`/`memStorCert`

/-- (persistent; raft-issued) raft handed out a snapshot at index `k` to install -/
def (sealed) snapGiven (γ) (id) (k : Nat) : IProp GF
/-- (persistent; raft-issued, by `Advance`) raft's applied index has reached `k` (M4) -/
def (sealed) nodeAppliedLb (γ) (id) (k : Nat) : IProp GF
theorem nodeAppliedLb_zero : ⊢ nodeAppliedLb γ id 0
theorem nodeAppliedLb_mono : k' ≤ k → nodeAppliedLb γ id k ⊢ nodeAppliedLb γ id k'
```

`isStorage γ id st` := `st` dispatches to methods with these triples, and the law after them:

```lean
{{ storEnd st e }} st.LastIndex()
{{ i, RET (i, nil); storEnd st e ∗ ⌜uint.nat i + 1 = e⌝ }}

{{ storLog st k dq es ∗ ⌜k ≤ i < k + |es|⌝ }} st.Term(i)
{{ t e, RET (t, e); same ∗
     (⌜e = nil ∧ t = es[i-k].term⌝ ∨ (⌜e = ErrCompacted⌝ ∗ storCompacted st (i+1))) }}

{{ storLog st k dq1 a ∗ storLog st (k + |a|) dq2 b ∗ ⌜k ≤ lo < hi ≤ k + |a| + |b|⌝ }} st.Entries(lo, hi, max)
{{ s es' e, RET (s, e); same ∗ ((⌜e = ErrCompacted⌝ ∗ storCompacted st lo) ∨
     (⌜e = nil⌝ ∗ entsRO s es' ∗ ⌜es' ≠ [] ∧ s.cap = s.len ∧ es' <+: (a ++ b).slice lo hi, cut by max⌝)) }}
  -- (two pieces: a frozen prefix and an owned tail, possibly empty: N4)

{{ storCompacted st c }} st.FirstIndex()
{{ fi, RET (fi, nil); ⌜c + 1 ≤ uint.nat fi⌝ ∗ storCompacted st (uint.nat fi - 1) }}

{{ storCompacted st c }} st.Snapshot()
{{ p e, RET (p, e); ⌜e = ErrSnapshotTemporarilyUnavailable⌝ ∨
     (⌜e = nil⌝ ∗ ∃ sv, ownSnapM p 1 sv ∗ ⌜c ≤ uint.nat sv.Index⌝ ∗
        (⌜sv.Index = 0⌝ ∨ snapshotValid γ sv)) }}

/-- compaction stays within what raft has applied, or within a snapshot raft handed out (a law of
`isStorage`, under an update: the justification is behind the implementation's invariant, M3) -/
storCompacted_bound : □ (storCompacted st c ={↑N}=∗ ∃ k, ⌜c ≤ k⌝ ∗ (nodeAppliedLb γ id k ∨ snapGiven γ id k))
```

`InitialState` is not in the contract (it is unlocked and returns the storage's own pointers:
`issues/raft-memorystorage-initialstate-unlocked.md`); `RestartNode` takes its triple as a premise, as
today.

**What the client must keep** (encoded by `isStorage`; proved by the implementation with the client's
invariant):

1. The log changes only where the client holds `storLog … (own 1)`, and its end only with `storEnd`.
2. A non-empty stored snapshot is valid; its index never decreases; the compaction point stays at or
   under it.
3. `Compact(x)` only with `(storLog st x □ [e] ∨ storCompacted st x)` (the frozen entry at `x`, or `x`
   already compacted: then the call answers `ErrCompacted`, M1), `x ≤` the stored snapshot's index and
   `nodeAppliedLb γ id x` (C2; it need not know the current compaction point). `ApplySnapshot(sv)` only
   with `storLog st j (own 1) old ∗ storEnd st (j + |old|)` for `j ≤ sv.Index`, `snapGiven γ id
   sv.Index` and `snapshotValid γ sv`: it then always succeeds (it compacts the owned range, M2).
   `CreateSnapshot(i)` only with the frozen entry at `i` (so every stored snapshot is at a frozen index,
   below any `j` raft lends: hence `ApplySnapshot`'s success).
4. The hard state is the client's (raft reads `InitialState` only at start).

## 3. Raft's specs about storage (synchronous mode)

Notation: `c` the compaction point raft holds (`storCompacted st c`), `f` the last frozen index, `k` a
batch's first index, all indices.

```lean
-- start: index 0 is a frozen entry of term 0, the storage's last index 0
{{ … ∗ isStorage γ id st ∗ storLog st 0 □ [e₀] ∗ storEnd st 1 ∗ ⌜e₀.Term' = 0⌝ ∗
     (InitialState's triple: hsZero and a ConfState of γ.c0) ∗ (start token) }}
  RestartNode(c)                           -- StartNode alike
{{ n, RET n; isNode n γ N id ∗ nodeDriver n γ N init ∗ nodeConfig n γ N ⟨0, γ.c0⟩ ∗ nodeRunning n γ N 1 }}

-- a Ready with entries `es ≠ []` from index `k`, no snapshot: the log from `k` on (current contents
-- `old`) for the client to write, and the Ready's committed entries below `k`, frozen (from `j = f+1`
-- before accept; raft's frozen prefix grows to include them: N5)
readySnap (none), es ≠ []:  … ∗ storLog st k (own 1) old ∗ storEnd st (k + |old|) ∗
     storLog st j □ ceBelow ∗ ⌜es indexed k, k+1, … ∧ j + |ceBelow| ≤ k⌝
readySnap (none), es = []:  … ∗ storLog st j □ ceBelow                   -- no log resource lent (N2)

-- a Ready with a snapshot `sv` (s = sv.Index): every log resource above the frozen prefix, the right
-- to install it, and what it is
readySnap (some):  … ∗ storLog st (f+1) (own 1) old ∗ storEnd st (f + 1 + |old|) ∗
     snapGiven γ id s ∗ snapshotValid γ sv ∗ ⌜f < s ∧ ce = []⌝          (M2: f + 1 ≤ s)

-- Advance takes back the batch: a frozen prefix (its delivered entries, possibly empty; B1) and the
-- owned rest
node.Advance pre (no snapshot, es ≠ []):  … ∗ storLog st k □ a ∗ storLog st (k + |a|) (own 1) b ∗
                                          storEnd st (k + |es|) ∗
                                          ⌜es = a ++ b ∧ a within the Ready's CommittedEntries⌝
node.Advance pre (no snapshot, es = []):  …                                  (nothing)
node.Advance pre (snapshot):  … ∗ storCompacted st s ∗ storLog st s □ [⟨s, sv.Term⟩] ∗
                              storLog st (s+1) (own 1) es ∗ storEnd st (s + 1 + |es|)
node.Advance post:  … ∗ nodeAppliedLb γ id a'
  -- a' = the delivered index (`sv.Index` after a snapshot Ready: N6). If a `restore` superseded the
  -- Ready's snapshot, `stableSnapTo` is ignored and `applied := s` still, so a' = s. The frozen
  -- delivered prefix the client needs afterwards it already holds (the Ready's `ceBelow`, and what it
  -- froze of its batch).
```

## 4. Raft's invariant, and why each step is provable

Raft's `ownRaftLog` holds, beside `unstable` (`offset`, `offsetInProgress`, entries `uents`, its snapshot)
and the stable entries `sents` (indices `c+1 … offset−1` above the compaction point):

- `storCompacted st c`, and the frozen prefix `F` (indices `c … f`, `F[0]` the entry or dummy at `c`):
  `storLog st c □ F`;
- `π`, the **physical log** raft accounts for (indices `c …`). With no `Ready` out (or one without
  entries), raft holds `storLog st (f+1) (own 1) (π from f+1) ∗ storEnd st (end of π + 1)`. With one out
  with entries, raft holds that part below `k`, the client holds `[k, …)` and `storEnd`, and `π` continues
  with the batch the client must return.

Invariant facts (A1: today's `LogPersistOk`, `InvRaftlog.lean:508-513`, over `π`; N8's P0 made explicit):

- (P0) `offset ≤ offsetInProgress ≤ offset + |uents|`;
- (P1) with no snapshot pending, `sents ++ uents.take (offsetInProgress − offset) <+: π` above `c`
  (everything raft handed out is there, or is the batch out);
- (P2) `offsetInProgress = offset + |uents|` and no snapshot pending → `π = sents ++ uents` above `c`;
- (P3) `uents = []` and no snapshot pending → no log resource is out;
- (F) `f ≤ applying < offsetInProgress` and `f ≤ committed`; `F` agrees with `π` (N3);
- (C) `c ≤ f`; with `storCompacted_bound` and the law of `snapGiven` below, at each use: `c ≤ applied`,
  or a snapshot is pending, or `run` is between `<-advancec` and `rn.Advance` with `c ≤ delivered` (B3,
  today's `RNState.flw`);
- (G) `snapGiven γ id k` → `k ≤ applied`, unless a snapshot is pending or the `Advance` rendezvous is
  open (N7);
- (T) at `c`, storage and the log agree by term only (the dummy);
- with a snapshot pending, `π` is arbitrary above `f` (raft reads no storage then).

The steps (raft v3.7: `log_unstable.go`, `log.go`, `rawnode.go`):

- **`truncateAndAppend`** (`log_unstable.go:200-222`). The append case leaves (P1) alone; `fromIndex ≤
  offset` shortens `sents` to a prefix of itself; the default case lowers `offsetInProgress`. `F` is never
  touched: `raftLog.append` panics on `fromIndex ≤ committed` (`log.go:137-139`), so `fromIndex > f`.
- **`acceptReady`** (`acceptInProgress`, `acceptApplying`). If `es ≠ []`: split raft's owned part of `π`
  at `k = offsetInProgress`, hand out `[k, …)` with `storEnd`. Freeze the `Ready`'s committed entries
  below `k` (in `π` by (P1); committed entries are never rewritten), extend `F` with them, and hand them
  out persistently (A4, N5). With a snapshot: hand out from `f + 1` with `storEnd`, and mint `snapGiven`.
  If `es = []` and no snapshot: nothing is lent (N2), and (P3)/(P2) give `π = sents ++ uents` in the one
  reachable case `uents ≠ []` (a term change while the earlier `Ready` was out: review 3, `rawnode.go:272`,
  `raft.go:1166-1180`).
- **Reads while a `Ready` is out.** Raft reads storage only below `offset ≤ k` (`term`, `log.go:391-405`;
  `slice`, `log.go:506-514`; `restore`'s `matchTerm`, `raft.go:1904`), and only at `≥ fi − 1 ≥ c` after a
  `firstIndex()` (`log.go:398-405, 500, 555-557`): over raft's two pieces, `F` and its owned part of `π`.
  With a snapshot pending, raft reads no storage (`log.go:300-320, 391-403, 555-557`).
- **`LastIndex`.** Called only with no unstable entries and no snapshot (`log.go:311-320`). (P0) and (P3)
  give nothing out, so raft holds `storEnd`, and (P2) gives `π = sents`: the answer `end of π` is raft's
  last index.
- **Compaction.** `nextCommittedEnts` reads from `applying + 1`, `hasUnappliedConfChanges` from
  `applied + 1` (`log.go:229-242`, `raft.go:1002`), `lastEntryID` the last index; by (C) none sees
  `ErrCompacted`. Other readers handle it (`matchTerm`, `findConflictByTerm`, `maybeSendAppend` → a
  snapshot).
- **`Advance`** (`stableTo`, `stableSnapTo`, `appliedTo`/`appliedSnap`). The client returns the batch, a
  frozen piece and an owned piece; raft joins them into `π`, re-establishing (P1)/(P2). If `stableTo`
  takes, the entries that agree become stable, including ones an earlier ignored acknowledgement's batch
  wrote ((P1) says they are in `π`). If it is ignored (truncation, `restore`, a term change, a superseded
  snapshot), (P1) still holds by Log Matching (review 3 checked all four causes). Freeze the delivered
  prefix (`f :=` the delivered index, possibly past `offset`) and hand it out. After a snapshot: `c := s`,
  `F := [⟨s, t⟩]` (the dummy, (T)), `f := s`, the pieces below `s` dropped (N1), `applied := s`.
- **`restore`** (`offset := sv.Index + 1`): `π` above `f` becomes arbitrary (a snapshot is pending); `F`
  stays (the snapshot's log extends it, `raft.go:1853`).
- **`Snapshot()`'s answer** (`maybeSendSnapshot`): pre `storCompacted st c'` from the `ErrCompacted` that
  sent raft there; post `c' ≤ sv.Index`, so `IsEmptySnap` cannot panic (`raft.go:678-680`); the
  `ErrUnavailable` path of `term(pr.Next − 1)` is excluded by the protocol invariants `1 ≤ pr.Next ≤
  lastIndex + 1` (`PrvalsOk`).

## 5. The asynchronous mode (not proved now; the same resources)

Several batches may be out, acknowledged in order (the local append thread). The client holds `[k₁, …)`
and `storEnd` from the first one out with entries. A later batch hands out only `[fromIndex, k₁)` when it
overwrites below `k₁`, nothing otherwise (and nothing for a batch with no entries). An acknowledgement
returns the part below the next outstanding batch's start; the last one returns the rest with `storEnd`.
An acknowledgement's `(index, term)` is `lastEntryID` at `Ready` time (`rawnode.go:355-357`), so it can
attest entries of an earlier batch whose own acknowledgement the term check dropped: (P1) over the list
of batches out allows it. `nodeAppliedLb` comes from `node.Step`'s spec for `MsgStorageApplyResp` (there is
no `Advance` in that mode), a rendezvous like `Advance`'s; `Step` must then admit local response messages.

## 6. Why implementations can prove `isStorage` (sketch)

`MemoryStorage` with a client invariant:
- a ghost map index ↦ entry with fractional points-to and a discarded state (`storLog`), an end token
  holding the exact last index (`storEnd`; `Append` holds the tail up to it, `Compact(x)` needs `x ≤`
  the last index, `ApplySnapshot` resets it to `s+1`), a monotone compaction point with its justification
  (`storCompacted`; `storCompacted_bound` from what the client's `Compact`/`ApplySnapshot` was given);
- the stored snapshot owned exactly by the client (kvreconf), or shared in an invariant with a persistent
  lower bound from both `CreateSnapshot` outcomes (etcd's two writers; `CreateSnapshot` must allow
  `ErrSnapOutOfDate` without the client knowing the stored index: etcd's race with the next `ApplySnapshot`
  is benign, `server.go:2106`);
- `Append(es)` at `k` takes `storLog st k (own 1) old ∗ storEnd st (k + |old|)` and gives the same with
  `es`; `ApplySnapshot` takes the whole owned log above the frozen prefix, `storEnd` and `snapGiven`, and
  gives the snapshot `Advance`'s resources; `CreateSnapshot(i)` reads the term from the caller's `storLog`
  at `i`, which must be frozen, and needs `snapshotValid`; `Compact(x)` needs `storLog st x □ [e] ∨
  storCompacted st x`, `x ≤` the stored snapshot and `nodeAppliedLb γ id x`.

## 7. Clients

- **kvreconf** (`run`): with a snapshot, `ApplySnapshot` first (it succeeds: `sv.Index > applying ≥` its
  stored snapshot), then `Append(rd.Entries)`; apply the committed entries; `maybeSnapshot(i)` with
  `snapshotValid` (the committed prefix, `confAt`, `ownSnapsMade`) and the term from what it holds at `i`
  (the `Ready`'s frozen `ceBelow` when `i < k`, its own batch range otherwise, the frozen delivered prefix
  after `Advance`); `Advance` with the range back (the delivered prefix of its batch frozen if it froze
  it); `maybeCompact(x)` for `x ≤ min(applied, its snapshot)` with `nodeAppliedLb` and the frozen entry at
  `x` (after an install, `nodeAppliedLb s`). It freezes its batch's committed prefix before snapshotting
  in it.
- **etcd's server** (with the fork's fix: snapshots after `raftAdvancedC`): the raft goroutine appends and
  installs; the apply thread snapshots and compacts with `nodeAppliedLb` and the frozen delivered prefix
  through its hand-off; its periodic `Compact(appliedi − 5000)` after an install is the
  already-compacted case (M1). Its snapshots carry `nil` data: its `snapMade` must accept that (etcd's
  own obligation).

## Limitations

- Fresh boot only (`storEnd st 1`): etcd's restart from disk is outside the contract, as today.
- One raft node per storage and id: kvreconf uses fresh ids.

## Removed

`StorState` (`prev`, `pend`, `fl`, `hd`, …), `ownStorage`, `appendTok`/`appendedTok`/`appendRight`/
`appendReceipt`/`advReceipt`, `storCut`, `storCap`, `storFloor`, `storCert`, `storTermsAt`, `storTermsPre`,
`storHoldsLb`, `appendReceipt_holds`, the hand-out/absorb/floor laws, the loan of the whole storage at a
snapshot `Ready`, `snapshotCert` (now `snapshotValid`), `storageCertLink`/`storCertOk`, and the premises
`σ.fl = 0`, `σ.hd = 0`.
