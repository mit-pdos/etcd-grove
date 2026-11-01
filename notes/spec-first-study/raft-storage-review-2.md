# Review 2: candidate 17 (raft's storage contract as range ownership)

Reviewed at `raft-unified` 6657289b28, in the worktree `raft-spec-review`, read-only.

**The Go checkout is not at the pin.** `.lake/go-src/raft` is at `509271dac`, which is a1's parent.
The pin is `565c2bd` (a2). `log.go` and `log_unstable.go` have no a2 changes. For `appliedSnap`,
which a2 changed, I read the order of operations in the translation and in its proof
(`Proof/go_etcd_io/raft/v3/raft__appliedSnap.lean:71-243`).

`.lake/go-src/etcd` lacks the fork's fix 1 (`applyAll` waiting on `raftAdvancedC`). The
translation does have that wait (`Code/go_etcd_io/etcd/server/v3/etcdserver.lean`, `applyAll.impl`).
Line numbers below are from the checkouts.

The coordinator's mid-review variant (`storLog st k dq es` with fractions, no `storFrozen`, no
`storCompacted_frozen`) is judged in §V.

## Verdict

The direction can be proved, and §2's reads are nearly complete. Two things block it.

1. **§4's invariant is too coarse to prove `Advance` after an ignored acknowledgement (A1).**
   The proof needs the agreement invariant that the current proof has (`LogPersistOk`). The
   candidate replaces it with "S's uncommitted tail ++ stale entries". That cannot describe entries
   that are physically present and agree with raft's log, but are still unstable.
2. **Invariant (a) and `readyRest`'s premises are false in reachable states (A2).** `k > committed`
   and `k ≤ |stable| + 1` both fail.

Raft also reads storage at index 0, and no premise covers that read (A3). kvreconf's snapshot in
the middle of a `Ready` needs a resource the candidate never gives (A4).

Review 1's A1, A2, B1, B2 and B5 are addressed (§VI). The LastIndex argument is sound once A1's
invariant is in place. The asynchronous mode generalizes, with one gap: where `nodeAppliedLb` comes
from (B4).

## What is good

- **The ranges replace the whole loan, receipt and floor machinery,** and keep its content. The
  client owns `[k, P)` while a `Ready` is out. Raft owns everything else, and reads only below
  `offset ≤ offsetInProgress = k`:
  - `term`: `log.go:391-405`; when `unstable` does not answer, the read is below `offset` or out of
    range.
  - `slice`: `log.go:506-514`, with `cut = min(hi, offset)`.
  - The `restore` probe `matchTerm(sv)`: `raft.go:1904`, below `offset` when it reaches storage.
- **B5 of review 1 is solved by the structure itself.** After a snapshot `Ready`, `Append` at
  `sv.Index+1` needs `storLog st (sv.Index+1) _ ∗ storEnd`. Only `ApplySnapshot` produces those.
  This matches `MemoryStorage.Append`'s "missing log entry" panic (`storage.go:321-323`) and
  `ApplySnapshot`'s wipe (`storage.go:235-236`).
- **Raft reads no storage while a snapshot is pending,** as the candidate says.
  - `firstIndex`, `lastIndex`, `term` and `slice` answer from `unstable` (`log.go:58-96, 294-320,
    398-403, 555-557`).
  - `hasUnappliedConfChanges`' `ErrCompacted` from `unstable` cannot happen: `hup` refuses to
    campaign through `promotable` (`raft.go:979, 1938-1941`).
  - So `snapGiven`'s compaction beyond `applied` is harmless. The window ends inside one
    `appliedSnap`: `stableSnapTo`, then `appliedTo`, with no read between them (a2 order,
    `raft__appliedSnap.lean:75, 141`).
  - The read in that window is a2's `lastIndex` (`raft__appliedSnap.lean:170`). It comes after
    `appliedTo`, and raft by then holds the returned resources, so the LastIndex triple applies.
- **`storCompacted_bound` closes review 1's A1.** The bound is applied (`nodeAppliedLb`, only from
  `Advance`) or a handed-out snapshot. That is exactly what `nextCommittedEnts`/`scan` from
  `applied+1` (`log.go:229-242`, `raft.go:1001-1019`) and `mustCheckOutOfBounds`' `fi ≤ lo`
  (`log.go:555-557`) need. It also needs the advance-rendezvous case of B3.
- **The error outcomes match `MemoryStorage`.**
  - `Entries`: `ErrCompacted` exactly when `lo ≤ c` (`storage.go:148-151`).
  - `Term`: `ErrCompacted` exactly when `i < c` (`storage.go:173-176`).
  - Neither triple's post allows `ErrUnavailable`. Raft's `slice` panics on it (`log.go:517-518`).
- **`maybeSendSnapshot` gets what it needs from the `Snapshot` triple.** Its pre is
  `storCompacted st c`, which comes from the `ErrCompacted` that sent raft there. Its post gives
  `c ≤ sv.Index`.
  - So `IsEmptySnap` cannot panic (`raft.go:678-680`).
  - `BecomeSnapshot(sindex)` keeps `sindex ≥ pr.Next > pr.Match`.
  - The `ErrUnavailable` path of `term(prevIndex)` (`raft.go:625-629`) needs `pr.Next ≤ lastIndex+1`
    instead. That is a protocol invariant, not a storage fact.
- **`snapshotValid` is a sound replacement for the certificate.** Every part is a persistent
  client-visible fact, and it can be built from what kvreconf and etcd hold.

## Findings

### Tier A (blocking: provability)

**A1. §4 loses the agreement between storage and raft's unstable entries, so `Advance` after an
ignored acknowledgement cannot be proved.**

*Principle:* the invariant must hold across `stableTo`, including after an earlier ignored
acknowledgement.

*Evidence.* The scenario is reachable in synchronous mode. It needs a leader change while a
`Ready` is out.

1. Batch `[5..9]` is out: `offset = 5`, `offsetInProgress = 10`.
2. A `MsgApp` matches at 7 and conflicts at 8. This is `truncateAndAppend`'s third case
   (`log_unstable.go:213-220`): `offsetInProgress := 8`.
3. `Advance`: `stableTo(9, oldterm)` is ignored, because the term is missing or mismatched
   (`log_unstable.go:139-158`).
4. Storage now physically holds `[1..9]` from batch 1. Raft's stable log `S` is `[1..4]`, and
   `unstable` holds `5, 6, 7` (old, but agreeing) and `8'…`.
5. The next `Ready` starts at `k = 8` (`nextEntries`, `log_unstable.go:100-106`). Its `stableTo`
   succeeds and sets `offset := last'+1` (`log_unstable.go:159-162`). Entries `5..7` are now stable
   *because batch 1 wrote them*.

§4 cannot account for this. It classifies raft's `storLog` as "S's uncommitted tail, and stale
entries (no longer in raft's log)", and entries `5..7` are neither. Its `Advance` step says "raft's
stable log is `S[<k] ++ es`". Here `S[<8] ++ es` has a gap at `[5, 8)`.

The current proof keeps exactly this invariant:
- `LogPersistOk` (`InvRaftlog.lean:508-513`): `sents ++ uents.take ipo <+: stored`, and
  `ipo = |uents| → sents ++ uents = stored`.
- Its docstring (lines 503-507) cites this very case: "a truncating `MsgApp` lowers
  `offsetInProgress` below entries the storage still holds, and the acknowledgement `Advance` steps
  next may move them stable".

*Caller affected:* `RawNode__Advance`, `raftLog__stableTo`, and every read below `offset`. The read
post `t = es[i-k].term` must equal raft's term there.

*Restatement.* Write `π` for the physical log: raft's contents, or, while a `Ready` is out, raft's
contents below `k` followed by what the client must return (`es`). Replace "S's uncommitted tail,
and stale entries" and (b) with:
- `(sents ++ uents.take (offsetInProgress − offset)) <+: π`;
- when every unstable entry is handed out (`offsetInProgress = offset + |uents|`) and no snapshot
  is pending, `π = sents ++ uents`.
- With a snapshot pending: `π` is arbitrary above `F`. Raft reads nothing in that window.

The second clause is the precise (b): stale entries exist only while some unstable entry has not
been handed out, or a snapshot is pending. LastIndex's argument then follows. With `unstable`
empty, `ipo = 0 = |uents|`, so `π = sents`, and storage's end is raft's `lastIndex + 1`.

**A2. Invariant (a) `k > committed`, `readyRest`'s `⌜k > committed ≥ applied ∧ k ≤ |stable|+1⌝` and
"F = S's committed prefix" are false or unprovable.**

*Evidence.*
- **`k ≤ committed` happens.** A follower receives entries together with a commit index covering
  them: `maybeAppend` → `commitTo(min(committed, lastnewi))` (`log.go:127-129`). The next `Ready`
  hands out entries at or below `committed`.
- **Committed entries in the batch are delivered in the same `Ready`.** In synchronous mode
  `applyUnstableEntries()` is `true` (`rawnode.go:144, 445-447`), so `maxAppliableIndex` is
  `committed` (`log.go:267-273`).
- **`k ≤ |stable|+1` fails** in A1's scenario: `k = 8`, `|stable| = 4`.
- **Delivered entries can be in the batch while its acknowledgement is ignored.** Batch `[5..9]`,
  `committed = 7` (delivered `5..7`), truncated at 8. `stableTo` is ignored, so `S` stays `[1..4]`.
  `Advance`'s post must still give `storFrozen st 1 (delivered)` up to 7, which is past `S`. The
  candidate's own `Advance` post ("storFrozen of the delivered (committed, stable) prefix") assumes
  the delivered prefix is stable, and it need not be.

*What is true:*
- `k ≥ offsetInProgress > |F|`.
- Truncation never reaches `F`: `append` panics on `fromIndex ≤ committed` (`log.go:137-139`), and
  `F ⊆ committed`.
- `F` lies within the agreeing region `[1, offsetInProgress)` of A1.

*Restatement.*
- (a) becomes `|F| < offsetInProgress` and `|F| ≤ committed`.
- `F` is "a prefix of the committed log that is physically present and agrees". At `Advance` it is
  set to the delivered prefix, which may extend past `offset`.
- `readyRest` states `⌜|F| < k⌝`. Drop `k > committed` and `k ≤ |stable|+1`: the latter is implied
  by owning `storEnd st (k+|old|)`.

**A3. Raft reads `Term(0)` from storage, and no premise covers index 0.**

*Evidence.*
- A fresh follower has `pr.Next = 1`, so `maybeSendAppend` reads `term(0)` (`raft.go:624-625`).
- So does `maybeAppend` with `prev = (0, 0)` (`log.go:110`, `matchTerm`).
- So do `lastEntryID` and `isUpToDate` on an empty log (`log.go:378-381`).
- With `fi = 1`, `term(0)` passes `0+1 < fi` and calls `storage.Term(0)` (`log.go:398-405`).
  `MemoryStorage` answers the dummy's term 0 (`storage.go:169-182`).
- Every read premise of §2 requires `storFrozen`/`storLog st k es` with `k ≥ 1`, and raft's `F`
  starts at 1. The same gap appears at the compaction point `c` after a snapshot. There the term
  comes only from `storCompacted_frozen`'s unstated `⌜…⌝` (open point 2).

*Restatement.* Make index 0 an ordinary entry of the contract.
- `StartNode`/`RestartNode` take `storFrozen st 0 [e₀]` (or `storLog st 0 □ [e₀]` in §V's variant),
  with `e₀.term = 0`.
- Raft's `F` starts at 0.
- `LastIndex`'s pre and post become `storFrozen st 0 F ∗ storLog st |F| U ∗ storEnd st (|F|+|U|)`,
  with `i + 1 = |F| + |U|`.

**A4. kvreconf's snapshot in the middle of a `Ready`, at an index below `k`, has no resource for
`CreateSnapshot`'s term read.**

*Evidence.*
- kvreconf calls `maybeSnapshot` after any applied entry, before `Advance` (`kv.go:366-369`), at
  `r.index` (the last applied entry, `kv.go:385-397`).
- The `Ready`'s committed entries are `[applied+1, committed]`. Some of them can be *stable
  entries below `k`*: a leader's own stable tail that only now became committed. That region
  `[|F|+1, k)` is raft's `storLog`.
- §6's `CreateSnapshot(i)` "reads the term at `i` from what the caller holds there (frozen or
  owned)". The client holds neither. §7's "its range mid-`Ready`, `storFrozen` after `Advance`"
  misses this case.
- `MemoryStorage.CreateSnapshot` reads `ents[i-offset]` (`storage.go:243-257`), so the
  implementation does need a resource there.

etcd is not affected. With the fork's fix 1 it snapshots only after `raftAdvancedC`, which comes
after `Advance` (translated `applyAll`).

*Restatement.* At `acceptReady`, raft freezes (`storLog_freeze`) its own committed entries below
`k` that the `Ready` delivers. That is sound, because committed entries are never rewritten
(`log.go:137-139`). `readyRest` then hands out `storFrozen st (|F|+1) ce_below_k`. In the
synchronous mode, freezing the batch's delivered entries waits for `Advance`; see B1.

### Tier B (must fix in the statement)

**B1. `Advance`'s pre should accept the batch's delivered prefix already frozen.**

The pre is "exactly the batch" as `storLog st k es`. A client that freezes the committed prefix of
its batch after `Append`, to snapshot there before `Advance` (kvreconf at `kv.go:366-369`, when
`r.index ≥ k`), can no longer give it back.

*Restatement:* `storFrozen st k a ∗ storLog st (k+|a|) b ∗ storEnd …` with `es = a ++ b` and
`k + |a| − 1 ≤ |delivered|`. Raft never writes committed entries. In §V's variant this is simply
`storLog st k □ a`.

**B2. `readySnap (some)` must keep `⌜|st.delivered| < sv.Index⌝` and `ce = []`.**

kvreconf ignores `ApplySnapshot`'s error, then sets `snapIndex := sv.Index` (`kv.go:355-357`). A
later `CreateSnapshot` panics on `ErrSnapOutOfDate` (`kv.go:397-399`) if that index was wrong.
`ApplySnapshot` fails when the stored snapshot is at least `sv.Index` (`storage.go:229-232`).

kvreconf's stored snapshot is at an index it has applied, so at most `|delivered|`. So it needs
`sv.Index > |delivered|`. Today's `readySnap` states this (`InvNode.lean:563-565`). The candidate's
`…` must keep it.

The implementation's `ApplySnapshot` spec should then say "succeeds when the stored snapshot's
index is below `sv.Index`", which the client's exact snapshot (§6) decides.

**B3. (d) must include the advance rendezvous.**

`node.Advance` returns at the `advancec` send (`node.go:555-560`), and the client then has
`nodeAppliedLb |delivered|`. Raft's `applied` moves later, in `rn.Advance` (`node.go:443-446` →
`rawnode.go:478-481` → `raft.go:1205-1209`).

*Restatement:* (d) is "`c ≤ applied`, or `run` is between `<-advancec` and `rn.Advance` and
`c ≤ |delivered|`". `rn.Advance`'s first steps are the self-addressed `msgsAfterAppend`
(`rawnode.go:411-417`). As a leader they can reach `maybeSendAppend`, which reads storage but
never at or below `applied` in a way that panics: `ErrCompacted` there is handled. This is today's
`RNState.flw` (`InvRaftlog.lean:650-663`); state it.

**B4. §5: in the asynchronous mode, `nodeAppliedLb` must come from `Step(MsgStorageApplyResp)`.**

There is no `Advance` in that mode (`rawnode.go:470-472`). The applied index moves when the client
steps the apply thread's response (`raft.go:1203-1209`).

So `node.Step`'s spec for local response messages must take the returned ranges and give
`nodeAppliedLb`. That is again a rendezvous: `recvc` is received and `r.Step` runs in the same arm
(`node.go:394-399`). Today's `Step` spec excludes local messages.

The rest of §5 is plausible, with the same resources:
- Batches are acknowledged in order.
- A truncating later batch hands out only `[fromIndex, k₁)`.
- An acknowledgement whose next batch starts below it returns nothing; its `stableTo` is ignored,
  by Log Matching or because the entry is missing.
- `LastIndex` still needs nothing out.

So "easily generalizable" holds, apart from the `Step` spec and A1's invariant extended to a list
of batches.

**B5. Ignored acknowledgements after `restore` also need Log Matching, and the candidate does not
say so.**

`restore` while a non-snapshot `Ready` is out (`raft.go:1913`; `log_unstable.go:192-198`):
- An acknowledgement at `last ≤ sv.Index` is ignored structurally (`log_unstable.go:145-148`).
- At `last > sv.Index`, entries appended since the restore can be at `last`. The acknowledgement
  is ignored only because `restore` ran: the term at `sv.Index` mismatched (`raft.go:1904-1912`),
  so by Log Matching no later entry of the old batch matches the leader's log.

State this case, since it uses the same protocol invariant as truncation.

**B6. Obligation 3 contradicts `ApplySnapshot`.**

The obligation reads "Compaction only of frozen indices". But `ApplySnapshot` compacts
`[j, sv.Index]`, which the client holds as `storLog` (§6). It must, because freezing stale
contents there would leave the dummy's term inconsistent with them.

*Restatement:* "`Compact(x)` only of frozen indices, `x ≤` the stored snapshot's index, and
`x ≤` a `nodeAppliedLb`. `ApplySnapshot` only with the whole non-frozen log, its `storEnd` and
`snapGiven`."

**B7. The `Entries` premise must allow a range that crosses from `F` into raft's `storLog`.**

`nextCommittedEnts` reads `[applying+1, …)` (`log.go:229-239`). `maybeSendAppend` reads
`[pr.Next, …)` (`raft.go:640`). Both can start in `F` and end in `[|F|+1, offset)`, but the premise
is `storFrozen st k es ∨ storLog st k es` for one region.

*Restatement:* `storFrozen st k a ∗ storLog st (k+|a|) b`, with `es = a ++ b`. In §V's variant this
is automatic: `storLog st k dq es` at mixed fractions, joined.

### Tier C (minor)

- **C1.** `snapshotValid γ N sv` never uses `N`. Drop the parameter.
- **C2.** `storCompacted_frozen`, as stated ("frozen at *any* contents"), means `storFrozen` has no
  agreement law. Two `storFrozen` facts at the same index may disagree. Say so in its docstring,
  or adopt §V, which removes the law.
- **C3.** `isStorage`'s witnesses are keyed by `(γ, N, id)`. That needs one raft node per id
  (review 1, C3). It still holds: kvreconf uses fresh ids. Say so.
- **C4.** The start spec covers only an empty storage (`storEnd st 1`). etcd's restart from disk
  (`ApplySnapshot` at bootstrap) is outside the contract. Today's proof covers only a fresh boot
  as well; note it as a limitation.

## §V. The coordinator's variant (fractional `storLog`, no `storFrozen`, no `storCompacted_frozen`)

**The claim about raft's reads holds, with one strengthening of `FirstIndex`.**

*Every storage read is at `≥ fi − 1`, with `fi` from a `FirstIndex` call made just before.*
- `raftLog.term` reaches `storage.Term(i)` only after `i + 1 < firstIndex()` failed
  (`log.go:398-405`).
- `slice` reaches `storage.Entries(lo, …)` only after `lo < fi` failed (`mustCheckOutOfBounds`,
  `log.go:500, 555-557`).
- `storage.Term` and `storage.Entries` are called nowhere else (`log.go:405, 514` are their only
  callers). `allEntries` is test-only, and `restore`'s `matchTerm` goes through `term`.
- A compaction between the `FirstIndex` and the read is the "or compacted" case:
  - `Term` → `ErrCompacted` → `raftLog.term` returns it (`log.go:409-410`). Its callers handle it:
    `matchTerm`, `findConflictByTerm`, and `maybeSendAppend` (which goes to the snapshot).
  - `Entries` → `ErrCompacted` from `slice` (`log.go:515-516`). This panics only in
    `nextCommittedEnts` and `hasUnappliedConfChanges`, and `storCompacted_bound` with (d) excludes
    both (`lo > applied ≥ c`).

*The strengthening:* to know `i ≥ s` after a snapshot, raft needs `fi − 1 ≥` the compaction point
it has observed. The candidate's `{{ True }} FirstIndex` does not give that.

*Restatement:* `{{ storCompacted st c }} st.FirstIndex() {{ fi, ⌜c + 1 ≤ fi⌝ ∗ storCompacted st (fi − 1) }}`.
Raft keeps `storCompacted st s` from the snapshot's `Advance` (and `storCompacted st 0` from start).
With this, the post-snapshot resources `storCompacted st s ∗ storLog st s □ [dummy] ∗
storLog st (s+1) 1 es ∗ storEnd` cover every read. `Term(s)` is answered by the dummy, and
`Entries` starts at `≥ fi > s`.

**What else the variant fixes or needs:**
- **It fixes A3.** Start with `storLog st 0 □ [e₀]`.
- **It fixes B1 and B7** directly.
- **It removes C2.** Agreement holds on overlaps.
- **It needs exclusivity:** `storLog st k 1 [e] ∗ storLog st k dq [e'] ⊢ False`. Then `Append`'s
  full fraction excludes persisted ranges. Validity of fractions gives this for free; state it.
- **It needs the agreement law on overlaps,** not only at a common `k`.
- **The dummy is not raft's entry.** Raft's log has `l[s]`, with data, while the storage's index `s`
  holds `{Index s, Term t}`. Raft's invariant must relate storage and log by *term only* at the
  compaction point. Raft only reads `Term(s)` there, since `Entries` starts at `> s`.
- **`ApplySnapshot` may overwrite the ghost value at `[j, s]`.** It takes the full fraction of
  `[j, P)` with `j = |F|+1 ≤ committed+1 ≤ s` (`raft.go:1853`). So the implementation can do it
  without breaking agreement with any discarded fragment.
- **"Compaction only of discarded ranges" keeps B6's exception:** `ApplySnapshot` compacts
  full-fraction ranges it consumes.

I recommend the variant. It is simpler: one predicate, no "any contents" law. It also fixes A3, B1
and B7.

## §VI. Review 1's findings

- **A1 (compaction bounded by applied): addressed** by `storCompacted_bound` and `nodeAppliedLb`
  from `Advance`. It needs B3's rendezvous clause in (d).
- **A2 (exact snapshot): addressed in §6.** The implementation gives the client its exact snapshot.
  It is not in the contract, which is right, since raft never writes the snapshot. kvreconf owns
  it. etcd's two writers can share it in an invariant only if `MemoryStorage`'s own specs for
  `CreateSnapshot`/`ApplySnapshot` are atomic over it, or give a persistent `storSnapLb`. With
  ordinary triples, etcd's apply thread must return a `storSnapLb i` on both `CreateSnapshot`
  outcomes (review 1, B4) for its `Compact`'s `x ≤` the stored snapshot. That belongs to
  `MemoryStorage`'s spec; flag it there.
- **B1, B2 (InitialState): addressed.** It is outside the contract, and a premise of `RestartNode`.
- **B5 (append after ApplySnapshot): addressed** by the ranges (above).

## Open points answered

1. **The split at the committed point:** right in principle. But the split point is the *frozen*
   prefix `|F|`, which can exceed `offset` (A2). Compaction never reaches a `storLog` region:
   `c ≤ applied ≤ |F|` by the bound and (d), and A2's `|F| < k`.
2. **`storCompacted_frozen`'s term:** the side condition is `k + |es| = c + 1 → last term = t`,
   which needs `storCompacted st c t`. Better, drop the law (§V).
3. **(b) is false as stated;** A1 gives the precise form. Ignored acknowledgements are covered once
   it is that form. `restore` during a `Ready` is covered with B5's Log Matching case.
4. **Reads:**
   - `matchTerm` at `fi − 1` is covered (by `F`) except at 0 (A3).
   - `findConflictByTerm` (`log.go:182-194`) and `maybeSendAppend` (`raft.go:625, 640`) are
     covered, the latter with B7's crossing range.
   - `scan`/`hasUnappliedConfChanges` (`raft.go:1001-1019`) and `nextCommittedEnts` are covered,
     with B3 and B7.
   - Every read stays below `offset ≤ k`, so the `Ready`'s range is never needed.
5. **The clients:**
   - kvreconf works with A4, B1 and B2.
   - etcd (with fix 1) works: everything after `Advance` arrives through `raftAdvancedC`. That
     leaves `storSnapLb` for its `Compact` (§VI A2).
   - Two writers: the raft goroutine's ranges and the apply thread's persistent facts are disjoint.

## Go bugs

None new. The design rests on the known issues `etcd-compact-past-raft-applied`,
`raft-compact-past-snapshot` and `raft-memorystorage-initialstate-unlocked`.

## Ranking (need of revision)

1. **§4's invariant:** A1, A2 and B3, B5.
2. **§3's hand-out and `Advance`:** A2's premises, A4, B1, B2.
3. **§2's read triples:** A3, B7, and `FirstIndex`'s pre (§V). Adopt §V's fractional `storLog`.
4. **§2's obligations and §6:** B6, and `storSnapLb` for etcd.
5. **§5:** B4.
