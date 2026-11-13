# M2, the storage side: review round 5 (2026-10-30)

Reviewed: branch `m2-storage`, `HEAD` = `44da86ab00` (the Q8 notes commit after `7786981f07`). This
is step 2's **third and last** round under `notes/spec-first-plan.md`'s Review rule. Step 1's
statements, which converged in round 3, were checked only for churn.

**Targets**
- Every Draft module (`git ls-files | grep M2StorageDraft`, 15 modules). The focus is on the new
  ones: `mvcc/M2StorageDraftIndex.lean`, `mvcc/M2StorageDraftChain.lean` and
  `etcdserver/M2StorageDraftScope.lean`, and on what round 4's repair changed in
  `mvcc/M2StorageDraftRestore.lean` ("mvcc R").
- The switched internals (`git diff lean...HEAD -- Proof Spec`, Drafts excluded). They are
  unchanged since round 4: `git diff --stat f3282099c3 HEAD -- Proof Spec` touches only Draft
  modules.
- `notes/m2-storage-plan.md`, "After review round 4": the 37-item approval list.

**Method.** I formed my view from the Drafts, the Go code at the pin (`.lake/go-src/etcd`) and the
callers' proofs, and read rounds 1-4 only afterwards. I built nothing and ran nothing. Nothing in
the repository changed except this file.

**Abbreviations.** `mvcc/` = `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/`; `etcdserver/` =
`Proof/go_etcd_io/etcd/server/v3/etcdserver/`; "Index", "Chain", "Scope", "mvcc R" as in the plan.

**Go.** No new Go bug. Two existing issue files bear on this round:
- `issues/etcd-txn-check-intervals-sibling.md` (finding B1 rests on it);
- `issues/etcd-restore-scheduled-compact-zero.md`. Its "How the proof handles it: not yet" is now
  stale, since Q7 (a) is drafted. Update it at the switch.

## Summary

**Two first-tier findings. Neither comes from round 4's repair of A1/A2 as such:**
- **B1** is a new premise that the repair introduced.
- **B2** is a gap in the realization of the user's Q8 (a).

- **B1. `KeyOnceAt` (item 33) is an unmarked scope restriction with a false justification.** Its
  docstring says "etcd's transactions never touch a key twice (`checkIntervals` rejects …)". The
  repository's own issue file shows otherwise: `checkIntervals` admits
  `Then(Txn(Then(Put k)), Txn(Then(Delete k)))`, a put and then a delete of `k` in one revision.
  - On such a log, the drafted invariant `IdxCRepN` fails after a mid-job image (worked example
    below). Go is right there: every read answers correctly.
  - So the premise excludes a gRPC-admitted workload that the code handles. It is needed only by
    `IdxCRepN`'s choice of an `Int` (main-revision) compaction level.
  - `cx3_not_compacted`, offered as the proof that the premise is needed, uses two puts of one key
    in one revision, which `checkIntervals` does reject.
- **B2. The decided Q8 (a), as the plan realizes it, does not give the index writer its seal
  bound after a compacted restore.**
  - Today the bound `logCh log < receiptBound` that every seal certifies (`idxSealed`), and from
    which the apply side's smallness (`2^48`) follows, comes only from the writer's receipt per
    change (`idxWriter_lt`).
  - "The writer's handle counts receipts from its last restore", plus `restoreBoundM`'s
    `logCh L' < receiptBound`, gives `< 2·receiptBound` for the next seal, not
    `< receiptBound`.
  - The premise also has no non-circular source on the apply side. Each member's own smallness
    comes from its own writer's receipts, and the image's log `L'` is the leader's.
  - This does not make any drafted statement false: it is a premise. It means items 36, 15, 16
    and 21 wait on more than "Q8".

**Round 4's findings.**
- **A2 is resolved.** `resumeHookM`, `lockNilSpec` and `bt_lockInNil` match Go's order
  (`server.go:1089-1093`, `batch_tx.go:111-122`) and the walk (`SnapApplyWalk.lean`: `hRst`,
  then `hSTP` with `HnH`).
- **A1 (a) is resolved:** the records vocabulary, with the two reads proved.
- **A1 (b) is resolved as evidence, and open as proof.** The counterexamples are right and well
  chosen. The repair (`kiNorm`/`IdxCRepN`, `entsCutAt`) is sound in design. Two caveats:
  - `KeyOnceAt` (B1);
  - the remaining work for item 32 is larger than the plan says (S2).
- **A1 (c)/(d)/(e):** drafted as described.
- **Round 4's leftovers:**
  - S1 (Q7): drafted (Scope).
  - S2.1: stated as a switch requirement.
  - S2.2 (`PhysNames.sx`): drafted, with `stopPayAt_done` proved.
  - S3: the Chain module.
  - S4: done.
  - S6: the list is complete. 37 items; I found no missing statement beyond B1/B2's consequences.

**Churn: none.**
- Step 1's Drafts are byte-identical since round 4's `f3282099c3`.
- The switched internals are unchanged.
- Step 2's changes since round 4 add to the Drafts; they reverse nothing. Two exceptions, both
  repairs and both renames:
  - `bucketThinnedAt` is replaced by `entsCutAt`, with a counterexample to the former;
  - `resumeCsM` is replaced by `resumeHookM`.

## The brief's decisions: realized soundly?

- **Restore in compaction mode; watchers excluded.** Unchanged since round 4 and sound
  (`storeStopR`/`compactRightR`/`fieldShare_reclaim`).
  - A2's nil-hook arm also checks against the batch-lock invariant. With no hook,
    `LockInsideApply` hands `P` through.
  - The pre-commit hook's consistent-index write is a no-op after `SetBackend`, as the plan says.
- **Write-back supply in `store.Compact`'s pre.** Unchanged. Chain's `store.Compact.specR` keeps
  `kbWTSupplyM γ.kb` (Chain:92).
- **Compaction revision logical (`c ≤ c'`), scope "no compaction at 0".** Sound.
  - The premise sits where round 4 asked: `EtcdServer.Compact.specD` (Scope:98-110) and
    `plainLogCD`. It is not in mvcc.
  - `compactableOk_serverD` shows the compactor's statement is unchanged.
  - `recsPos_crev` (mvcc R:294) removes the corner.
  - The realization is stricter than the decision: S4.
- **Scheduler `Stop` returns the run token; barrier tracked.** Sound.
  - `stopPayAt` gives `γx` a home.
  - `stopPayAt_done` (mvcc R:1009) is the step `compactBarrier` needs.
- **Q8 (a).** The decision is a reasonable choice; its realization is B2.
- **Snapshot track drafts stay the collaborator's.** Respected: nothing of D22's is switched.
- **Compaction-off reads as today.** Exact for each new statement:
  - `spec_of_specM` ×2 and `Close.spec_of_specM`;
  - `store.restore.spec_of_specR` (mvcc R:1399, proved, at `r = empty`, whole bucket,
    `RevP0 = RevP`);
  - `metaReadSpecR_empty`, `…R_empty` for the whole vocabulary, `restoreImageM_off`,
    `keyImageM_off`;
  - `restoreBoundM` (vacuous off) and `resumeHookM_no`.

## First tier

### B1. `KeyOnceAt` (item 33): a scope restriction stated as an etcd guarantee, and needed only by the invariant's choice of level

**Principles:** "No unneeded premise" (a scope restriction must be marked and filed; a premise
that excludes a legitimate caller fails sufficiency); "Every premise has a source the client
sees".

**Evidence.**

1. **The docstring's claim is false.** `Index.lean:327-335` says "etcd's transactions never touch
   a key twice … so every revision of the committed log has it".
   - `issues/etcd-txn-check-intervals-sibling.md` (upstream etcd-io/etcd#16380, known, unfixed)
     shows that `checkIntervals` (`api/v3rpc/key.go:236-321`) accepts
     `Then(Txn(Then(Put(k))), Txn(Then(Delete(k))))`: a put and then a delete of `k` in one
     revision.
   - The repository already treats "a revision writes each key once" as a premise about other
     writers: `srvNoDupKeys`, `client/v3/InvWatch.lean:367-380`, on the watch track.
   - `v3rpc/Defs.lean:37-43` says the checks give `NoDupKeysPerRev` only under `noFromKeyDel` and
     `siblingSafe`.
2. **Such a log breaks `IdxCRepN` after a mid-job image, while Go is correct.** I worked this
   example by hand against `key_index.go:91-126, 215-291` and the Index definitions; it is not
   checked in Lean.
   - The log is `[[], [], [put a], [put a, del a]]` (put at `2`; put `⟨3,0⟩`, delete `⟨3,1⟩`).
     Compaction is at `c = 3`.
   - The log's key index is `{created 2, ver 3, [2, ⟨3,0⟩, ⟨3,1⟩]}`, then an empty generation.
     Since `doCompact` keeps the tombstone at `atRev` (`key_index.go:276-282`), the entries
     deletable at `3` are `2` and `⟨3,0⟩`.
   - The job deletes in bucket order from revision `0` (`kvstore_compaction.go`). A batch boundary
     right after `2` leaves `[⟨3,0⟩ put, ⟨3,1⟩ tomb]`. `entsCutAt L 3` holds, and
     `KeyOnceAt L 3` fails.
   - The rebuild runs `restore(created 2, ⟨3,0⟩, ver 2)`, then `tombstone(3,1)`. It gives
     `{created 2, ver 3, [⟨3,0⟩, ⟨3,1⟩]}`, then an empty generation.
   - The log's index compacted at each allowed level:
     - levels `-1 … 2` keep revision `2`;
     - level `3` cuts to `[⟨3,1⟩]`.

     No level gives two revisions starting at `⟨3,0⟩`, and `kiNorm` does not apply: the
     generation has two revisions. So `IdxCRepN 3` fails.
   - Go is right:
     - `kiGet` at any readable revision (`≥ 3`) finds the tombstone and answers nothing, as the
       log does;
     - the resumed job at `3` then deletes `⟨3,0⟩`.
3. **`cx3_not_compacted` (Index:316) does not show that a reachable workload needs the premise.**
   Its log puts `a` twice in revision `3`. `checkIntervals` rejects that: a nested put is checked
   against `puts`, and a level's puts against `puts` and `dels`.
4. **The premise is the invariant's artifact.**
   - In both counterexamples the rebuilt index is "the log's compacted at the first surviving
     entry's *revision* `⟨3,0⟩`", and readers cannot tell it from the level-`3` one.
   - A level that is a revision (`Rev`, sub-revision included) rather than a main revision would
     make `IdxCRepN` hold without `KeyOnceAt`. Compaction at a main `c' ≥ level.main` of that
     index equals compaction of the log's index at `c'`, since `doCompact` reads only revisions.
     I have not checked this in Lean (uncertain).

**Callers affected.** D22's `specSnap` (`hkI : keyImageM`, item 21) would have to supply
`KeyOnceAt` for every revision `≤ r.crev` of the leader's log. On the apply side that is a new
request premise, `irrNoDelPut`'s analogue in `rqShapeC`, which excludes gRPC-admitted
transactions.

**Concrete restatement** (a question for the user, per the third-round rule):
- **(i) recommended:** make `IdxCRepN`'s per-key level a revision.
  - `∃ ℓ : Option Rev, … (idxGet idx k).map kiNorm = (kiCompactRevO ℓ (kiOfKey evs k)).map kiNorm`,
    with `kiCompactRevO` the cut that keeps the revisions `≥ ℓ` within the generation `doCompact`
    would pick.
  - Drop `KeyOnceAt` from `idxRestore_cutStmt`, `keyImageM`, `restoreImageM` and `specR`.
  - Item 33 disappears, and with it an apply-side obligation.
- **(ii) if (i) is refused:** keep `KeyOnceAt`, mark it as M2's scope restriction, and cite
  `issues/etcd-txn-check-intervals-sibling.md` and the `srvNoDupKeys` precedent.
  - Say in the docstring that Go is correct there and the premise is the proof's.
  - Name its apply-side source: the same "other writers" premise as `srvNoDupKeys`, stated over
    the committed log.

Item 33 is **not approvable as drafted**.

(The existing `NoDelPutAt` docstring, `Compact.lean:1637-1639`, on `lean`, has the same flaw: "The
server's transaction checks (`checkIntervals`) ensure it". A from-key delete then put passes:
`issues/etcd-txn-delete-then-ignore-put.md`. There the premise is a recorded decision, `irrNoDelPut`,
so only the sentence is wrong.)

### B2. Q8 (a)'s realization: the seal bound after a compacted restore, and the bound's source

**Principles:** Complete ("each caller can establish the precondition"); "Every premise has a
source the client sees".

**Evidence.**
- **The writer's seal bound comes only from its receipts.**
  - `idxWriter` (`mvcc/InvIndex.lean:921-924`) holds `⧗ (logCh ilog + pend.length)`.
    `idxWriter_lt` (`:968-975`) derives `logCh ilog + pend.length < receiptBound` from it by
    `receipt_lt`.
  - `idxSealed` (`:1024-1027`) carries that bound, and `idxSealed_small` exports it (`:1030`).
  - `txn.soleWriter_small'` (`etcdserver/txn/SoleWriter.lean:100-109`) turns it into the apply
    side's `logCh log < 2^48`.
  - `srvApplyKV_small'` (`etcdserver/InvApplier.lean:752-770`) feeds that bound to every request's
    size premise (`rqSmall_of_small`).
- **After a compacted restore, "counting receipts from the last restore" breaks this.**
  - The handle would hold `⧗ (changes since the restore)` and, from `restoreBoundM`,
    `⌜logCh L' < receiptBound⌝`.
  - The next seal then has `logCh < 2·receiptBound`, not `< receiptBound`. So `idxWriter_lt`'s
    statement, `idxSealed`'s conjunct and their consumers cannot be kept as they are.
  - Doubling the bound per restore does not stabilize. The next follower's `restoreBoundM` would
    be fed from a seal at `< 2·B`, so the bound grows with each restore of a restored image.
- **The premise has no stated source.**
  - The plan (Q8 (a)) says "an invariant of the KV model". But the only smallness the apply side
    has today is each member's own writer's (above), and `L'` is the leader's log.
  - The applied-index bound (`srvWTPool`, `InvApplier.lean:795-830`) counts entries, not changes.
- I did not check whether Perennial's persistent receipts (`⧖`, `preceipt_lt` at
  `InvIndex.lean:1098`) could carry a global count across members (uncertain). If they can, that
  is the vehicle "an invariant of the KV model" needs. If not, only a configuration bound gives
  it, which is Q8 (b), the option the user declined.

**Callers affected.**
- D22's `specSnap` (item 21) must supply `restoreBoundM`.
- Every proof that uses `idxSealed_small`/`soleWriter_small'` after a restore: the apply thread's
  request premises and the watch track's `srvLogsSmall`.

**Concrete restatement.**
- Item 36's text (`restoreBoundM d' L := d'.cm = true → logCh L < receiptBound`) can stay as
  mvcc's premise: mvcc needs it.
- But item 36 should be relabeled "[waits] on the bound's source and the seal law". The plan
  should state:
  - how a sealed log's `logCh < receiptBound` is kept after a compacted restore: a restated
    `idxWriter`/`idxWriter_lt`, and whether `idxSealed`'s bound or the `2^48` premises (`hrb`)
    change;
  - what on the apply side gives `logCh L' < receiptBound` for the leader's log.
- If no non-circular source exists, Q8 goes back to the user with this evidence. The decision is
  not unsound, but (a) is not achievable as "internal to mvcc".

## Second tier

### S1. The records reads: two proved specs per function at the switch (item 28)

- `UnsafeReadFinishedCompact.wp_proofR` (mvcc R:1097) re-proves the function for `r ≠ empty`. It
  uses today's spec only for `r = empty`.
- Today's spec stays, because `checkPrevCompactionCompleted` uses it at `nc = false`
  (`metaReadTx`, `InvStore.lean:708`; `store__checkPrevCompactionCompleted.lean:31-32`).
- So the switch leaves two WP proofs of one function ("One spec per function"; internal, so second
  tier).
- **Restatement:** one reader predicate with an optional record set. `metaReadSpecR rt
  (rs : Option CmpRecs)`: `none` is today's `nc = false` ("a value the store wrote"), `some r` is
  exact. Then one spec, whose post is `∀ r, rs = some r → …`, and today's two shapes are
  instances.

### S2. Item 32's remaining work is understated

- The plan ((d), item 32) says every use of `HL` goes through `IdxCRep.kiAt`/`rangeAt`, to be
  re-proved over `kiGet_kiNorm`.
- But the writers and the compaction use `IdxCRep` through more lemmas:
  - `IdxCRep.step` (`Compact.lean:1496`, every write);
  - `IdxCRep.compactAt` (`CompactIdx.lean:451`);
  - `avail_some/none`, `keep_some/none`, `avail_inj`, `gensOk` (`CompactIdx.lean:389-437`);
  - `get_some`'s positional `rfl` uses.
- Each needs a `kiNorm`-invariance fact: `kiAvail`, `kiKeep` and `kiCompact` commute with `kiNorm`,
  and `idxApply` preserves equality up to `kiNorm`.
- All are pure and very likely true, since they read only revisions, and the last generation is
  never normalized. But they, and not only `idxRestore_cutStmt`, are what item 32 waits on.
- If B1 (i) is taken, `IdxCRepN`'s definition changes first.

### S3. Redundant conjunct and premise placement in the image (items 21, 36)

- `keyImageM`/`restoreImageM` carry both `NoDelPutAt L r.crev` and `∀ x ≤ r.crev, KeyOnceAt L x`.
  The latter implies the former (`Compact.lean:1640`), and for `r.crev = -1` it holds by
  `NoDelPutAt_neg`. Drop one: under B1 (i), drop `KeyOnceAt`.
- `Restore.specM` asks `restoreBoundM` whenever the mode is on, even for an image with nothing
  deleted. `specR` asks only "whole bucket or the bound" (mvcc R:1361-1363).
  - Moving the disjunction into `restoreImageM`'s on branch (`ents = logEnts … ∨ logCh … <
    receiptBound`) would make the premise exactly what the code needs ("No unneeded premise").
  - Second tier, because B2 may change the premise anyway.

### S4. `1 ≤ r` is stricter than the decided scope (item 35)

- `EtcdServer.Compact.specD`'s `1 ≤ r` (Scope:101) also excludes negative revisions.
- Go handles those harmlessly: `updateCompactRev` returns `ErrCompacted` for `rev ≤ compactMainRev`
  (`≥ -1`), so no record is written.
- The decision was "no compaction at revision `0`". The only caller, the compactor, gives `> 0`,
  so nothing breaks.
- Either say this margin in the docstring ("Know the margin"), or state `r ≠ 0`, at the cost of
  the apply side showing that a negative compaction writes no record.
- **Approvable with the docstring.**

### S5. Small text items

- mvcc R:51 still names `resumeCsM` in the module header.
- Chain's `mvcc_NewStore_backend_cmpR` (item 24, Chain:167) takes `backend.fkV d.γB true`. With
  item 29's merge at the switch this is `fkVM`; say so in the item.
- Item 19's approved text is the design "`pay` a field of `SchedNames`". The Lean `Stop.specD` is,
  by its own docstring, unprovable until then. The approval should name the field, not the Lean
  text.
- `issues/etcd-restore-scheduled-compact-zero.md`: update "How the proof handles it" (Q7 (a)).

## Per target

**Index** (`kiNorm`, `IdxCRepN`, the three counterexamples, `kiGet_kiNorm`, `entsCutAt`,
`KeyOnceAt`, `idxRestore_cutStmt`, `idxRestore_full_N`)
- Good:
  - `idxCRep_restore_counterexample` is exactly the right evidence. It covers every level up to
    `cmax ≤ 4`, and `cx_idxCRepN` shows the repair holds there.
  - `kiGet_kiNorm` matches Go's `findGeneration`: a non-last generation's tombstone `≤ rev`
    returns nil, and `revs[0] > rev` skips. The proof goes through `kiFindGenAux_spec`, so readers
    cannot see `kiNorm`.
  - `bucketThinnedAt_counterexample` rightly kills round 3's shape.
  - `entsCutAt` matches the job: per key, deletable is a prefix of the key's entries; the job
    deletes in revision order; the union of a finished compaction's prefix and the job's cut is a
    prefix.
- Findings: B1, S2, S3.

**mvcc R** (records vocabulary, `keyCleanRead_of_backendC_stmt`, `keyImageM`/`restoreImageM`,
`restoreBoundM`, A2, `Restore.specM`, `specR`, `stopPayAt`, `StoreNamesD`, the two reads)
- Good:
  - `CmpRecs`, `metaReadSpecR` and `kbRecs` agree with `kvstore.go:330-391`.
  - `revFinW` mirrors the `found` branch's lock round, and `restoreDone`'s `compactMainRev` is
    `r.fin.getD (-1)`.
  - `restoreDone`'s `currentRev = |L'| - 1` holds over a cut image. The last revision's entries are
    never deletable at `c ≤ |L'| - 1`, and `recsOk` keeps both records `< |L'|`, so Go's two
    raises (`kvstore.go:363-378`) do not exceed it.
  - `resumeK` captures "`restore()` calls `compactLockfree` and ignores its error".
  - `keyCleanRead_of_backendC_stmt` quantifies `r` soundly: the evidence is in `NC = kbRecs`.
  - The off laws are proved.
- Findings: B1, B2, S1, S3, S5.

**Chain** (`compactJobPreR`, `store.Compact.specR`, `updateCompactRev.specR`, `compactLockfree.specR`,
`lockCtxM`/`lockBackM`, `mvcc_NewStore_backend_cmpR`)
- Good:
  - One spec per function, with the hook state as a case split on the input (`hk : Option val`),
    not a family.
  - `store.Compact.specR` has no revision premise beyond today's, as round 4 asked.
  - `mvcc_NewStore_backend_cmpR` is proved.
- Findings: S5 (`fkV`).

**Scope** (`compactPropOkD`, `plainLogCD`, `plainLogCD_compaction_pos`, `EtcdServer.Compact.specD`,
`compactableOk_serverD`)
- Good: placed where round 4 asked, and the compactor's statement is unchanged.
- Findings: S4.

**schedule Draft:** only the docstring changed (S2.1 stated). Findings: S5 (item 19's wording).

**etcdserver R:** the rename only (`storeCloserM`).

**Step 1 Drafts and the switched internals:** unchanged since round 4. No churn.

## Approval list: verdicts

**Approvable now, as drafted:**
- 1-3 and 5-14 (step 1; no churn);
- 4 and 17 (Chain's texts);
- 19 (as the design with the `pay` field: S5);
- 20, 22, 23, 24 (note `fkVM`), 25, 26, 27;
- 28 (but unify the two specs at the switch: S1);
- 29 (the vocabulary);
- 31, 34;
- 35 (with S4's margin in the docstring).

**Not approvable as drafted:** 33 (B1). It needs the user's choice between (i) and (ii).

**Waiting items: is the stated gap the only one, and will the design close it?**
- **15, 16** (`Restore.specM`, both stores). The plan names 32, Q8 and 37. They also wait on:
  - 30 (the walk builds the clean read from it);
  - B2, which is now the receipt question, not Q8;
  - B1, if `KeyOnceAt` changes.

  The design closes the index (32) and the view (37) as far as I can see. B2 is open.
- **18** (`specR`). It waits on 32, including S2's lemmas; B1 changes its premises. Otherwise
  closed by the design: the reads are proved, and the off law is proved.
- **21** (D22's). It waits with 15, and also on the apply-side sources of `KeyOnceAt` (or its
  removal, B1) and of `restoreBoundM` (B2).
- **30** (`keyCleanRead_of_backendC`). Yes, its only gap is item 29's `fkOk` clause, and the design
  is plausible. Uncertain until the backend re-proof says whether a bbolt fact is needed (then the
  `axiom` skill).
- **32.** It waits on `idxRestore_cutStmt` *and* S2's invariance lemmas. These are pure and likely
  to close.
- **36.** Q8 is decided, but the gap is not closed: B2.
- **37** (`kbView_widen`). Not drafted. The design (widen the view at the open over keys the
  registration marks deletable) is plausible.

## Ranked by need of revision

1. **Index/mvcc R's `KeyOnceAt` (B1, item 33).** This is the user's question: a revision-level
   `IdxCRepN` (recommended), or a marked scope premise.
2. **Q8's realization (B2, items 36, 15, 16, 21).** State the seal law after a compacted restore
   and the bound's source, or return Q8 to the user.
3. **Item 32's remaining lemmas (S2).**
4. **The records reads as one spec (S1, item 28).**
5. **Image premises (S3), `1 ≤ r` margin (S4), text items (S5).**
6. **Step 1 Drafts, schedule, etcdserver R, Chain:** no change needed.
