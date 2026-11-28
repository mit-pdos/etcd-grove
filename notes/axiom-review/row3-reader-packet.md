# Row 3, corrected: `bootstrap`'s restart contract over the reader (packet for Upamanyu, 2026-11-28)

Session R3-1 (coordinator etcd-grove-03), branch `row3-reader/2026-11-28` off the held crash-restart line
`etcd-safe-crashrestart-held/2026-11-28` @ `beaf83ccb8`. Rule #8: a statement/axiom change; not landed, not
queued. Sources: the review `/shared/tmp/trust-review/row3.md`, DELTA-8's
`notes/axiom-review/bootstrap-crash-eagerfold.md` (branch `etcd-safe-crash-delta-now/2026-11-27`), B2's
section of `bootstrap-restart-commitle.md` (branch `b2-walcl-p5/2026-11-28`). Lean (`5212560c0d`) is not
affected: its `walFiles` holds both the reader's and the eager fold's `σ` (DELTA-8's pre fix), so its
`bootstrap.wp_proofRestart` claims nothing of a WAL whose folds differ. The packet is for the crash line,
whose pre `srvFilesC`/`walFilesC` keeps only the reader (`walRead (walSrvHist d.H) = some σ`).

## The text: old and new

Old (crash line, `WalApi.lean`; `bootOkR`'s slot, the post of `bootstrapRestartContract`, so of the axiom
`bootstrap.wp_proofRestart`, and of `bootstrapCrashContract`):

    wal.restartOk cfg id cid w σ :=
      (∃ h Hs, ⌜h.w = w⌝ ∗ walOpenedH h cfg.DedicatedWALDir' id cid σ Hs true ∗ walPurgeRight h ∗
         WalFs.walSyncedLb h.dir h.γ.inc |Hs| ∗ ⌜walIdxLe (2^61-1) Hs ∧ walCommitLeFrom walFresh Hs⌝) ∗
      ⌜walReadFacts σ⌝
    walOpenedH h dir id cid σ Hs := walOpen h 1 ∗ walHistH h Hs ∗ ⌜walFoldChkFrom walFresh Hs = some σ⌝ ∗ …

New:

    srvFilesC dd id σ Hs D      -- the files' history named: walFilesC's d has walSrvHist d.H = Hs
    bootstrapRestartContract … := □ ∀ σ Hs i L D M, ⌜… walReadFacts σ⌝ -∗ … -∗
      {{ … srvFilesC cfg.DataDir' id σ Hs D }} bootstrap cfg {{ b err, err ≠ nil ∨ bootOkR … σ Hs … b }}
    wal.restartOk cfg id cid w σ Hs :=
      (∃ h, ⌜h.w = w⌝ ∗ walOpen h 1 ∗ walHistH h Hs true ∗ ⌜walRead Hs = some σ⌝ ∗ walMetaIs h id cid ∗
         ⌜h.dir = cfg.DedicatedWALDir'⌝ ∗ walPurgeRight h ∗ WalFs.walSyncedLb h.dir h.γ.inc |Hs|) ∗
      ⌜walReadFacts σ⌝

Directions: (1) post, `walFoldChkFrom walFresh Hs = some σ` → `walRead Hs = some σ` (replaced: the reader
is what Go computes); (2) post, `walIdxLe (2^61-1) Hs` and `walCommitLeFrom walFresh Hs` **dropped**
(weaker; neither is checked by `bootstrap`, so neither belongs in its post); (3) post's history is the
pre's `Hs`, not an existential (stronger, but it is what the proved `WAL.ReadAll.spec` says: "the history
is not changed"; `walHistH` already fixes `Hs = walSrvHist d.H`). Because the history passes through,
every fact the caller proved of `Hs` before the restart (index bound, commit-le, the reads at later
commits) holds after it with no trusted claim. The pre admits the same files as before.

## The Go counterexample to the old text

A follower receives `MsgSnap` at `S` above its saved commit; `raftNode` runs `SaveSnap` (synced,
`wal.go:1423`) before `Save(hs{commit S})` (`raft.go:266-291`); a kill in between. The files' reader drops
the record (`ValidSnapshotEntries` keeps records ≤ commit, `wal.go:974`; `walKeep`), the eager fold applies
it. No `σ` meets both the pre and the old post, and `bootstrap` returns `nil`.

## Evidence that the new text is true of Go

`examples/axiomcx/row3reader/row3reader_test.go` (`cd examples && go test ./axiomcx/row3reader/ -v`, at
the examples' etcd pin; passes). The writer is a child process that dies by `os.Exit`, no `Close`.

- `TestSnapBeforeSaveCrash`: `Save(commit 5, 1..5)`, `SaveSnapshot(3)`, `SaveSnapshot(10)`, killed.
  bootstrap's read (`ValidSnapshotEntries` + `Open` + `ReadAll`): base 3, commit 5, entries `[4 5]` =
  `walRead Hs` (by the definition: filter at commit 5, fold). Eager fold: base 10, no entries.
- `TestDanglingSnapRevived`: the restarted member (opened as `bootstrap` does) appends `Save(commit 12,
  6..12)` and is killed again. The read now **keeps** the record at 10: base 10, commit 12, entries
  `[11 12]`; `walRead` of the extended history gives the same (`walSaveSnap` at 10 > commit 5 empties the
  entries; `readEnt` skips 6..10). So a dangling record is not gone: a later commit revives it. This is
  true of Go and harmless (10 was a committed snapshot), but the restart proof must model it (below).

## The index bound

Claim (`walIdxLe (2^61-1) Hs`, `WalHistLemmas.lean:779`): every entry and snapshot record of the history,
overwritten and dropped ones included, has index ≤ `2^61-1`. Why it holds: every record of the history
was appended by a `Save` whose batch fits raft's room (`rnFits`/`rnFits_idx`, `InvRaftNode.lean:326`: from
the node API's `readyFits`, the receipts bound `ReceiptBoundLe (2^60)` past the boot log, `receipt_lt`) or a
`SaveSnap` whose index is ≤ raft's last (`raftState_lastFits`, `DurableLastFits.lean`, same receipts). The
lifetime argument is the receipts': fewer than `2^60` receipts cluster-wide bound every index ever assigned.

**It is already proved**, not trusted, everywhere but the restart's post: the crash invariant carries it
(`HistReadOk`'s first conjunct, kept by `walIdxLe_snoc_save`/`_snap` at each `Save`/`SaveSnap` law, whose
premises `rnDurK_save.law` gets from `rnFits_idx`). The old post asserted it of the files afresh; the new
text drops it, and the restart's allocation takes it from the image (`walIdxLe_take` of `HistReadOk`), as a
fact of the same `Hs`. Nothing about it stays in the trust base. Same for `walCommitLeFrom walFresh Hs`
(B2's `histReadsK_commitLe` proves it of the invariant's history; `walCommitLeFrom_take` of a crash prefix).

## What downstream needs

What raft's restart needs is unchanged: `σ` with I1-I4 (`walReadFacts`, a premise as today),
`StorageHolds S σ`, `ViewOk ⟨S, σ.hs, none, l₀⟩ σ` (`viewOk_restart`, from `walReadFacts` only). The
restart's **durability invariant** is what changes: `rnRestartWal` asks `HistReads σ Hs` (`InvWalCrash.lean`:
at every commit `c` ≥ the last saved, `walReadAt Hs c = some σ`), which is **false** with a dangling record
(at `c ≥ 10` the read is base 10). Today it is derived from the eager fold (`histReads_of_fold`); under any
true post it cannot be. Changes, estimated:

1. Trusted text (above): `WalApi.lean` (`wal.restartOk`, a reader form `walOpenedR` beside `walOpenedH`,
   which the first start keeps: at `walFresh` the folds agree), `InvRestart.lean` (`srvFilesC` +`Hs`,
   `bootOkR` +`Hs`, the contract), `InvCrashImage.lean` (`bootstrapCrashContract`), `WalRecsCrash.lean`
   (`walFilesC` +`Hs`). ~60 lines.
2. Plumbing: `restartOk_startK`/`_startRK` give `walRead` and take the index bound and reads from the
   image; `wal.stopImage`/the crash image gain the history's facts (`walIdxLe Hs`, the reads above the
   commit); `walFilesC_crash`, `srvFiles_srvFilesC`; `wal.restartOk_start` (lean's non-crash allocation via
   `walRecs`) is deleted or takes the eager fold from its caller. ~150 lines, one session.
3. The invariant: generalize the one pending received snapshot (`recsAt`, `HistReadsK`, `CertBaseK`) to the
   history's **dangling snapshot records** (above its last saved commit): the reads at `c` revive those
   ≤ `c`. Needs (a) their certificates (`walOpCert`: `snapshotValid`, the `.snap.db` durable `sd`) carried
   across the restart in the image (P5-RESTART option (B) dropped exactly these, `walHistCerts`); (b)
   `ImgOk` of a read whose base is a revived snapshot, from its certificate (committed, so the restarted
   log agrees at its index); (c) the graceful stop's take (`rnDurK_take.law`) in the reader form, since a
   restarted generation may stop with a dangling record. ~400-700 lines, 2-4 sessions; the riskiest is
   (b). Open (to check, not assumed): `ReleaseSnapDBs` never removes a dangling record's `.snap.db` while a
   later commit could revive it (`sd` is persistent in the invariant).

## Consistency with B2

B2 (option (c)) keeps `walCommitLeFrom walFresh Hs` in `wal.restartOk` for `wal.restartOk_start`'s
conversion `walHistH → walRecs`. The new text drops it and that conversion (no `walRecs` at a restart: the
eager fold is not `σ`); B2's `walHistH`, `walSaveH`/`walSaveSnapH` laws and WalRecsH lemmas are untouched;
`histReadsK_commitLe` becomes the image's source for the commit-le, if (3) still needs it.

## Status

No Lean changed. Merging lean into this branch conflicts in 8 files (auth's nomode D3 follow-up, and
`WalApi.lean`/`RnNewStorage.lean`, which B2-1's port resolves): the Lean start waits for B2-1's merge.
