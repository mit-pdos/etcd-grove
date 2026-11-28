# `bootstrap`'s restart contract: the eager fold in the post is false of Go (2026-11-28)

A bug in this repository's own spec (CLAUDE.md, "Issues in the verified code": bugs in our specs go in
`notes/`). Found by the independent review of TRUST-1's row 3 (`/shared/tmp/trust-review/row3.md`,
2026-11-28, for the etcd_safe lead, #50) of branch `etcd-safe-crash-delta-now/2026-11-27`; extended here
(DELTA-8) to lean's text. Not yet reviewed by the `axiom` skill: the statements below are argued, the WAL
read is measured, no Lean counterexample was run.

## The statements

- `bootstrapRestartContract` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRestart.lean`): a premise of
  `etcd_robust_single_process` (restartN's and restart1's, through `etcdstart.bootPremiseR`). Its pre holds
  the member's files: lean has `srvFiles`, the delta `srvFilesC`. Their WAL part (`walFiles`, `walFilesC`,
  `storage/WalRecs.lean`, `WalRecsCrash.lean`) fixes the records `σ` as **what a restart reads**:
  `walRead (walSrvHist d.H) = some σ` (`storage/WalHist.lean`: `walKeep` drops the snapshot records above the
  last saved commit, then folds). Its post (`bootOkR`'s `wal.restartOk`, `etcdserver/WalApi.lean`) holds
  `walOpened` (lean) or `walOpenedH` (the delta). Through `walRecs` (lean) or `walHistH` plus the fold (the
  delta), that is the **eager fold** of the history on disk: `walFoldChkFrom walFresh Hs = some σ`, every
  snapshot record applied (`walSaveSnap`, `storage/WalRecsCore.lean`).
- `bootstrapCrashContract` (`etcdserver/InvCrashImage.lean`, delta only): the same post, over crash images.

## The counterexample

The two folds differ on a WAL that ends with a **synced snapshot record above the last saved commit**:

1. `Save(hs{commit 5}, entries 1..5)`, `SaveSnapshot(3)`, `SaveSnapshot(10)`. `SaveSnapshot` ends in
   `w.sync()` (`wal.go:1423`), so every record is durable.
2. `walRead` drops the record at 10 (`10 > 5`): `σ` has base 3, entries `[4 5]`, commit 5. `σ` meets
   `walReadFacts` (I1-I4).
3. The eager fold applies `walSaveSnap` at 10: base 10, no entries (`10 > commit`). No `σ` is both.
4. Go reads the WAL back without error: `ValidSnapshotEntries` keeps the records at or below the commit
   (newest 3, `wal.go:974`), and `Open(3)` + `ReadAll` returns `err = nil`, commit 5, entries `[4 5]`
   (measured, `examples/axiomcx/restarteagerfold`, at the etcd pin `30df685e4`). `bootstrap` therefore
   returns `nil` while the post cannot hold. (The test runs the WAL calls, not `bootstrap` end to end;
   without a `.snap` file for 3, `LoadNewestAvailable` returns `ErrNoSnapshot`, which `bootstrap` accepts,
   and it reads the WAL from its `{0, 0}` record, also without error.)

How the state arises:

- **etcd, with a crash or kill** (the reviewer's case): a follower receives `MsgSnap` at `S` above its
  saved commit; raftNode calls `SaveSnap` (synced) before `Save(hs{commit=S})` (`raft.go:266-291`); a crash
  in between leaves the WAL so. Every crash cut of `walFilesC_crash` keeps the record (the cut is at or past
  the synced mark). So the delta's widening to `srvFilesC` admits it.
- **Any writer of the WAL, with a graceful `Close`** (DELTA-8's addition): the test closes the WAL after
  the record at 10. `Close` syncs and adds no record, so the files carry the synced mark at the whole
  history: they are **lean's `srvFiles`** too (the synced mark is the only conjunct `srvFilesC` drops). The
  predicate says nothing of who wrote the WAL; etcd's own graceful stop never leaves this state (the stop
  check at `raft.go:250-253` precedes `SaveSnap`), but a premise is a claim over every state its pre admits.

So the flaw is **not** the delta's widening alone: lean's restart contract has the same post over a pre that
admits the same files. The review's "on lean, the contract was only claimed for graceful images" is true of
etcd's images, not of the predicate.

## Which top-level statements it makes vacuous

Checked on lean `30e7e48f43` (grep of the `TopLevelDefs`/`TopLevelRobustness` files and the modules they
import; `etc/tcb-collections/`):

- **`etcd_robust_single_process`** (`examples/etcd/all`): its premises `etcd_restartN.premises` and
  `etcd_restart1.premises` include `bootstrapRestartContract` (lean's text). If the argument above is right,
  that premise is false and the theorem is **vacuous as a whole** (the premise is a hypothesis of the whole
  statement, not of a crash path). On the delta the same, through `srvFilesC`.
- `bootstrapCrashContract`: **not on lean**. On the delta it is reached only by the crash path
  (`CrashInterim.lean`'s law `bootstrapCrashContract.law`, no axiom; `NewServerC_dist.wp_proof`, an axiom no
  result reaches: neither is in `etc/tcb-baseline.txt`). No top-level statement, on lean or the delta,
  reaches it: no statement is vacuous "on the crash path" through it.
- No other top-level statement on lean reaches an eager-fold post: `wal.restartOk` is reached only through
  `bootOkR` in `bootstrapRestartContract`; the first start's `wal.bootOk` is at `walFresh`, where the folds
  agree; the distributed theorems (`etcd_safe_nocrash`, `etcd_kv_safe_nocrash`, `putget_safe`) never restart.
- **`etcd-safe-rule41rm/2026-11-27`** (not landed) turns the contract into the axiom
  `bootstrap.wp_proofRestart` with the premise `walReadFacts σ`. The counterexample's `σ` meets
  `walReadFacts`, so that axiom would be **false**: an unsound axiom, not a vacuous premise. It must not land
  with this post.

## Fixes (none applied: rule #8; for the lead)

- **Pre (minimal text):** `walFiles`' (and `walFilesC`'s) `walRead (walSrvHist d.H) = some σ` becomes
  `walFoldChkFrom walFresh (walSrvHist d.H) = some σ ∧ σ.b ≤ σ.commit`, which gives `walRead … = some σ`
  (`walRead_of_fold`, `storage/WalLinkPure.lean`). The graceful `Close` already proves it
  (`walRecs_closeAU` has both facts), so the single-process proofs keep working; the contract then claims
  nothing of a WAL whose eager fold runs past its commit. The crash path's `walFilesC_crash` could not give
  it for the state above (correctly): the crash restart needs the second fix.
- **Post (the review's):** `walOpenedH`/`restartOk` over the reader (`walRead Hs = some σ`, or the
  `walKeep`-filtered fold) in place of the eager fold. This reworks the restart's durability allocation
  (`wal.restartOk_startK`, `rnDurK_alloc_law_holds`: `HistOkK`, `recsOf` assume the eager fold).

## Evidence

- Go: `examples/axiomcx/restarteagerfold/restarteagerfold_test.go` (`cd examples && go test
  ./axiomcx/restarteagerfold/ -v`); the reviewer's program `/shared/tmp/trust-review/row3-go/main.go` is the
  same, as a `main`.
- Known divergence: `InvWalCrash.lean` (the reader drops the record) and `notes/wal-p8-handoff.md`.
