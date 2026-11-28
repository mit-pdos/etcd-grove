# `bootstrap`'s restart contract: the files admitted a WAL whose eager fold is not what a restart reads (2026-11-28)

A bug in this repository's own statement (CLAUDE.md, "Issues in the verified code": bugs in our specs go
in `notes/`), not in etcd. Found by the review of TRUST-1's row 3 (`/shared/tmp/trust-review/row3.md`), extended
by DELTA-8 (branch `etcd-safe-crash-delta-now/2026-11-27`, its note `bootstrap-crash-eagerfold.md` at
`9a260473c1`) and reviewed again for lean (`/shared/tmp/efr/report.md`, lean `ee0d41ff1c`). Fixed on branch
`walfiles-fold/2026-11-28`.

## The false statement

`bootstrapRestartContract` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRestart.lean`), a trusted premise
of `etcd_robust_single_process` (`examples/etcd/all`, through `etcd_restartN.premises` and
`etcd_restart1.premises`, `etcdstart.bootPremiseR`):

- **Pre**: the member's files `srvFiles`, whose WAL part `walFiles` (`storage/WalRecs.lean`) fixed the records
  `σ` only as **what a restart reads**: `walRead (walSrvHist d.H) = some σ` (`storage/WalHist.lean`: `walKeep`
  drops the snapshot records above the last saved commit, then folds).
- **Post**: `bootOkR` → `wal.restartOk` → `walOpened` → `walRecs h σ` (`etcdserver/WalApi.lean`,
  `storage/WalRecs.lean`), which holds the **eager fold** of the same history:
  `walFoldChkFrom walFresh (walSrvHist d.H) = some σ`, every snapshot record applied (`walSaveSnap`).

When the two folds differ, the pre holds, `bootstrap` returns `nil`, and no post state exists: the premise
is false, so `etcd_robust_single_process` was vacuous as a whole. `walReadFacts σ` (the premise the
unlanded `etcd-safe-rule41rm` adds to the same contract as an axiom) holds of the counterexample's `σ`, so
that axiom would have been unsound.

## The counterexample

A WAL that ends with a **synced snapshot record above the last saved commit**:

1. `Save(hs{commit 5}, entries 1..5)`, `SaveSnapshot(3)`, `SaveSnapshot(10)`, `Close`. `SaveSnapshot` ends in
   `w.sync()`; `Close` syncs and adds no record, so the files are a closed WAL's with the synced mark at the
   whole history: `walFiles` (before the fix) held of them.
2. `walRead` drops the record at 10 (`10 > 5`): `σ` has base 3, entries `[4 5]`, commit 5.
3. The eager fold applies the record at 10: base 10, no entries. No `σ` is both.
4. Go reads it back without error: `ValidSnapshotEntries` keeps the records at or below the commit (newest
   3, `wal.go:974`), `Open(3)` + `ReadAll` returns `err = nil`, commit 5, entries `[4 5]`; and a real member
   whose WAL ends so restarts and is ready (the two tests below).

## (d) etcd never writes it in a graceful run

- **A received snapshot.** Raft's `restore` sets `committed = s.Index` and accepts only `s.Index > committed`
  (raft `log.go:468`, `raft.go:1877`), so the `Ready` that carries the snapshot carries a `HardState` with
  commit ≥ its index. etcd's raft loop calls `SaveSnap(raftSnap)` (`server/etcdserver/raft.go:269`) and then
  `Save(rd.HardState, rd.Entries)` (`:276`), with no stop point between them (the stop points are at `:222`,
  `:253`, `:335`, `:352`, `:366`); a failure of either is `lg.Fatal`, an exit, not a graceful stop; the WAL is
  closed only after the loop returns (`onStop`). So a graceful stop always follows that `Save`.
- **The apply loop's own snapshot** is taken at the applied index, which waits on `notifyc`, signalled only
  after the `Save` (`raft.go:296`, `:319`): it is ≤ the saved commit.
- **This repository's model agrees**: the storage's `Close` law takes `walRecs h σ` and `σ.b ≤ σ.commit`
  (`WalApi.lean`) and makes `walFiles` through `walRecs_closeAU`, which already had the eager fold (`hf.1`) and
  derives `walRead` from it (`walRead_of_fold`, `storage/WalLinkPure.lean`).
- Only a **crash** between `SaveSnap` (synced) and `Save`, or a file not written by etcd, leaves the shape. The
  crash restart is the crash contract's concern (`bootstrapCrashContract`, not on lean; DELTA-8's note): its
  post must change there, a premise cannot fix it.

## The fix

`walFiles`' pure fact gains one conjunct (`storage/WalRecs.lean`):

    ⌜walRead (walSrvHist d.H) = some σ ∧ walFoldChkFrom walFresh (walSrvHist d.H) = some σ ∧ …⌝

- Only that conjunct; not DELTA-8's variant (`walFoldChkFrom … ∧ σ.b ≤ σ.commit` in place of `walRead`).
- Producer: `walRecs_closeAU` gives it (`hf.1`). Consumers: none unfolds `walFiles` (it is `@[no_expose]`; the
  only unfolds are in `WalRecs.lean`), so no other proof changed.
- Effect: `srvFiles`, hence the contract's pre, excludes the counterexample; the docstrings of `walFiles` and
  `srvFiles` say why. No axiom or `sorry` moves.
- **Approved**: coordinator-E, #50, 2026-11-28 01:31Z, under Upamanyu's delegation. Ledger:
  `notes/specs-only/ledger.md`, 2026-11-28.

## Evidence

Go, at the etcd pin `d26dd5da6f` (`examples/go.mod`), go1.27.1; `cd examples && go test ./axiomcx/<dir>/ -v`.

- `examples/axiomcx/restarteagerfold` (from `9a260473c1`): the WAL calls of the counterexample.

      restarteagerfold_test.go:87: valid snapshots 2, newest 3; ReadAll err=nil commit 5 entries [4 5]; the eager fold's base would be 10
      --- PASS: TestTrailingSnapAboveCommit (0.04s)

- `examples/axiomcx/restarteagerfoldboot` (the review's `efrboot_test.go`): a single-member etcd
  (`embed.StartEtcd`, `t.TempDir()`) stopped gracefully, a synced snapshot record at the saved commit + 10
  appended to its WAL and the WAL closed, then restarted by etcd itself: `bootstrap` succeeds and the member
  is ready.

      restarteagerfoldboot_test.go:65: after graceful stop: commit 4 last 4 term 2
      restarteagerfoldboot_test.go:71: restart ok: applied 6 committed 6
      --- PASS: TestRestartTrailingSnap (1.68s)

  (Its embedded server logs `http: Server closed` / `use of closed network connection` on each `Close`:
  the listeners' shutdown, not a failure. It listens on the default ports 2379/2380. `embed` needed its
  indirect requirements added to `examples/go.mod`/`go.sum`.)
