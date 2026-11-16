# auth-schema-srv: handoff

## START HERE (2026-11-16, A0: the soundness repair; STOP before etc/land.sh)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`. Session row in `/shared/etcd-grove-sessions.md`.
  Decisions: `questions.md` (Q1 (a), Q2-Q9; the A0 items).
- Done: Scope (b4528c167d); **A0** (this checkpoint): the read contract per bucket (`BkView`, `authViewSnap(From)`,
  `authReaderOkV`, `authTxReadsV`; `authReadTxOk`, `authReadTxLocked(From)` restated), `passwordChecked` weakened,
  the write contract's session token `Sw`/`AuthSess` (`authBatchTxLk(R)`), every auth proof re-threaded; Go tests
  `nonissues/etcd-auth-readtx-delete-window-mixed-state/zz_authschema_perbucket_test.go`; ledger entry; review
  `/shared/tmp/auth-schema-srv/a0/review/report.md`.
- Next, after the coordinator's go and the land: A1's own Scope (the backend read model over tracked hook buckets,
  with the window: per bucket, put buckets after, delete buckets before; build it over the backend's `RdSt` window
  flag and `dls`, per the Q9 audit), then A2-A6, A7 (closed statements, to the user). Scope §3.
- Go tests: copy the test files into `server/storage/schema` of the clone `/shared/tmp/auth-schema-srv/etcd`
  (fork pin 6e8f0c004); `cd server; PATH=/usr/local/go/bin:$PATH TMPDIR=/shared/tmp systemd-run --scope -q -p
  MemoryMax=32G env GOWORK=off GOTOOLCHAIN=go1.27.3 go test ./storage/schema/ -run TestAuthSchemaRead -count=1 -v`.
- Pitfalls: `Model.lean` already has an `AuthView` (isOpPermitted's four views): the bucket view is `BkView`.
  `iexact` does not see through `(fun st => Hs (BkView.uni st)) st` vs `Hs (BkView.uni st)` or
  `(BkView.uni st).atUsers`: `dsimp only [BkView.uni]` first. Builds: `/shared/tmp/build-slot.sh lake
  --packages=/shared/tmp/manifest-e9e.json build ...`; `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json` for
  `etc/lean-check.py` (it printed nothing on a module whose import failed to build: build first).

## History

### Scope (2026-11-16, HARD STOP, refutation)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema` (lean 8448906500 merged, fast-forward;
  the Scope commit on top). Session row in `/shared/etcd-grove-sessions.md` ("auth-schema-srv agent of
  etcd-grove-02").
- Done (notes only, no Lean): the Scope `notes/auth-schema-srv-scope.md`; the refutation R1 recorded
  (`notes/auth-schema-srv-refuted.md`, "Second refutation"; nonissue
  `nonissues/etcd-auth-readtx-delete-window-mixed-state.md` with its Go test; STATUS section "Refuted
  hypothesis" and Last-updated entry).
- R1 in one line: `authReadTxOk`'s one-state `RLock` is false (Unlock writes puts back, releases
  `readTx`, then commits the delete), so `authSchemaSrv` is false and the three auth closed theorems are
  vacuous; `CheckPassword.spec` too.
- Waiting on: etcd-grove-02 / the user, Scope §4 Q1-Q9 (Q1 the fix: per-bucket read states recommended;
  Q2 the backend read model proved as its own sub-plan; Q3 Marshal axioms; Q4 `sizeCache` fix; Q8
  delete `authSchemaBoot`/`newAuthStore_boot`).
- Next, in order, once Q1 is decided: A0 (restate the read contract and `CheckPassword.spec`, axiom
  review; statement stop), then A1's own Scope (the backend read model over tracked hook buckets),
  A2-A6 over A1's statement, A7 (drop `hD22`: closed statements, to the user). Scope §3.
- Go test: copy `nonissues/etcd-auth-readtx-delete-window-mixed-state/zz_authschema_window_test.go` into
  `server/storage/schema` of an etcd clone at the fork pin 6e8f0c004 (a clone is at
  `/shared/tmp/auth-schema-srv/etcd`); run under `systemd-run --scope -q -p MemoryMax=32G` with
  `GOWORK=off GOTOOLCHAIN=go1.27.3 go test ./storage/schema/ -run TestAuthSchemaReadWindowMixedState -count=1 -v`.
  It fails on the first `UserDelete` (3/3 runs).
- Pitfalls: the worktree's `.lake/build` was moved in and is not current: `etc/tcb-report.py` refuses until
  a build (`/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build ...`); the auth
  collections show no schema auth axiom anyway (all behind the hypothesis). `notes/status-history.md` is
  append-only: merge lean before touching it.
