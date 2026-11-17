# auth-schema-srv: handoff

## START HERE (2026-11-17, A1.1 done; STOP at checkpoint A1.1)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`. A1 Scope `notes/auth-schema-srv-a1-scope.md`,
  decided by etcd-grove-03 (`questions.md`, "A1 Scope decided"): claim per bucket, kinds, the accessor, `hookStep`
  strengthened (ledger entry old → new when edited; stop if a post weakens or a premise grows), `OpenBackend` via
  `isBackend` with a filled-value soundness argument written at A1.5 and reviewed before proving past it.
- Done: Scope (e256330834); A1.1, the pure model `Proof/.../storage/backend/TrkModel.lean` (`RbK`, `TkMap`, `rvBkt`,
  `kOk`, `trkOk`, `hookStepT`; preservation by put/del/create/delBucket/write-back/hook/commit; the readers' contents
  at the write-back by kind and at the commit; built, imported by nothing). Forms: `questions.md` "A1.1".
- Next: wait for etcd-grove-03's word that the origin/lean merge (pin c6b39d4f8) landed; merge lean; then A1.2 (the
  kinds' home, `γ.rbr` and the claim marker in `BNames`, `rtCore`/`rbSide` halves, `trkOk` into `sessWf`/`freeOk`,
  `hookStepT` into `hooksSpec` + ledger, `New`/`NewAlloc`), A1.3-A1.5, checkpoint A1.5 (with the soundness
  argument).
- Go test: `notes/auth-schema-srv-a1/zz_a1_trackedwindow_test.go` into `server/storage/backend` of
  `/shared/tmp/auth-schema-srv/etcd`; `cd server; PATH=/usr/local/go/bin:$PATH TMPDIR=/shared/tmp systemd-run --scope -q
  -p MemoryMax=32G env GOWORK=off GOTOOLCHAIN=go1.27.3 go test ./storage/backend/ -run TestA1 -count=1 -v` (~35 s).
- Pitfalls: `lean-check` on a fresh file rebuilds imports first (minutes), then says "stopped when the edited
  declaration was done": rerun with `-a`. In `TrkModel`, rewrite `bkOf ... = []` after `lastVal_append_single`, not
  before (simp turns `[] ++ [e]` into `[e]`). Builds: `/shared/tmp/build-slot.sh lake
  --packages=/shared/tmp/manifest-e9e.json build ...`; `LAKE_OPTS=--packages=...` for `etc/lean-check.py`, `--stop` it
  before ending a turn. Bucket view in auth is `BkView` (`Model.lean` has an `AuthView`).

## History

### A0 land stop (2026-11-17)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`. Session row in `/shared/etcd-grove-sessions.md`.
  Decisions: `questions.md` (Q1 (a), Q2-Q9; the A0 items, accepted).
- Done: Scope (b4528c167d); A0, the soundness repair (73ca90894e; accepted by the coordinator); lean 1612a1143a
  (k8s 7f-6 D) merged (2913cbf0a7: STATUS Last-updated ten newest, 7f-5a-P and kvreconfN moved to status-history;
  ledger both sides). Full build ok; `etc/gates.sh` all passed (tcb 877/4 = baseline, 65 collections, axiom-tok,
  bounds 390, mode 453, interfaces, links current), log `/shared/tmp/auth-schema-srv/gates-merge.log`.
- Now: the coordinator runs `etc/land.sh`. No commits to this branch until it says the land finished.
- Next, after the land: A1's own Scope (the backend read model over tracked hook buckets, with the window: per
  bucket, put buckets after, delete buckets before; over the backend's `RdSt` window flag and `dls`, per the Q9
  audit), then stop; then A2-A6, A7 (closed statements, to the user). Scope §3.
- Go tests: copy the test files into `server/storage/schema` of the clone `/shared/tmp/auth-schema-srv/etcd`
  (fork pin 6e8f0c004); `cd server; PATH=/usr/local/go/bin:$PATH TMPDIR=/shared/tmp systemd-run --scope -q -p
  MemoryMax=32G env GOWORK=off GOTOOLCHAIN=go1.27.3 go test ./storage/schema/ -run TestAuthSchemaRead -count=1 -v`.
- Pitfalls: `Model.lean` already has an `AuthView` (isOpPermitted's four views): the bucket view is `BkView`.
  `iexact` does not see through `(fun st => Hs (BkView.uni st)) st` vs `Hs (BkView.uni st)` or
  `(BkView.uni st).atUsers`: `dsimp only [BkView.uni]` first. Builds: `/shared/tmp/build-slot.sh lake
  --packages=/shared/tmp/manifest-e9e.json build ...`; `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json` for
  `etc/lean-check.py` (it printed nothing on a module whose import failed to build: build first). The worktree's
  `.lake/packages` had a stray Perennial clone (at e9e6351d9); moved to
  `/shared/tmp/auth-schema-srv/perennial-stray-from-worktree` so gates link PERENNIAL_CHECKOUT.

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
