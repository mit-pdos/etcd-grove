# auth-schema-srv: handoff

## START HERE (2026-11-17, A1 done: A1.9 checkpoint, report to etcd-grove-03)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. A1 Scope `notes/auth-schema-srv-a1-scope.md`; decisions and
  forms `questions.md` (untracked; **A1.5 decided**, **A1.6-A1.9**); soundness `notes/auth-schema-srv-a1-soundness.md`
  (§4.1 discharged, §5 the claim).
- Done: A1.1-A1.5 (52d85a42f6 … 149ad8bdd5); A1.6-A1.8 496f8061dd (`rbSide … I`, `trkSide`'s `I = tkI P st`; idle
  steps at `Unlock`'s end; `batchLocked_claim`; claimed parts' split laws; `rbRd`/`rbrHalves` sealed); **A1.9 (this
  commit)**: full build ok (20455 jobs, log `/shared/tmp/auth-schema-srv/a19-build1.log`); `etc/tcb-report.py --check`
  matches the baseline (892 axioms, 4 sorries); interfaces regenerated (`ClaimedLemmas`, `TrkModel`, `UnlockClaimed`
  new); layout baseline + `Unlock.wp_proofC`; `etc/import-all.txt`: `ClaimedLemmas` sealed, allows for
  `ClaimedLemmas`/`ReadLemmas`; api-check 0 errors, import-all-check ok.
- Next: the coordinator's go after the A1 report; then A2-A7 (`notes/auth-schema-srv-scope.md` §3); before landing:
  merge lean, `etc/gates.sh` via land.sh (coordinator).
- Pitfalls: (1) a hand-written `if m = n` picks `instDecidableEqString`, the laws' `if S n` (open Classical)
  `Classical.propDecidable`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (2) `unfold` does not
  beta-reduce `(fun n => S n ∨ S' n) n`: `dsimp only`. (3) A theorem's default argument (`trkHalf_eq … I`) is
  filled with the default when omitted: pass it. (4) Macros: frame patterns as ``$(frameH `H)``. (5) Stray
  Perennial clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris.

## History

### A1.6-A1.8 (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. A1 Scope `notes/auth-schema-srv-a1-scope.md`; decisions and
  forms `questions.md` (untracked; read **A1.5 decided** and **A1.6-A1.9**); soundness
  `notes/auth-schema-srv-a1-soundness.md` (§4.1 discharged, §5 the claim).
- Done: A1.1 52d85a42f6; A1.2a c0ae7d8a3e; A1.2b 0e825c0590; A1.3 b573c5d64e; A1.4 3e072b3ca8; A1.5 149ad8bdd5
  (accepted by etcd-grove-03); **A1.6-A1.8 (this commit)**: `rbSide … I` with `trkSide`'s `I = tkI P st` (flag
  clear ⇒ kind idle); idle steps moved to `Unlock`'s end (MAJOR 1); `batchLocked_claim` + claimed parts' split
  laws (`ClaimedLemmas.lean`, end); `rbRd`/`rbrHalves` sealed; `ClaimedLemmas`/`UnlockClaimed` importable.
  Checked with lean-check (TrackedLemmas, ClaimedLemmas, InvBatch, InvCommit, NewAlloc, ReadLemmas, unsafeCommit,
  Unlock: 0 errors). No full build yet.
- Next, A1.9: full build (`/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build`, retry on
  exit 143), `LAKE_OPTS=… etc/tcb-report.py --check` (no axiom/sorry change expected), `etc/gen-interface.py
  etc/api/backend.txt` (+ `--layout --update`: `Unlock.wp_proofC` a new layout entry), `etc/api-check.py
  etc/api/backend.txt --check`, `etc/import-all-check.py`; commit; report A1's end to etcd-grove-03.
- Then A2-A7 (`notes/auth-schema-srv-scope.md` §3).
- Pitfalls: (1) a hand-written `if m = n` picks `instDecidableEqString`, the laws' `if S n` (open Classical)
  `Classical.propDecidable`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (2) `unfold` does not
  beta-reduce `(fun n => S n ∨ S' n) n`: `dsimp only`. (3) A default argument of a theorem (`trkHalf_eq … I`) is
  filled with the default when omitted: pass it. (4) Macros: frame patterns as ``$(frameH `H)``. (5) Stray
  Perennial clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris.

### A1.5 (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. A1 Scope `notes/auth-schema-srv-a1-scope.md`; decisions and
  forms `questions.md` (read **A1.5** first); soundness `notes/auth-schema-srv-a1-soundness.md` (complete, §4 the
  obligations; review of A1.4: `/shared/tmp/auth-schema-srv/a1-soundness-review.md`).
- Done: A1.1 52d85a42f6; A1.2a c0ae7d8a3e; A1.2b 0e825c0590; A1.3 b573c5d64e; A1.4 3e072b3ca8; **A1.5 (this commit)**:
  `ClaimedLemmas.lean` (`rbAcc`, `unlockOk`, `trkSide_updR`, `trkSide_mode`, `rbPartR_idle` private, `batchGhostAt_clr`,
  `batchLocked_claimed`/`_cwOk`/`_rbPartR_RB`); `UnlockClaimed.lean` (`Unlock.specC`); `Unlock.wp_proofC`, and
  `Unlock.wp_proof` its corollary; mode on `batchLockedW`/`batchGhostW`; `commit`/`unsafeCommit` specs take `c Sc Rr`;
  `wbSt` resets `cw` on buckets left idle. Built (targeted, log `/shared/tmp/auth-schema-srv/a15-build1.log`): backend
  `Link`, `OnPreCommitUnsafe`, `CindexBackend`, `lessor.initAndRecover`, mvcc `BackendBridge`. No full build;
  interfaces not regenerated (A1.9).
- Waiting on: etcd-grove-03's review of the A1.5 forms (questions.md A1.5) and the soundness argument.
- Next after the go: A1.6 (lock-free commits keep `γ.rbr`: mostly done by A1.5's commit change), A1.7 the claim law
  **with** the invariant "flag false ⇒ tk idle" in `rbrOne` and `unlock_idle`/`unlock_idleR` moved to `Unlock`'s end
  (soundness §4.1, open item), A1.8 callers (rename `specC` → `spec`?), A1.9 interfaces/gates (add `ClaimedLemmas`,
  `UnlockClaimed` to `etc/api/backend.txt`; `Unlock.wp_proofC` is a new layout entry; seal `rbrHalves`?).
- Pitfalls: (1) `ihave H := lemma $$ [A B]` opens a subgoal for the premise FIRST: use `$$ [$A $B]`. (2) In
  `bu_commit` the commit pre's tail after `iframe` is `commitReq ∗ ⌜…⌝ ∗ Rr` (X already gone). (3) `.rfl` converts
  `batchPhys`/`batchGhostAt` between `st` and `st.clrCw` (no definition reads `cw` but `rbrSide`/`rbrOne`/`cwOk`/
  `trkKept`). (4) `rw` with a higher-order `?Φ k` pattern fails: pass the family explicitly. (5) Stray Perennial
  clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. Builds: `/shared/tmp/build-slot.sh
  lake --packages=/shared/tmp/manifest-c6b.json build <targets>`; lean-check with `LAKE_OPTS=--packages=…`, `-q`, `--stop`
  before builds.

### A1.4 (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. A1 Scope `notes/auth-schema-srv-a1-scope.md`; decisions and
  forms `questions.md` (A1.1, A1.2a, A1.2b, **A1.4**: read A1.4 first).
- Done: A1.1 52d85a42f6; A1.2a c0ae7d8a3e; A1.2b 0e825c0590; A1.3 b573c5d64e; **A1.4 (this commit)**: `BSess.cw`;
  the mode `c` (trailing default `false`) on `batchLocked`…`rbrSide`, `cwOk`; sealed claimed parts
  `rbPartRF`/`rbPartR`/`rbOwnInR` (half a `γ.rbc` element); `rbPut … k` (`k = true`: `rbPutR`); `rbrOne`'s claimed
  branch `tk idle ∨ cw` with the `γ.rbk` half as `rbPart`; the five write specs `∀ (c k) {_hkc : k ≤ c}`;
  `trkKept` keeps `cw` (ledger addendum). Built (targeted): backend `Link`, mvcc `BackendBridge`/`NewStoreSessReal`/
  `BackendRecsSnap`/`NewStoreRCallers`, `InvHooks`, `OnPreCommitUnsafe`, `CindexBackend`, `lessor.initAndRecover`,
  and the 31 importers naming the write specs/`batchLocked`/`hookStep` (`/shared/tmp/auth-schema-srv/a14-targets.txt`,
  log `a14-build4.log`). No full build; interfaces not regenerated (A1.9).
- Next, A1.5: `Unlock`'s accessor (Scope D5): mode-`c` `Unlock.spec` with the claimed set `Sc`, premise
  `∀ n, st.cw n → n ∈ Sc`, the client's halves `rbRd γ n ½ _` reached by `Rr ={⊤}=∗ …` at the write-back
  (`rtRes_wb_close*`'s update wand, built today by `trkSide_upd`) and at the commit (`rtRes_cm_close`, in
  `unsafeCommit`); `Unlock.spec_old` the `Sc = ∅`, `c = false` corollary. Design points already fixed: `cw` kept by
  the write-back for `del` buckets, reset for buckets that become idle (decide in `wbSt`); the commit runs the hook in
  the client-facing mode with `cw` non-empty (allowed: `cnt.hw = true`), the hook keeps `cw` (`trkKept`); replace
  `rbrSide_step`/`trkSide_upd`'s "`cw` empty" premises by the accessor. Then the HARD STOP: complete
  `notes/auth-schema-srv-a1-soundness.md` (draft written; §4.1, the claim law's invariant vs the axioms returning
  `rbOwnIn`, is the point to attack) and report.
- Pitfalls: (1) `simp only [↓reduceIte]` does not reduce `if false = true`: `rbPut`'s new `if k` needs
  `Bool.false_eq_true` where an `RB = true` branch is simplified. (2) A Lean arrow after a spec's trailing binders
  becomes an open goal under `wp_apply` (`forallMetaTelescope` + `wp_apply_side` decides only arithmetic): hence
  `{_hkc : k ≤ c}`; a caller that does not frame `rbPut` must pass `false false`. (3) `hookStep` 13 conjuncts, the last
  `trkKept` (3 now: W, tk, cw); `bgOk` 10; `freeOk` 6. (4) Stray Perennial clone: keep `.lake/package-overrides.json`
  (copy of the c6b manifest); `ls .lake/packages` = Qq, batteries, iris. Builds: `/shared/tmp/build-slot.sh lake
  --packages=/shared/tmp/manifest-c6b.json build <targets>`; lean-check with `LAKE_OPTS=--packages=…`, `-q`, `--stop`
  before builds.


### A1.2b/A1.3 (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean 9702d5707e merged. Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. A1 Scope `notes/auth-schema-srv-a1-scope.md`; decisions
  `questions.md` ("A1 Scope decided", forms "A1.1", "A1.2a", "A1.2b": read A1.2b's design gap first).
- Done: A1.1 (52d85a42f6); A1.2a (c0ae7d8a3e); A1.2b (this commit): `BNames.rbr`/`rbc`; `rbrHalves` in `clnPart`
  and `rtCm`; `rbrOne`/`rbrSide` (sealed) inside `trkSide` (replaces `trkHalf` in `batchGhostAt`/`W`); laws in
  `TrackedLemmas.lean` (end): `rbr_alloc`, `rbrSide_init`, `rbrHalves_frac`, `rbrSide_congr`, `rbrSide_write`
  (claimed bucket excluded: `rbr_claimed_excl`), `rbrSide_step`, `trkSide_congr`, `trkSide_upd`; read-side steps take
  the update wand; `batchGhost_step*` take the kinds of the other buckets (`hK`). Built: backend `Link`,
  `BackendBridge`, `OnPreCommitUnsafe`, `CindexBackend`, `lessor.initAndRecover`, `MustUnsafeGetAllLeases`. No full
  build yet; interfaces (`etc/gen-interface.py etc/api/backend.txt`) not regenerated (do at A1.9).
- A1.3 (next commit): `rbRd γ n q v` (`InvBackend`: `⌜n ∈ rbD⌝ ∗` half-element of `γ.rbr`), in `ReadLemmas`:
  `rbrHalves_agree`, **`rtHeldF_rbRd`** (the readers' law, D4), `rbRd_frac`, `rbRd_agree`. Built `ReadLemmas`.
- Next, in order: A1.4 claimed parts `rbPartR`/`rbOwnInR`
  (sealed: half of `γ.rbc`'s element `some (r n, F)`), `BSess.cw` (A1.2b gap), writes through either part; A1.5
  `Unlock` accessor (wand into `rtRes_wb_close*`/`rtRes_cm_close` built from `trkSide` + client halves), STOP with
  the soundness argument (decision 5).
- Pitfalls: (1) **the stray Perennial clone's cause**: `lake serve`'s workers run `lake setup-file` without
  `--packages`, so `etc/lean-check.py` cloned and built Perennial into `.lake/packages/perennial`. Fixed here by
  `.lake/package-overrides.json` (a copy of `/shared/tmp/manifest-c6b.json`; Lake reads it on every invocation):
  keep it; check `ls .lake/packages` (Qq, batteries, iris only). (2) `hookStep` 13 conjuncts, `bgOk` 10
  (`Hbg.2.2.2.2.2.2.2.2.2.2.1` is `trkOk`), `freeOk` 6. (3) `iframe` does not see `(commitSt …).S` as `st'.S`:
  convert with `(show … ⊢ … from .rfl)`. Builds: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json
  build <targets>`; lean-check with `LAKE_OPTS=--packages=…`, `-q`, `--stop` before builds.


### A1.2a (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean 9702d5707e merged (2f92623f49; Perennial
  pin c6b39d4f8: use `--packages=/shared/tmp/manifest-c6b.json` everywhere). A1 Scope
  `notes/auth-schema-srv-a1-scope.md`; decisions `questions.md` ("A1 Scope decided", forms "A1.1", "A1.2a").
- Done: A1.1 (52d85a42f6, `TrkModel.lean`); A1.2a (c0ae7d8a3e): `RbK`/`TkMap`/`tkSet`/`tkWb`/`wEmpty`/`kOk`/
  `trkOk`/`trkKept` in `Model2.lean`, `BSess.tk`, `trkOk` in `bgOk`, kinds idle in `freeOk`, `hookStep` keeps
  `trkKept` (ledger 2026-11-17), commit specs take "kinds idle or del"; backend `Link`, `InvHooks`,
  `OnPreCommitUnsafe`, `CindexBackend`, `BackendBridge`, `lessor.initAndRecover`, `BootBackend`, `InvApply`,
  `InvBoot`, `MustUnsafeGetAllLeases` build. No full build yet.
- Next, A1.2b (design fixed, not started): BNames `rbr` (ghost map name ↦ `BktData`, the readers' contents
  `rvBkt P rv n` of each name of `rbD`) and `rbc` (ghost map name ↦ `Bool`, claimed). The `rbr` authority (`∃ M`,
  full) and the `rbc` authority on the **batch lock side** (every `rv` change, write-back and commit, holds the batch
  lock). Element halves: `readTx.mu`'s ½ split by `q` (add `[∗map] n ∈ rbD, elem γ.rbr n (q/2) (rvBkt P rv n)` to
  `clnPart`, which takes `rv`; 19 uses), the other ½ on the lock side for an unclaimed bucket (`elem γ.rbc n 1
  false ∗ elem γ.rbr n ½ (rvBkt P (st.C, st.R) n)`) or the client's (`rbRd γ n q v := elem γ.rbr n q v ∗ elem γ.rbc
  n □ true`). Where the lock side goes: a new conjunct of `batchGhostAt` (many `%Hok⟩` patterns) or inside
  `trkHalf` given `(C, R)` (fewer sites): decide by counting. Allocation in `NewAlloc.lean` beside `rbEls_alloc`
  (line ~535). Then A1.3 (readers' law from `clnPart`'s halves), A1.4 (claimed parts `rbPartR`/`rbOwnInR`,
  sealed), A1.5 (`Unlock` accessor; update the halves in `ReadSide`'s `rtRes_wb_close*`/`rtRes_cm_close`), STOP
  at A1.5 with the soundness argument (decision 5).
- Pitfalls: a stray Perennial clone appears in `.lake/packages` (twice now; moved to
  `/shared/tmp/auth-schema-srv/perennial-stray*`): check `ls .lake/packages` before building (only Qq, batteries,
  iris links). `hookStep` has 13 conjuncts (the last `trkKept`), `bgOk` 10 (the last `w ≤ ver ∧ trkOk ∧ free→idle`:
  `Hbg.2.2.2.2.2.2.2.2.2.2.1` is `trkOk`), `freeOk` 6 (`.2.2.2.2.1` is `hw`). Builds via `/shared/tmp/build-slot.sh
  lake --packages=/shared/tmp/manifest-c6b.json build ...`; edit scripts in `/shared/tmp/auth-schema-srv/scripts/`.

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
