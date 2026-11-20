# auth-schema-srv: handoff

## START HERE (2026-11-20 m, AT THE LAND STOP: no commits until the coordinator says the land finished)

- Branch `auth-schema-port` (worktree `/shared/etcd-grove-authschema`), pin 3afd77e35 (`--packages=/shared/tmp/manifest-3af.json`,
  `.lake/package-overrides.json` = it, `PERENNIAL_DIR=/shared/perennial-3afd77e35`). lean `34986d22ae` merged (8798fdc497);
  `auth-schema-srv` fast-forwarded to `auth-schema-port` (checkpoint B).
- Build 5 `20261119-222252-2311069` green (162 modules, before the merge); build 6 `20261119-235631-2598891` green (7303 modules,
  1h35m, after the merge).
- Checks after build 6: every gen-link mode + btree (no change), interfaces --check --layout (6 packages; bbolt/backend
  regenerated d049248bbe, `batchTxBuffered__Commit` importable 7f011bbc49), tier, gen-init/gen-raft-tla/copy-part/gen-k8s-deep
  --check, goose --check (all projects), axiom-tok --check + selftest, bounds (allow entry 7f011bbc49), api-check, import-all,
  errorf, mode, model-param, pbschema, reader-slot, bgcancel (needs a path manifest: `/shared/tmp/auth-schema-srv/manifest-path.json`),
  issues-status. tcb `--check --update`: 785 → 787 axioms (+ `proto.MarshalUser/MarshalRole.wp_proof`, A3), 2 sorries; collections
  auth3/authN/authkv + `proto.(Un)marshalUser/Role`, server + the Marshal pair (7c56732d06).
- C: `python3 /shared/tmp/auth-schema-srv/stmtdiff2.py lean`: 20/20 OK, only hD22 removed. Trusted text (TrustedCode, GooseLang):
  unchanged vs lean; `Code/go_etcd_io/bbolt.lean` re-translated from the fork (verified code).
- Next: the coordinator's land go: merge lean once more if it moved (k8s 7g), rerun what the merge touches, then land.
- Pitfalls: (46)-(49) below; (50) gen-init needs `PERENNIAL_DIR`, bgcancel a path manifest in `LAKE_PACKAGES`; never `git stash` with
  uncommitted baselines (popped back once, 2026-11-20).

## History (START HERE of 2026-11-19 l, superseded)


- Branch `auth-schema-port` (worktree `/shared/etcd-grove-authschema`), head = this commit; pin 3afd77e35
  (`--packages=/shared/tmp/manifest-3af.json`, `.lake/package-overrides.json` = it, `PERENNIAL_DIR=/shared/perennial-3afd77e35`).
  lean 5f94c44bee merged (f3278f12b4); merge lean again if it moved (grpc-stats origin merge expected). `auth-schema-srv`
  still cc85342beb: fast-forward it to `auth-schema-port` at checkpoint B.
- Route (d') (user, 2026-11-19; questions.md, ledger "the auth records' size"): bbolt fork 3f8520b (pushed by the user,
  branch `goose-lean-entrymax`), `etc/goose.py` pin, examples/go.mod bumped; `etc/goose.py --check` passes (all projects).
  Coded: `Bucket.Put.spec` in place + PutWp (fresh lean-check clean); backend `unsafePut`/`UnsafePut`/`UnsafeSeqPut`
  (premise dropped, post: entry ≤ 2^28, Fatal arm) and `batchTxBuffered.UnsafePut/SeqPut`; 8 direct callers; issue files.
- **Build 4** (`20261119-205653-1967841`): the only failure was `backend.batchTx__unsafePut` (Fatal arm: `wp_auto` on
  `match err`), fixed in 8f5882ebfa (fresh lean-check of unsafePut + UnsafePut clean); its dependents were not built.
- **Next, in order**: (1) full timed build 5: `/shared/tmp/build-slot.sh etc/timed-build.py --packages=/shared/tmp/manifest-3af.json`
  (expect breaks only downstream of the Put specs: batchTxBuffered Put proofs, callers listed in
  `/shared/tmp/auth-schema-srv/putcalls.txt`, AuthRealWr's `lk_put`/`lk_putA`); report its id.
  (2) gen-link all modes (loop: `/shared/tmp/auth-schema-srv/links/map.txt`, `LAKE_OPTS=--packages=...`), interfaces
  (`etc/gen-interface.py etc/api/<pkg>.txt` for bbolt, backend, others that differ: `--check` first), tier-check,
  gen-init `--check`, gen-raft-tla `--check`. (3) tcb `--check --update` (expected: −2 ForEach axioms vs 794/2 baseline,
  plus any delta) and every collection (`--collection … --check --update`). (4) checkpoint B report (soundness §8 +
  independent check done: notes/auth-schema-srv-a1-soundness.md §8). (5) C: `python3 /shared/tmp/auth-schema-srv/stmtdiff2.py lean`
  (20 statements incl. the three `*_robust.spec`: only hD22 removed), trust-base delta, stays/leaves list; land stop.
- Pitfalls: (46) duplicate `Countable Qp`: `attribute [-instance] Perennial.Fs.Qp.countable` in the realization files;
  (47) PutWp: clear facts on `sint.Z (W64 268435456 - key.len)` before `omega` (kernel deep recursion); no `contradiction`
  near `bboltEntryMax`; (48) a Go-interface `err` from a spec post: destruct it (`err = ok eo`) before `wp_auto` on
  `err != nil`; (49) lean-check `-a` after a stopped incremental run says "unchanged": `--stop` and recheck fresh.

## History (START HERE of 2026-11-19 k, superseded)

## History (START HERE of 2026-11-19 i, superseded: stop on option (1))

## History (START HERE of 2026-11-19 h, P3-P5 BLOCKER: UnsafePut's entry-size premise)

- Staging branch `auth-schema-port` (worktree `/shared/etcd-grove-authschema`), pin 3afd77e35:
  `--packages=/shared/tmp/manifest-3af.json`, `.lake/package-overrides.json` = that manifest. `auth-schema-srv` still at
  cc85342beb (fast-forward at checkpoint B, not reached). Checkpoint A ACCEPTED (questions.md).
- **Done**: e0fba3c0e6 the four `UnsafeForEach` callers over lean's vocabulary (read: visitor `txLive rtx γ.db q (ro
  rv.1)`; batch: `∀ G`, `ownWTxG st.tx γ.db st.C st.S G`); 525d00e65f backend Link regenerated + realization vocabulary
  (`rdB γ.db`, `txBytes … γ.db`, `kvsOutRd_* γ.db`); backend Link target builds green (3804 jobs); every other gen-link
  mode: no change. e5737627bc soundness §8 + independent check (OK, 3 MINORs). 8f9a9f734c, 5969f26472: realization files
  `attribute [-instance] Perennial.Fs.Qp.countable` (iris now has `instCountableQp`; the duplicate split the pools'
  ghost-map instance).
- Full timed builds: 20261119-180506-1343931 (failed: AuthRealInv, fixed), 20261119-190055-1577997 (failed only at
  `AuthRealWr` l.1209/1260; everything else up to it green).
- **BLOCKER**: lean's `batchTxBuffered.UnsafePut.spec` takes `kb.length + vb.length ≤ bbolt.bboltEntryMax` (2^28);
  `lk_put`/`lk_putA` (AuthRealWr) put `userEncode ur`/`roleEncode rr` whose size nothing bounds (the schema write
  contract gives only key bounds; `authSmall` bounds roles/permissions by the revision ≤ 2^61; `authRecordsFit` is an
  opaque Prop with no law). Needs a decision (report of 2026-11-19 h); no Lean change made for it.
- Next after the decision: fix `lk_put`/`lk_putA` and their callers, rerun the full timed build, tcb `--check --update`,
  collections, interfaces, tier-check; checkpoint B; then C (stmtdiff: `/shared/tmp/auth-schema-srv/stmtdiff2.py lean`,
  20 statements incl. the three `*_robust.spec`, currently all OK with only hD22 removed).
- Pitfalls: (44)-(45) as before; (46) a file importing the file extension and iris's ghost maps over `Qp` needs
  `attribute [-instance] Perennial.Fs.Qp.countable` (or delete the duplicate in `GooseLang/Ext/{Fs,OsFs}/Ghost.lean`).

## History (START HERE of 2026-11-19 g, PORT CHECKPOINT A, superseded)


- Port Scope ACCEPTED by etcd-grove-03 (questions.md "Port Scope ACCEPTED"): staging branch `auth-schema-port`
  (worktree `/shared/etcd-grove-authschema`), pin 3afd77e35: `--packages=/shared/tmp/manifest-3af.json` everywhere,
  `.lake/package-overrides.json` = that manifest, `PERENNIAL_DIR=/shared/perennial-3afd77e35`. `auth-schema-srv` stays
  at cc85342beb until checkpoint B (fast-forward then).
- **Done**: b0a40c1277 merge of lean e95ce79ce9 (Scope §2.A resolutions; not compiled; interfaces/tcb/collections/
  backend Link taken from lean, to regenerate). 7940a3e03b P2: `Spec/go_etcd_io/bbolt/Bucket__ForEach.lean` +
  proof (public Cursor/First/Next), bbolt Link/Results regenerated, `etc/api/bbolt.txt`, A2's `_kv` ForEach axioms
  deleted. Next commit: `unsafeForEach` over `Tx.Bucket` + `Bucket.ForEach` (spec: `txLive tx γd q T`,
  `T.rw → q = 1`, entries `bktOf T.cur`); `FeSide`/`feOwn` deleted from `InvBackend`. Both lean-checked clean.
- **Next (P3)**: the backend's callers of `unsafeForEach` (`baseReadTx`/`readTx`/`batchTx`/`batchTxBuffered`
  `.UnsafeForEach`: visitor gets the walk's `txLive` at its view, batch `∀ G` + `wView st.C st.S G` at 1, read
  `ro rv.1` at q), then Scope §2.C compile-fix, backend Link (`LAKE_OPTS=... etc/gen-link.py --backend`), P4
  realization, P5 full timed build via build-slot (`etc/timed-build.py`), P6.
- Pitfalls: (44) a backend glue lemma's statement needs `txLive (GF := GF)` (else `TypedPointsto w8` stuck) and
  no `open go_etcd_io.bbolt ... in` around backend names (`txBytes` resolves to bbolt's: `HasExt` missing).
  (45) lean-check `-a` after a stopped incremental run says "unchanged": `--stop` and re-check fresh to trust it.

## History (START HERE of 2026-11-19 f, PORT SCOPE STOP, superseded)

- Decided by etcd-grove-03 (questions.md "BLOCKER ... decided"): port this branch's backend onto lean's (bbolt-integrate),
  prove bbolt's `Bucket.ForEach` (canonical, no twin; A2's two `_kv` axioms leave), A7's statement change after the port.
- **Done**: the Scope, `notes/auth-schema-srv-port-scope.md` (trial merge only: `git merge-tree`, conflicts in
  `/shared/tmp/auth-schema-srv/mt.txt`). STOP for its independent review; branch otherwise unchanged (99a71018a7 + this).
- Next after the review: Scope §6 P1-P6 (staging branch `auth-schema-port`, pin manifest-3af, PERENNIAL_DIR=/shared/perennial-3afd77e35).

## History (START HERE of 2026-11-19 e, A7 linked; LAND STOP, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; pin f551a1b46: `--packages=/shared/tmp/manifest-f55.json`
  everywhere (`.lake/package-overrides.json` = that manifest); gen-init with `PERENNIAL_DIR=/shared/perennial-f551a1b46`.
- A7 approved by the user 2026-11-19 (questions.md "A7 approved"); forms in questions.md "A7 link forms".
- **Done**: lean df37bd5157 merged (a719190cf9; Scratch/ moved to `/shared/tmp/auth-schema-srv/scratch-moved`, it broke
  tier-check); the link (2add4c3ae2): `authSchemaSrv` moved to `AuthSnapKit.lean`, `authStoreKit_on` uses
  `authReal.real_srv` (47 specs; the kit's pre carries `isPkgInit backend/schema` and `receiptBound GF ≤ 2^48`, discharged
  in `NewServer`/`NewServerR`), `authSrvTP_on` takes the specs, `srv_auth_tp_on` links them; `hD22` gone from the three
  closed theorems, their `*_robust` and chains (statement diff: `/shared/tmp/auth-schema-srv/stmtdiff.py`, all OK).
  Full timed build green (`20261119-113918-3123454`, 1h31m); tcb `--check` matches the baseline (888 axioms, 4 sorries);
  collections authkv/auth3/authN +6 axioms, server +2 (committed); interfaces `--check` clean (all six); gen-link
  --server/--authkv/--backend/--mvcc: no change. Then lean (per-heap, 1e4cb38613) merged again (e6993af3bb): rebuild,
  re-checked: full timed build green (`20261119-143502-174164`), tcb `--check` matches (886 axioms, 4 sorries), all
  collections match, interfaces and Links unchanged, tier-check ok. Isolation plan ACCEPTED (etcd-grove-03).
- **BLOCKER (questions.md "BLOCKER: merging lean e95ce79ce9")**: lean moved to e95ce79ce9 (pin 3afd77e35, bbolt-integrate);
  the merge conflicts in 16 Lean files of the backend (both sides redesigned its invariants) and lean removed the `_kv`
  layer this branch's A2 ForEach axioms belong to. Merge aborted; awaiting the coordinator's decision.
- Land: `LAKE_PACKAGES=/shared/tmp/manifest-f55.json PERENNIAL_CHECKOUT=/shared/perennial-f551a1b46
  PERENNIAL_DIR=/shared/perennial-f551a1b46 etc/land.sh` (GOWORK unset), only when the coordinator says go.
- Pitfalls: (0)-(42) as before (History); (43) the TCB tool's statement scan must skip `:=` inside parentheses
  (`(GF := GF)`).

## History (START HERE of 2026-11-19 d, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; pin 6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json`
  everywhere (`.lake/package-overrides.json` = that manifest). When lean has "Merge origin/lean (d52bb9be66)": merge,
  switch to manifest-f55 (and the overrides copy), full timed rebuild.
- Decided 2026-11-19 by etcd-grove-03 (questions.md "A6 K-c, real_bkLend, V-pub decided"): K-c, `real_bkLend`
  ACCEPTED; V-pub ACCEPTED (internal) after an independent check, done: OK, two liveness MINORs (questions.md).
- **Done** (b7c4a39873, c43860f056, bf2c6f69d9): AuthRealWr's 18 errors fixed; AuthRealNew compiles; new
  `etcdserver/AuthRealSrv.lean`: `real_srv : isPkgInit backend ∗ isPkgInit schema ⊢ authSchemaSrv` and `real_snap`
  (`authSchemaSnap` at the tickets over the vault), over 47 proved callee specs and `receiptBound GF ≤ 2^48`; no axiom
  or sorry. Targeted build rc=0 (`/shared/tmp/auth-schema-srv/srv-build1.log`: AuthRealSrv, server Link, backend
  Link, ImageOn, RoleList); backend interface `--check` clean (no etcdserver API config exists, nothing to
  regenerate there). Full timed build GREEN (21852 jobs, build id `20261119-034000-1196107`, 49m26s); interfaces `--check`: backend, etcdstart, raft, bbolt clean, mvcc regenerated (A6.2's `BNames` fields, (c)'s `viewSame_*` at any `cl`); `tcb-report --check` matches the baseline (895 axioms, 4 sorries).
- **A7 STOP** (`notes/auth-schema-srv-a7.md`): the link drops `hD22` from `etcd_auth_safe`, `etcd_auth3_safe`,
  `etcd_authN_safe` and their chains; the trusted-text list with what stays in the TCB; the trust-base delta. Nothing
  linked until the user decides.
- Next after the decision: the link (`authStoreKit_on` at `AuthSrv.lean:496` uses `real_srv`; package inits from the
  context's `isPkgInit`; `hRB` from `ReceiptBoundLe`), regenerate Links (`LAKE_OPTS` for gen-link), collections
  `--check --update`; land stop.
- Pitfalls: (0)-(39) as before (History); (40) lean-check's output right after an edit can repeat the previous run's
  errors: re-run before trusting it; (41) `iexact`/`iframe` match only up to reducible unfolding: convert a hypothesis
  with `iapply (show A ⊢ B from .rfl) $$ H` (record projections, `authBktL`, `authRolesName`, `0 + 1`), and unfold a
  tactic `let` in the goal with `dsimp only [L]`; (42) an Iris hypothesis applied to arguments in a term
  (`wp_apply (H a b)`) is an unknown identifier: write `wp_apply H $$ %a %b [..]`.

## History (START HERE of 2026-11-19 c, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; pin 6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json`
  everywhere (`.lake/package-overrides.json` = that manifest; f551a1b46 / manifest-f55 comes with the next lean merge).
- Decided 2026-11-19 by etcd-grove-03 (questions.md "A6 O-a and STOP 6 decided"): O-a ACCEPTED; STOP 6 -> (K-c).
- **Done now**: (K-c) in the backend (ce1b9bc920): `rbPartRF` holds ⅛ of `γ.rbk` (an `rbEls` conjunct), `rbClaimC`
  ⅝; `rbPartRF_rbPart_agree` + corollaries (contents only); independent check done (soundness §7, forbidden laws
  amended in `rbOwnInR`'s docstring); backend lean-checked clean (InvBackend, TrackedLemmas, ClaimedLemmas).
  `real_bkLend` (AuthRealWr end). (e) F-pub found and fixed internally by V-pub (43746319cc; questions.md "A6 (e)
  F-pub"): store vault `pubVault`/`vaultInv`, live branch `liveP`, retired branch the apply quarter at `p`,
  `real_view` takes the reader's `depT`, `real_retire`/`real_life` take `vaultInv`. `AuthRealNew.lean`:
  `real_create`, `vault_alloc`, `vault_take`.
- **Build state** (kc-build2, rc=1 only at AuthRealInv, since fixed): backend, auth (RoleList), schema, ImageOn and
  everything not under AuthRealInv built. lean-check clean (whole file): AuthRealInv, AuthRealRsv, AuthRealLife,
  AuthRealRd. **AuthRealWr: 18 errors** (`/shared/tmp/auth-schema-srv/wr-errors.txt`), all in c89577b8ed's never-compiled
  code: `lk_claim` fixed; left: the `Unlock` clause (l.1882, 2602: `iapply (Hunl st X …)` treats an Iris hypothesis as
  a term: write `iapply Hunl $$ %st %X %w %(wbTok d.γB)` / `wp_apply (Hunl …)` likewise), `real_forceCommit`-area
  `▸` (2018), `real_getAllRoles` (2126: `BSess` literal has 12 fields; 2176 `Hrd`, 2206/2229 unsolved, 2243 `Hlock`,
  2268 a parse error that hides what follows), `real_createAuthBuckets` (2499, 2568-2594: `lkI` counts `0 + 1` vs
  the goal's form), `real_wAtHook` (2668 `plHookRO`). Then lean-check AuthRealNew (never compiled) and the server
  Link; regenerate the backend interface again if the backend changes (done for ce1b9bc920's state: 9 files).
- Next: `⊢ authSchemaSrv` (allocate γt's discarded authority (`ticketN`, R := `ownToks γt 1`), `vault_alloc`, split
  `authPubQ ½ 0` into the realization's ¼ and the post's `authPubTok`; `real_create` at `bootState`, `r` empty;
  then the clauses: `real_backendOk`, `real_wAtHook`, `real_wBoot`, `real_createAuthBuckets`, `real_bkLend`,
  `real_life`, the tickets, `authSchemaSnap` from `vault_take` + `real_create` (needs `viewAt` from `authBucketsAt`,
  the converse of `viewAt_bucketsAre`)); A6-end report; A7 HARD STOP (trusted list incl. K-c).
- Pitfalls: (0)-(37) as before (History); (38) questions.md is gitignored (worktree-local), commit the rest; (39) a
  foreground wait longer than 3 min is moved to the background: watch builds with a background `until grep rc=` loop.

## History (START HERE of 2026-11-19 b, STOP 6, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; pin 6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json`
  everywhere (`.lake/package-overrides.json` = that manifest; f551a1b46 / manifest-f55 comes with the next lean merge).
- Done before: A1-A5, A6.1-A6.2, fix (A), F-enc/F-acc, pool, L-rev/P2, read side, reserved reads, lifecycle, P1', (c),
  (R-c), `real_getAllRoles`, `real_wAtHook`, `real_wBoot`, `real_createAuthBuckets` (c89577b8ed; all ACCEPTED,
  questions.md "A6 R-c, A6 (d) forms and STOP 5 decided").
- **Done now**: (O-a) `schema.authBucketsAre`'s roles clause up to permutation (InvAuthBackend.lean); survey of its
  consumers in questions.md (all opaque; ~5 lines); ledger entry and the fifth refutation in
  `notes/auth-schema-srv-refuted.md`.
- **Build state**: c89577b8ed + O-a NOT yet compiled. Targeted build queued detached (setsid nohup):
  `/shared/tmp/auth-schema-srv/rc-build4.log` (backend Link, auth RoleList, AuthRealWr, AuthRealRd, ImageOn, server
  Link; ends with an `rc=` line). Then fix errors with lean-check (expect them in the new AuthRealWr code), regenerate
  the backend, schema and etcdserver interfaces (`etc/gen-interface.py etc/api/<pkg>.txt`, LAKE_OPTS).
- **STOP 6 (questions.md "A6 STOP 6")**: `authBkLend`'s law is fupd-free (Snapshot's observation is), the auth buckets
  are claimed, and only the claim invariant relates `rbOwn r` to claimed contents. Recommended (K-c): `rbPartRF` keeps
  ⅛ of `γ.rbk`, `rbClaimC` ⅝; a pure agreement law `rbPartR` vs `rbPart`; then `authBkLend` from a borrowed `bkIdle`.
- Next after the decision: (K-c) in the backend, `authBkLend`, (e) creation, `⊢ authSchemaSrv`, `authSchemaSnap`;
  A6-end report; A7 (HARD STOP; trusted list incl. R-c, O-a and STOP 6's item).
- Pitfalls: (0)-(36) as before (History); (37) a nohup build from a session can die with it: launch with `setsid nohup`.

## History (START HERE of 2026-11-19 a, STOP 5, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; pin 6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json`
  everywhere (`.lake/package-overrides.json` = that manifest). lean 1b298c1e70 merged.
- Done before: A1-A5, A6.1-A6.2, fix (A), F-enc/F-acc, pool, L-rev/P2, read side, reserved reads, lifecycle, P1', (c).
- **Decided 2026-11-19** (questions.md "A6 (c) forms and STOP 4 decided"): (c) forms ACCEPTED; STOP 4 -> (R-c).
- **Done now** (see the commit after c92d56d253): (R-c) `auth.rolesListed` (InvAuth) in `rolesOut` and `roleListOut`
  (ledger entry; independent check: no consumer uses completeness, no closed statement mentions role lists);
  `real_getAllRoles` (AuthRealWr; the bbolt tx pinned by a one-shot `dghostVar` set at Lock: `garLk`, `gar_rolesRange`;
  `rolesOutD_at`, `rolesListed_range`, `dRm`), `garClause` gone; the unused `lg ≠ null` premise dropped from schema's
  `unsafeGet{User,Role}`, `auth{Batch,Read}Tx.UnsafeGet{User,Role}`, `authBackend.Get{User,Role}` and the realization
  lemmas (authWAtHook quantifies every logger); `real_wAtHook`, `real_wBoot`; (d) `real_createAuthBuckets` (`lk_claim`
  factored out of `lk_lock`, `lkI`, `lk_create`, `lkOk_create`; `LkOk.pend` has a slack of 3; `unC`'s second token
  generic `Y`).
- **Build state**: everything above was queued in ONE targeted build, `/shared/tmp/auth-schema-srv/rc-build2.log`
  (backend Link, auth RoleList, AuthRealWr, AuthRealRd, server Link); the build slots were busy for hours. Expect
  errors in the new AuthRealWr code; fix with lean-check once the imports are built; then regenerate the backend,
  schema and etcdserver interfaces (`etc/gen-interface.py etc/api/<pkg>.txt`).
- **STOP 5 (questions.md "A6 STOP 5")**: F-order: `authBkLend`'s `authBucketsAt` needs the roles in the state's order;
  Go sorts, the model appends. Recommended (O-a) `authBucketsAre` up to order. `authBkLend` not started.
- Next after the decision: `authBkLend` (agreement law `rbOwn` vs claimed part through the claim invariant), (e)
  creation, `⊢ authSchemaSrv`, `authSchemaSnap`; A6-end report; A7 (HARD STOP; trusted list incl. R-c).
- Pitfalls: (0)-(35) as before (History); (36) the build slots poll randomly: a queued targeted build can wait hours;
  batch all edits before queuing.

## History (START HERE of 2026-11-18, STOP 4, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; pin 6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json`
  everywhere (`.lake/package-overrides.json` = that manifest). lean 1b298c1e70 merged.
- Done before: A1-A5, A6.1-A6.2, fix (A), F-enc/F-acc, pool, L-rev/P2, read side, reserved reads, lifecycle, P1' (ACCEPTED).
- **Done now, (c)** (`etcdserver/AuthRealWr.lean`, commits e1ef4bdf53 .. HEAD; forms in questions.md "A6 (c) forms"):
  backend: `Unlock`'s confirmation window `rbConf` (Rr → Rr'), commit's post keeps `rbData`, `UnsafeRange` in either mode,
  new `batchTxBuffered.UnsafeForEach` (spec/proof/link/importable), `batchLocked_rbPartR_agree`; `schema.rolesAt` up to
  order; session token `bkSw` (`γw`) in `bkIdle`. Realization: batch reader (`bt_reader`, `bt_rolesRange`), windows
  (`real_acc`, `real_conf`), borrow/return (`real_borrow`, `real_return`, `real_unborrow`), the lock token (`LkOk`, `lkR`,
  `lkT`), `lk_lock`/`lk_put`/`lk_putA`/`lk_del`/`lk_unlock`/`lk_commit`/`lk_reads`, `real_batchTxLkR` (T ⊣⊢ authWTok ∗ Hk),
  `real_forceCommit`, `real_wbackendOkR` (GetAllRoles as the premise `garClause`). lean-check clean (whole file, no sorry).
- **STOP 4 (questions.md "A6 STOP 4")**: F-roles: `rolesOut` lists every role but the range caps at `2^63 - 1` entries and
  nothing bounds a state's roles; recommended (R-c) weaken `rolesOut`/RoleList. Waiting for the decision.
- Next, after it: GetAllRoles (schema `authBackend.GetAllRoles.spec`: Lk m pins the batch's `tx` by a one-shot
  `dghostVar` set at Lock, `Lk m := ∃ bs st, ⌜bktOf bs.S roles = m⌝ ∗ pin(bs.tx) ∗ batchLocked … ∗ lkR … ∗ bkSw ½ init ∗
  authOwnF hs ∗ Wb ∗ Wb`; `dR m` by choice (as `dRL`); a `rolesOutD_at` from `rolesAt` via `cursorRange_window`/
  `mem_window`), then `authWAtHook` (T = authWTok, Hk = emp, `plHookRO f'`), the boot contract (Hk = plHook nil, f = nil,
  P = Pk); (d) `authBkLend`, `CreateAuthBuckets`; (e) creation, `⊢ authSchemaSrv`, `authSchemaSnap`; A6-end report; A7.
- Builds: `/shared/tmp/auth-schema-srv/c-build2.log` (backend Link, AuthRealWr, server Link). Interfaces of backend and
  etcdserver APIs not regenerated yet (`etc/gen-interface.py etc/api/backend.txt` after a build).
- Pitfalls: (0)-(31) as before (History); (32) after `wp_apply` the goal is the post: `iapply wp_fupd` first to `imod`
  after it; (33) a spec's state projection gets reduced (`(bs.put …).S` shows as `<[…]>bs.S`): pass `_` or `rw` a `rfl`
  equation (`hS`) before framing; (34) `(authD bs.S).users` vs the reduced bucket: `simp only [authD, mvcc.authUsersBI, …]
  at Hv` before using its parts; (35) a pattern variable over `▷` needs `Inhabited` (`inhAuthSess`).

## History (START HERE of 2026-11-18, A6: P1' and the write side's forms applied; (c) next, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean 1b298c1e70 merged (c6546c5303): pin
  6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json` everywhere (`.lake/package-overrides.json` = that manifest).
- Done: A1-A5, A6.1a/b, (b), A6.2 C1-C5, fix (A), F-enc + F-acc, the pool, L-rev/P2, the read side, (a) reserved
  reads, (b) the lifecycle (all ACCEPTED); **STOP 3 decided** (questions.md "A6 STOP 3 decided"): **P1'** applied
  (`auth.authLockQ` carries `∀ st ∈ hs, permKeysOk st`, Model.lean; independent read-only check: OK, every producer
  via `authHist_split`), and the forms: `bkIdle` takes `q0` and holds `bOpen q0` and the batch token `bkTok γ 1 (csT
  cs)` (a ghost variable of the three readers' contents); live branch `succ ∗ retired ∗ pools ∗ (bkIdle ∨ bkBatch)`,
  `bkBatch γ cs = authWTok ∗ bkTok γ ½ (csT cs)`; `batchTok γ = ∃ x, bkTok γ 1 x` (gone branches);
  `viewSame_putHB`/`viewSame_del` at any `cl` (BackendBridge). Builds: `p1-build1.log`, `p1-build2.log`
  (`/shared/tmp/auth-schema-srv/`); full build after P1': see the latest `p1-full*.log`.
- **Next, (c) the write side** (new file `etcdserver/AuthRealWr.lean`, importing AuthRealInv, mvcc BackendBridge,
  schema's `authBatchTx.*`/`authBackend.{BatchTx,ForceCommit,GetAllRoles}` specs, backend `batchTxBuffered.*`):
  1. a batch reader: `schema.authReader t H D` and `authRolesRange t H m` under `H ⊇ batchLocked γ P b st c` with
     `D` the auth buckets of `st.S` (from `batchTxBuffered.UnsafeRange.spec` (its `rdB` capability) and
     `batchTx.UnsafeForEach.spec`; model the read side's `schema.authBE_real`, schema `InvAuthBackend`);
  2. `Lk st X := ∃ bs k, batchLocked d.γB d.P d.be bs true ∗ rbPartR d.γB (· ∈ authBktL) (rbData d.P bs.S) ∗
     bkTok γ ½ x ∗ bOpen d.γB q0 ∗ W ∗ Pk ∗ X ∗ ⧗ k ∗ ⌜sessWf, cnt.hw = false, ndel/viewSame, cw ⊆ authBktL,
     tk n = idle → bktOf bs.S n = x.n, the writer's contents encode st (authAt/usersAt/rolesAt), pend < limit + k,
     permKeysOk st? (not needed: P1')⌝`; `Sw w := ⌜bs.tk users/roles = w's kinds⌝` inside Lk (Sw may be `True` and the
     kinds kept in Lk: Sw is the contract's own token, choose `Sw w := ghostVar`-free pure if possible);
  3. Lock: borrow (deposit `T`, take `bkIdle`, leave `bkBatch`), `LockInsideApply` (hookRun's non-nil branch from
     `csContractA`; boot token: nil branch with `plHook nil`), `batchLocked_claimed`, `rbOwnInR_part`;
  4. the six writes (schema's spec with the backend's `UnsafePut`/`UnsafeDelete` at `k = c = true`, `rbPartR_split`/
     `_congr`/`rbPutR`; `hkPut`/`fkPut` trivial off `Meta`; `isBucket` of schema's globals; receipts:
     `receipt_add_one_lt`, `receiptBound GF ≤ 2^48` a section premise, `P.Wf`: `limit ≤ 2^57`, `hookMax ≤ 2^16`);
  5. Unlock: schema's `authBatchTx.Unlock` = backend `Unlock` (first branch: `viewSame_thin`, `W ∗ Pk`, `Sc =
     authBktL`, `Rr = authLockI ∗ bkTok ½`, `rbAcc` opening `realInv` at `E = ⊤ ∖ ↑authRealN`: each moved or untouched
     bucket to `st` at `hs.length - 1` (`authStateAt` from `authLockQ`, P1'), a deleted-only kept bucket at its old
     state; back to idle at the first window or the second) then `Commit` (`commitReq_true`, `bOpen q0`);
  6. `authBackendReads.GetAllRoles` (Lock, `UnsafeGetAllRoles`, Unlock with `Sc = []`, `rbAcc_nil`), `ForceCommit`
     (borrow with `T`), `BatchTx`; then `authWBackendOkR` at `authWTok γc` (authWAtHook) and at the boot token.
  Then (d) `authBkLend`, `CreateAuthBuckets`; (e) creation and `⊢ authSchemaSrv`, `authSchemaSnap`; A6-end report.
- Pitfalls: (0)-(30) as before (History); (31) `bkTok` needs its `Timeless` instance (AuthRealLife) for `>` patterns.

## History (START HERE of 2026-11-18, A6 STOP 3, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean 1b298c1e70 merged (c6546c5303; fmt
  soundness: no repair needed, nothing of this branch names `errOk`/`fmt.Errorf`): pin 6d365ee1a,
  `--packages=/shared/tmp/manifest-6d3.json` everywhere (`.lake/package-overrides.json` = that manifest).
  Full build after the merge: `/shared/tmp/auth-schema-srv/merge-fmt-full1.log`.
- Done: A1-A5, A6.1a/b, (b), A6.2 C1-C5, fix (A), F-enc + F-acc, the pool, L-rev/P2, the read side, (a) reserved
  reads (80ed776890), (b) the lifecycle (bac82a9720); (a)/(b) and their forms ACCEPTED (questions.md "A6 reserved
  reads and lifecycle: decided").
- **STOP 3 (questions.md "A6 STOP 3")**: F-perm2, `Unlock` cannot record the session's state (`authLockQ` has no
  `permKeysOk`); recommended P1' (`authLockQ` carries `∀ st ∈ hs, permKeysOk st`, trusted text, ~20 lines).
- Next, after the decision, in order: (0) P1' if approved (Model.lean:701, `authHist_split`, `authHistHalf_lockQ_agree`);
  (1) the forms of STOP 3's last bullet (the idle branch holds `bOpen q0`; the batch token a ghost variable of the
  three readers' contents, ½ in the batch branch, ½ in `Lk`; `viewSame_putHB`/`viewSame_del` at any `cl`);
  (2) (c): `Lk st X` = `batchLocked … true` ∗ `rbPartR γB (· ∈ authBktL) (rbData P bs.S)` ∗ the token's ½ ∗
  `bOpen q0` ∗ `W` ∗ `Pk` ∗ `X` ∗ `⧗ k` ∗ pure (`freeOk`-derived facts, `cw ⊆ authBktL`, `tk` = `Sw`'s kinds, untouched
  ⇒ contents = the token's, the writer's contents encode `st` (`authAt`/`usersAt`/`rolesAt`), `pend < limit + k`);
  Lock deposits `T` (borrow lemma), Unlock with `Sc = authBktL`, `Rr` = the lock share ∗ token ½, `E = ⊤ ∖ ↑authRealN`;
  writes by schema's `authBatchTx.*` at `batchTxBuffered.UnsafePut/UnsafeDelete` (`k = true`, `rbPartR_split`);
  GetAllRoles (no writes: `Sc = []`, `rbAcc_nil`); ForceCommit (borrow `bOpen q0` with `T`); then (d), (e) as below.
  `⊢ authSchemaSrv` takes `receiptBound GF ≤ 2 ^ 48` (closed theorems: `receiptBound = n + 1`, `n + 2 ≤ 2 ^ 28`).
- Pitfalls: (0)-(30) as before (History).

## History (START HERE of 2026-11-18, A6 reserved reads and lifecycle, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean fb68edfec8 merged (lean has not moved since):
  pin 6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json` everywhere (`.lake/package-overrides.json` = that manifest).
- Done: A1-A5, A6.1a/b, (b), A6.2 C1-C5, fix (A), F-enc + F-acc, the pool, L-rev/P2, the read side (forms ACCEPTED by
  etcd-grove-03, questions.md "A6 read side: decided"); **(a) the reserved pool's reads** (80ed776890,
  `AuthRealRsv.lean`: `real_acqR`/`real_obsR`/`real_relR` at `R := authWTok ∗ X` (any `X`: the boot token's
  `plHook` rides along), `L _ := authOwn (.on γa) hs` lent to `RLock`, `Y rv` carries the view of `hs`'s last
  (`viewL`) so schema's `Φ` premise is a plain observation (`heldR_phiL`); `real_BER`; `real_reads3`: the three
  read-transaction clauses of `authBackendReads`); **(b) the lifecycle** (bac82a9720, `AuthRealLife.lean`:
  `pool_release_later`, `real_retire`/`real_release`/`real_publish`, `real_life` at `authOpenQ = qpRep q0 s0 authRdN`;
  no credits: `▷ realSt` destructured with `icases` (IntoExists under `▷` needs `Inhabited`: local instances for
  `GMap Nat (Option Qp)`, `BktData`), timeless leaves taken with `>`). lean-check clean (without `--fast`);
  targeted build: `/shared/tmp/auth-schema-srv/life-build1.log`.
- Next, in order: (c) the write side over F-acc: `authBatchTxLkR` (Lock/Unlock/the six writes/two reads/reader) from
  schema's `authBatchTx.*` specs (A5, generic in the backend transaction's triples) instantiated with the backend's
  `batchTxBuffered.{LockInsideApply,UnsafePut,UnsafeDelete,UnsafeRange,Unlock,Commit}` at the claimed parts
  (`rbPut … true` = `rbPutR`; `Unlock.spec` at `Sc = authBktL`, `Rr`/`rbAcc` opening `realInv` around
  `E = ⊤ ∖ ↑authRealN`, moving each bucket's `rbRd ½`/`authStateAt` to the `Unlock`'s `st`); the Unlock precondition's
  `thinV … ∗ W ∗ Pk ∗ Q` side (see how `Unlock.spec_free`/`Unlock.bare` (UnlockBare.lean) and the mvcc session
  realization `NewStoreSessReal.lean` discharge it: `thinV_refl`, `viewSame_noPuts`); `GetAllRoles` (a batch);
  `ForceCommit`; then `authWBackendOkR` at `authWTok γc` (authWAtHook) and at the boot token; (d) `authBkLend`
  (`1 ≤ st.revision`; agreement law `rbOwnInR` vs `rbOwn`), `CreateAuthBuckets`; (e) creation (claim, tickets,
  pools, `γc`, `realInv` allocation) and `⊢ authSchemaSrv`, `authSchemaSnap`. A7 HARD STOP for the user (trusted
  texts: fix (A), L-rev, P2, `rbPartF`, `newPostK`, `authRdSlots`, the ticket count).
- Pitfalls: (0)-(26) as before; (27) section `variable [schema_sem …]` is included in every theorem of the section
  (instance-implicit): a file using `AuthRealRsv`'s lemmas needs the schema `Assumptions` variable too; (28) `>⟨`
  lexes as one token: write `> ⟨`, but `>` cannot open `▷ ∃` (not timeless): destructure `▷ ∃` plainly; (29)
  `rw [← lemma]` on a `Qp` sum rewrites every `1` in the goal: combine fractions in a separate lemma (`pub_join`);
  (30) `ihave #H := lemma $$ []` on a `⊢ □ ∀ …` lemma specializes the `∀`: drop the `$$ []`.

## History (START HERE of 2026-11-18, L-rev/P2 and the read side, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean fb68edfec8 merged (a03f3662f7, 198b95c198):
  pin 6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json` everywhere (`.lake/package-overrides.json` = that manifest).
- Done: A1-A5, A6.1a/b, (b), A6.2 C1-C5, fix (A), F-enc + F-acc, the pool; STOP 2 decided (questions.md "A6 STOP 2
  decided"): **L-rev** (`authBkLend` takes `1 ≤ st.revision`; consumer `srvAuthAtLog_rev_pos`, `kvAppliedM_rev`) and
  **P2** (`authSchemaSnap` takes `permKeysOk st`), ledger entry; pool forms (`pool_release` by `Rs`, `poolRel` keeps the
  empty map, `poolRel_rel`, `poolRel_noRcpt`): 3c6d5319cf, cce362ea70; full build green (`lrev-full4.log`, 21846 jobs).
- **Read side** (forms: questions.md "A6 read side"): later credits on schema's read contract; `AuthRealInv.lean`
  (the invariant `realSt`/`realInv`, the ticket pool's steps `real_acq`/`real_obs`/`real_rel`, the views
  `real_view`/`real_viewIdle`, `usersOutD_at`); `AuthRealRd.lean` (`real_BE`, `real_readTxOk`, `real_backendOk`).
  targeted build green: `/shared/tmp/auth-schema-srv/rd-build2.log` (32 leaves of the changes, 9992 jobs).
- Next, in order: (a) the reserved pool's reads (`authBackendReads`' `GetUser`/`GetRole`/`GetAllUsers` at `R := T`:
  a second `authBE_real`, steps like the ticket pool's on `γm'`/`γh'`, view = idle via `real_viewIdle`'s argument);
  (b) the life (`authBkLife`): retire/publish need no credit (touch timeless parts only: destructure `▷ realSt` with
  `>`); release needs a `pool_release_later` on `▷ poolSt` (Timeless `dep`/`Rs`/`sh`; the free slots' `rdTok` under
  `▷`) and `authOpenQ = qpRep q0 s0 authRdN`; (c) the write side over F-acc (`authWBackendOkR`, `authWAtHook`;
  `rbAcc` opens `realInv` around `E = ⊤ ∖ ↑authRealN`); (d) `authBkLend` (`1 ≤ st.revision`: an absent revision key
  reads 0; agreement law `rbOwnInR` vs `rbOwn`), `CreateAuthBuckets`; (e) creation (claim, tickets, pools, `γc`) and
  `⊢ authSchemaSrv`, `authSchemaSnap`. A7 HARD STOP for the user (trusted texts: fix (A), L-rev, P2, `rbPartF`,
  `newPostK`, `authRdSlots`, the ticket count).
- Pitfalls: (0)-(22) as before; (23) `wp_apply` leaves the post (`Φ v`), not a WP: `iapply wp_fupd` before a call
  whose continuation opens an invariant; `wp_apply (lc := n)` credits come from pure steps AFTER the call (none after
  a bare method call); (24) `lc_fupd_elim_later` needs `HasLC.hasLC` and explicit `(E := …) (P := …)`; (25)
  `obtain … := h` clears `h`: use `id h` to keep it; (26) `subst` on `su = sa` removes `sa`.

## A6 invariant, refined (2026-11-18, over "A6 realization design" below)

- As built (`AuthRealInv.lean`): the branch sits with the life (`realSt`): live ∗ (idle ∨ batch `T`), retired ∗ gone,
  released ∗ gone, gone = `authWTok ∗ batchTok`; the rest below holds.

- **Pool edits** (AuthRealPool, forms): `pool_release`'s hypothesis `∀ d a, dep d ∗ Rs (a+1) ∗ Z ⊢ False` (the
  reserved pool refutes by `Rs`, its `dep` is `True`); `poolRel` keeps `ghostMapAuth γm 1 ∅` (a reader's `Robs`
  after the release refutes its receipt).
- **Readers' family**: `ι := Option Qp`, `L (some q) := authCur γc q` (clauses 1-2; `authPubLb` stays with the
  reader), `L none := authWTok γc` (clause 3; `authHistHalf` stays with the reader); `dep := L`; `C o qo := ∃ k,
  ghostMapElem γm k (own 1) o ∗ ⌜qo = s0⌝`; `Y _ := ownToks γh 1`. Views post hoc after schema's `RLock` (unfold
  `heldR`, `rtHeldF_rbRd` per bucket). `Hs v := ∃ x D, Held x D ∗ authReader rt (Held x D) D ∗ ⌜viewAt v D⌝`.
- **Buckets** (always): `rbRd ½ c_n` ×3, `authStateAt j_n s_n` ×3, `authPubQ ¼ p`, pure: `authAt s_a c_a`
  (flag `= enabledOf`, `uint.nat revisionOf = revision`, `revWf`), `∃ dU, usersAt s_u c_u dU`, `∃ dR, rolesAt …`,
  `j_u, j_r ≤ j_a`, `p ≤ j_u, j_r`; branch **idle** `∃ hs, authLockQ hs ∗ rbOwnInR γB (· ∈ authBktL) rc ∗ batchTok
  ∗ ⌜last hs = s_a = s_u = s_r, j_n = hs.length - 1, bktOf rc n = c_n⌝` | **batch** `authWTok γc` (Lock deposits
  `T`; the writer's `Lk` holds `batchTok`, refuting idle/gone at `Unlock`) | **gone** `batchTok` (after retire).
- **Life**: live `authSucc ∗ authRetired ∗ pools ∗ bOpen q0` | retired `authWTok ∗ authPubTok ∗ pools ∗ bOpen q0`
  | released `authWTok ∗ authCur 1 ∗ authRetired ∗ poolRel`s. Pools: tickets `poolSt γm γh (ticketsIn γt K) L
  rdTok (bOpen s0) K` (`K = authRdN - 1`), reserved `poolSt γm' γh' (tokIn (authWTok γc)) (fun _ => True) rdTok
  (bOpen s0) 1`; `authOpenQ = qpRep q0 s0 authRdN` (`bOpen_rep`). Release's `Z := authCur 1 ∗ authWTok`.

## A6 realization design (2026-11-18; checked against the specs, no Lean yet)

One invariant per backend `γc` (namespace disjoint from `rbClaimN`, `curN`), holding:
- **Tickets**: `R := ownToks γt 1`, global names `γt` with the discarded authority `ownTokAuthDfrac γt discard
  (authRdN - 1)` (persistent, allocated once in `⊢ authSchemaSrv`, shared by `authSchemaSnap γa R`).
- **Ticket pool** (`authRdN - 1` slots of `authRdSlots`; each slot carries `sh := bOpen γB s0`, `s0` a fixed share of
  the realization's `authOpenQ`, `bOpen_rep`): free `rdTok ∗ sh`; acquiring (between `Racq` and `Robs`: `sh` lent to
  `readTx.RLock`) a deposit in a ghost map `m : GMap Nat (Option Qp)` (`some q`: `authCur γc q`, clauses 1-2;
  `none`: `authWTok γc`, clause 3; the persistent `authPubLb` and `authHistHalf` stay in the reader's `C`), receipt
  `C i qo := ghostMapElem γm k d ∗ …`; held (between `Robs` and `Rrel`) `R ∗ sh` with receipt `Y := ownToks γh 1`;
  counts `kf + kh + m.size = authRdN - 1` (`GMap.size`); `kf ≥ 1` at `Racq` by `toks_bound` (deposited tickets
  `kh + m.size` and the one in hand ≤ `authRdN - 1`). Deposits are needed: release must refute every acquiring
  loan (`authCur γc 1`, the retired `T`) to collect its `sh`; a receipt holding `authCur q` in the reader's hands
  is not visible to the release. (Fraction-scaled vaults were rejected: they need `Σ`-invariants over `Qp`.)
- **Reserved pool** (1 slot, `R := T = authWTok γc`, same moves, deposit `T` from `Racq` to `Rrel`):
  `authBackendReads`' `GetUser`/`GetRole`/`GetAllUsers` call schema's `authBackend.Get*` at `R := T`, `L i :=
  authOwn hs`. `T` in the invariant here = no batch (idle facts hold).
- **Life**: live | retired (holds `authWTok γc`; `authBkLife` clause 1 mints `authRetired γc`) | released (holds
  `authCur γc 1 ∗ authWTok γc`: refutes every `Racq`). Release (clause 2) refutes every acquiring entry and
  collects the `sh` of free and held slots: `bOpen authOpenQ` back; held readers' `Rrel` still works after it.
- **Buckets** (no lent state, F-acc): `rbRd γB n ½ c_n` for `auth`, `authUsers`, `authRoles`; states `s_n` recorded
  at `j_n` (`authStateAt`), `c_a` encodes `s_a`'s flag and revision (`enabledOf`/`revisionOf`, `revWf`: also the boot
  buckets, where `authBucketsAre` fails), `c_u` `∃ dU, usersAt s_u c_u dU`, `c_r` likewise; `j_u, j_r ≤ j_a`; the
  realization's quarter `authPubQ γa ¼ p` with `p ≤ j_u, j_r`. Idle branch (T with the client or in the reserved
  pool): `authLockI (.on γa) st` and every `s_n = st` at its index. Batch branch: `T` deposited by `Lock`.
  At each `rbAcc` window (write-back, commit) a bucket moves to the writer's contents, which encode the `Unlock`'s
  `st` (recorded, latest), or stays (`unlockOk`; no session puts and deletes in one bucket): `s_n := st` whenever
  `c_n` encodes `st` (an untouched bucket encodes `st` too: the step changed nothing it holds), so `j_a` is always the
  latest and `j_u, j_r ≤ j_a` holds; `p` moves only with `T` in hand (idle).
- **Views, post hoc**: after `RLock`, with the token's `rtHeld`, open the invariant: `rtHeldF_rbRd` gives `rvBkt = c_n`
  (the read lock stops the write-back): the view `⟨s_a, s_u, s_r⟩` with `authViewSnapFrom` (`p ≥ i` from
  `authPubLb i`), or with `T ∗ authHistHalf hs` in hand the idle branch: `uni st`, `hs` last `st`.

## History

### A6 STOP 2 (2026-11-18, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean 49bd7924e6 merged: pin 6d365ee1a,
  `--packages=/shared/tmp/manifest-6d3.json` everywhere (`.lake/package-overrides.json` = that manifest). lean will
  move (origin's big merge): merge it before the next full build.
- Done: A1-A5, A6.1a/b, (b), A6.2 C1-C5, fix (A), F-enc + F-acc (c35919e62f), the pool (ebb39ec414, 5e577037ab);
  decided by etcd-grove-03 (questions.md "F-enc/F-acc as committed…"): F-enc/F-acc, their two forms, and the
  deposit design ACCEPTED. Rebuild of backend `Link` + server `Results` + `AuthRealPool`:
  `/shared/tmp/auth-schema-srv/fenc-build4.log` (see the STOP report for its outcome).
- **STOP (questions.md "A6 STOP 2")**: F-lend, a fourth refutation of `authSchemaSrv` (the lend before the revision
  is written; `notes/auth-schema-srv-refuted.md`), recommended (L-rev) `⌜1 ≤ st.revision⌝` in `authBkLend`; F-perm,
  `authSchemaSnap` cannot record the snapshot's state (`authStateAt` needs `permKeysOk`), recommended (P2)
  `⌜permKeysOk st⌝` in `authSchemaSnap`. Both trusted text (weaker hypotheses). No A6-proper Lean yet.
- Next, after the decision, in order: (0) the pool edits below; (1) `AuthRealInv.lean`: the per-backend invariant
  (refined design below) and its creation lemma (premise `permKeysOk st`); (2) the read side; (3) the write side
  over F-acc; (4) `authBkLend` (premise `1 ≤ st.revision`; agreement law `rbOwnInR` vs `rbOwn`), `authBkLife`,
  `authWAtHook`, `CreateAuthBuckets`; (5) `⊢ authSchemaSrv`, `authSchemaSnap`. Report at A6's end; A7 HARD STOP.
- Pitfalls: (0)-(21) as before (History); (22) `authLockQ` carries no `permKeysOk`: record a state from the reader's
  `authHistHalf` (`authHistHalf_stateAt`) or from the invariant's own witnesses, never from the lock's quarter.

### A6 F-enc/F-acc done (2026-11-18, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean 49bd7924e6 merged (2e7984f8a5): pin
  6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json` everywhere (`.lake/package-overrides.json` = that manifest).
- Done: A1-A5, A6.1a/b, (b), A6.2 C1-C5, fix (A) (all ACCEPTED; questions.md "A6 design findings decided").
  **F-enc** and **F-acc** (c35919e62f): schema's reads return the record the caller names (`usersDec`/`rolesDec`,
  `usersAt`/`rolesAt`, `authBucketsAre_usersAt`/`_rolesAt` by choice; no injectivity); `rbAcc … E` atomic around
  `E ⊇ ↑rbClaimN` in `Unlock`/`commit`/`unsafeCommit` (docstring: the window vs the four forbidden laws). The 42
  changed modules + `AuthRealRead` built (`/shared/tmp/auth-schema-srv/fenc-build2.log`); backend `Link` + server
  `Results`: `/shared/tmp/auth-schema-srv/fenc-build3.log`.
- **Pool** (ebb39ec414, 5e577037ab): `etcdserver/AuthRealPool.lean` (lean-check clean, not yet in a lake build):
  the generic slot pool (`poolSt`, `pool_alloc`/`_acq`/`_obs`/`_rel`/`_release`, `poolRel`) and its counters
  (`ticketsIn` with `ticketsIn_dep`/`_wd`; `tokIn` for the reserved slot).
- Next, in order: (1) the rest of the per-backend invariant (design below): the bucket/history part
  (`viewAt v D`: per-bucket predicates from `usersAt`/`rolesAt` and the `auth` bucket's flag/revision, `viewAt →
  authWf`), the life part, one `inv` per backend holding both pools; (2) the read side: `authTxReadsV` of
  `Hs v := ∃ x D, Held x D ∗ authReader … ∗ ⌜viewAt v D⌝` from schema's `authReadTx.*` specs (+ F-enc's
  `userOutD_are`; `GetAllUsers`' names `es.map fst`), `authBackendOk` from `authBE_real` (ticket pool) + post-hoc
  view facts; `authBackendReads`' reads from a second `authBE_real` (reserved pool, `R := T`); (3) the write side
  over F-acc; (4) `authBkLend`, `authBkLife`, `authWAtHook`, `CreateAuthBuckets`; (5) `⊢ authSchemaSrv`,
  `authSchemaSnap`. Report at A6's end; A7 HARD STOP (trusted texts: `rbPartF`'s fraction, `newPostK`'s tokens,
  `authRdSlots`' tokens, `authSchemaSrv`'s ticket count, fix (A)).
- Pitfalls: (0)-(18) as before (History); (19) `rbAcc_nil γ ok Rr E` now takes the mask; callers at `⊤` pass
  `⊤ CoPset.subseteq_top` to the specs; (20) a lemma stated with a bare `|==>` goal fails `imod`/`imodintro` ("is
  not a modality"): state ghost steps at `|={E}=>` (AuthRealPool does); (21) an Iris hypothesis cannot be the
  target of `rw … at`: rewrite the goal (the context is part of it).


### F-enc/F-acc decision (2026-11-18, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean b0bb9df7c3 merged (75f8363b83; lean had
  not moved on 2026-11-18): pin 6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json` everywhere
  (`.lake/package-overrides.json` = that manifest). Merge lean before the next full build.
- Done: A1-A5, A6.1a/b, (b), A6.2 C1-C5 (ACCEPTED); **fix (A)** (936035ac75, decided by etcd-grove-03, questions.md
  "A6 STOP decided"): `authSchemaSrv`'s boot write contract and `CreateAuthBuckets` at `T_b := authWTok γc ∗ plHook
  d.γB func.nil` (handed out as the token), C9 `Post -∗ bOpen qo`; the server splits the returned token
  (AuthSrv.lean); `authApplyResPre` (StoreLatest.lean) names the schema auth backend (`ablOn`) in place of the boot
  contract, `authApplyResB_of_pre` takes the contract at the frozen hook. Ledger, refuted note (third refutation),
  soundness §6 restated (A6 creates claimed buckets; `Unlock.spec`'s `Sc` is any superset of `cw`: parts come back).
  Targeted build (server Results + auth/auth3/authN Results): `/shared/tmp/auth-schema-srv/a6-fixA-build.log`.
- **Open (questions.md "A6 design findings")**: F-acc (`rbAcc` must be mask-changing, `|={⊤,E}=>` … `|={E,⊤}=>`,
  so the realization's invariant has no lent state; backend `ClaimedLemmas`/`Unlock`/`UnlockBare`) and F-enc
  (schema's user/role reads must return the caller's named record: `userEncode` is opaque and not injective, so
  `userOutD_are`'s `hinj` cannot be discharged). Both internal, recommended as forms. No A6-proper Lean yet.
- Next, after the decision: F-enc (A5's read specs, ~10 files), then the read side: (1) the per-backend
  realization invariant (questions.md "A6 STOP", "Unaffected"; no lent state given F-acc), (2) `authBackendOk` from
  `authBE_real` + `authTxReadsV` from schema's `authReadTx.*` specs (a per-bucket `authBucketsAre`), then F-acc and
  the write side (3), `authBkLend`/`authBkLife`/`authWAtHook`/`CreateAuthBuckets` (4), `⊢ authSchemaSrv` and
  `authSchemaSnap` (5). Report at A6's end; A7 HARD STOP (trusted texts: `rbPartF`'s fraction, `newPostK`'s tokens,
  `authRdSlots`' tokens, `authSchemaSrv`'s ticket count, fix (A)).
- Pitfalls: (0)-(16) as before (History); (17) resolved (soundness §6); (18) a term argument of type `IProp` with
  `∗` inside a definition needs `iprop(…)` (the elaborator error "`term_∗_` has not been implemented").


### A6 STOP (2026-11-18, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean b0bb9df7c3 merged (75f8363b83): Perennial pin
  6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json` everywhere (`.lake/package-overrides.json` = that manifest).
  lean is moving (Hctx Part B, origin's zap.Logger.Panic fix): merge lean before the next full build.
- Done: A1-A5, A6.1a/b, (b), A6.2 C1-C5 (all ACCEPTED; C5 gates green, tcb 896/4; questions.md "C5 gates reviewed").
- **STOP (questions.md "A6 STOP")**: `authSchemaSrv`'s boot write contract (C3 at the unset hook, persistent) cannot be
  realized: schema's `Lock` is `LockInsideApply`, which needs `plHookAt … f`; the realization must hand `plHook nil`
  back whole through C9's plain wand, after which the server sets the hook. Recommended (A): the boot contract and
  `CreateAuthBuckets` at `T_b := authWTok γc ∗ plHook d.γB func.nil`, C9's wand `Post -∗ bOpen qo`; the server splits
  the returned `T` (AuthSrv.lean ~497-570). Trusted text (hypothesis) for the A7 report. No Lean written for A6 yet.
- Next, after the decision: apply (A) (or the decision); then A6 proper in this order: (1) the per-backend realization
  invariant (design in questions.md "A6 STOP", "Unaffected"): tickets `R` (global `ownToks` + authority `authRdN - 1`),
  per-backend slots (free/acquiring/held) with the `bOpen` loans, the claimed `rbRd` halves with recorded indices
  (`j_u, j_r ≤ j_a`, `≥` published), `T`/idle branch with `authLockQ`, retired/released; (2) `authBackendOk` from
  `authBE_real` (+ a second `authBE` at `R := True` for `authBackendReads`' `T`-reads, the reserved slot); (3) the write
  side (`Lk`, claimed writes, `Unlock`'s accessor `rbAcc`, receipts); (4) `authBkLend` (new internal backend agreement
  law `rbOwn` vs claimed part, through the claim invariant), `authBkLife`, `authWAtHook`, `CreateAuthBuckets` (claimed
  creates, `Sc = authBkts` at `Unlock`); (5) `⊢ authSchemaSrv`, `authSchemaSnap` from one per-backend lemma. Report at
  A6's end; A7 HARD STOP (trusted texts: `rbPartF`'s fraction, `newPostK`'s tokens, `authRdSlots`' tokens,
  `authSchemaSrv`'s ticket count, and (A) if applied).
- Pitfalls: (0)-(13) as before (History "A6.1b STOP" and "A6.2 C1-C5"); (14) an `icases` pattern's last name absorbs
  the rest of a `∗` chain: name every conjunct (`…, Hsr, -⟩`); (15) only one agent per worktree; (16) questions.md is
  untracked (gitignored): decisions live there, not in commits; (17) soundness §6's "A6 creates no claimed bucket" is
  stale (the claim precedes `CreateAuthBuckets`): restate when A6 lands.


### A6.2 C1-C5 green, C5 gates (2026-11-18, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; lean b0bb9df7c3 merged (75f8363b83): Perennial pin
  6d365ee1a, `--packages=/shared/tmp/manifest-6d3.json` everywhere (`.lake/package-overrides.json` = that manifest).
- Done: A1-A5, A6.1a/b, (b), A6.2 C1-C5 (9c3a07c198, 448f9578a0, a9fe8620fc; build green 3a94a88689: mvccfull
  `Writer` drops `newPostK`'s tokens). Delta review SOUND, deviations ACCEPTED (questions.md "A6.2 C1-C5"; review
  `/shared/tmp/auth-schema-srv/a6-claim-review3.md`); MINOR 1 folded: forbidden law (iv) in `bStopView`/`rbOwnInR`
  docstrings and soundness §6.
- C5 gates green: full build on pin 6d365ee1a (`/shared/tmp/auth-schema-srv/c5-full2.log`, 20543 jobs);
  `etc/tcb-report.py --check` matches the baseline (896 axioms, 4 sorries: no change); backend/bbolt interfaces
  regenerated and `--check` clean; api-check 0 errors after making A2's `Bucket__ForEach_kvr/_kvw` and A6.1a's
  `readTx__UnsafeForEach` importable (165634bbd4); backend `--layout` baseline +4 for `readTx__UnsafeForEach`
  (8443232b3a, the same pattern as its `readTx` siblings).
- Next: A6 proper (decided by etcd-grove-03): the per-backend realization invariant using `rbOwnIn_claim` (sketch:
  History "A6.1b STOP"), instantiating `authBE_real`'s `Racq`/`Robs`/`Rrel`; the write side from A5's callee triples
  (claimed `rbOwnInR`/`rbRd`, `Unlock.spec`'s accessor at ⊤); the auth-level read contract (`authBackendOk`); then
  `authWBackendOkR`, `authWAtHook`, `authBkLend`, `CreateAuthBuckets`, `authBkLife`, tickets, `authSchemaSnap`;
  report at A6's end. A7 HARD STOP (trusted texts: `rbPartF`'s fraction, `newPostK`'s tokens, `authRdSlots`' tokens,
  `authSchemaSrv`'s ticket count).
- Pitfalls: (0)-(13) as before (History "A6.1b STOP" and the A6.2 START HERE below); (14) an `icases` pattern's last
  name absorbs the rest of a `∗` chain: name every conjunct (`…, Hsr, -⟩`); (15) only one agent per worktree (a resumed
  older agent edited here concurrently on 2026-11-18).


### A6.2 C1-C5 written (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; pin c6b39d4f8: `--packages=/shared/tmp/manifest-c6b.json`
  everywhere (`.lake/package-overrides.json` = that manifest). lean merged at f256fa496e (04b1fa5134).
- Decisions: questions.md "A6.2 second review" (GO for C1, MINORs folded) and "A6.2 C1-C5" (forms: invariant in the token,
  not `isBackend`; M1 by a clear claimed `γ.rbk` flag + `tkI := idle ∨ cw`; `newPostKP` unchanged, tokens beside it).
- Done (commits 9d…→a9fe8620fc): `InvBackend` (`rbClaimU/C/One/Inv`, `rbClaimN`, `rbClaimToks`, `rbPartF` ¼, `rbRd` q/2,
  uniform `rbrOne` ¼, `rbrSide` without `rbc`, `rbSide` holds the inv); `TrackedLemmas` (writes/flag clears over the inv,
  helpers); `ClaimedLemmas` (`rbOwnIn_claim` lock-free, token laws, stepR, `rbPartR_idle`); `NewAlloc` allocation;
  `newPostK` + `newPostK_pool`; `authRdSlots := rdAuth ∗ rbClaimToks authBkts`; boot (`BootBackend`, `boot_storage(R)`,
  NewServer(R)) and snapshot (`SnapApplyWalk`) threading; soundness note §6; forbidden laws in `bStopView`/`rbOwnInR`.
- Checked: lean-check of InvBackend, TrackedLemmas, ClaimedLemmas, InvBatch, NewAlloc, Unlock, RdPool, UnsafePut,
  unsafeCommit, newBackend, InvCommit: 0 errors. Targeted build (backend/etcdserver/mvccrand/mvccfull Links):
  `/shared/tmp/auth-schema-srv/c1-build2.log`.
- Next: fix the build's errors; C5 (`etc/gen-interface.py etc/api/backend.txt`, api-check, tcb `--check`: no axiom/sorry
  change expected); then A6 proper (realization invariant using `rbOwnIn_claim` in the update, write side, auth read
  contract); A7 HARD STOP (old → new statements: `authRdSlots`, `newPostK`, `rbPartF` fraction, `authSchemaSrv` tickets).
- Pitfalls: (0)-(10) of History "A6.1b STOP"; (11) `if` instances: `rbEls`/`rbClaimToks` use `Classical.propDecidable`;
  state helpers with a generic `S` (see `mapIf_one`) or `dsimp only` + explicit `@ite`; (12) after `cases hcl : Cl n`
  apply `rbClaimOne_U/C γ n _ rfl`, not `… (Cl n) hcl`; (13) build slots can be busy for >30 min.


### A6.2 Scope STOP (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A6, A7); decisions `questions.md` (untracked; "A6.2 decided").
- Done: A1-A5, A6.1a, the Held index, A6.1b, the lent family (History); (b) (8acf5658a9, ACCEPTED: `authSchemaSrv`'s
  tickets `authRdN` → `authRdN - 1`, for the A7 report; `authSchemaSnap` unchanged).
- **A6.2 Scope (this commit): `notes/auth-schema-srv-a6-claim-scope.md`**: a lock-free claim law `rbOwnIn_claim`
  (`isBackend ∗ rbOwnIn ={⊤}=∗ rbOwnInR ∗ rbRd ½`) over a new sealed invariant `rbClaimInv` in `isBackend` holding
  per tracked bucket shares of `rbk` (½), `rbr` (¼), `rbc` (whole, with its authority) and the link `f = false → v =
  bktOf c`; `rbPartF` (so `rbPart`/`rbOwnIn`/`rbOwn` and the lock's `rbSide`) scaled ½ → ¼ uniformly (Snapshot's
  observation hands the lock's share as an `rbOwn`); `rbRd q` = element `q/2`. 1000-2100 lines, backend only.
- Review (`/shared/tmp/auth-schema-srv/a6-claim-review.md`): B1 (second claim not refutable; `Close` hands the lock's
  share out) → §R.1 the per-bucket claim token (in `newPostK`, carried with `authRdSlots`); M1 → §R.2 the claimed
  flag cleared at `Unlock`'s end with the claim marker's; MINOR 1 already restated (§R.3).
- **STOP**: a short second review before any Lean (decided by etcd-grove-03).
- Next, after the review: C1-C5 of the Scope §5 (probe `wb_core`/`unsafeCommit` first), then A6 as planned
  (realization invariant, write side, auth-level read contract), then A7 HARD STOP.
- Pitfalls: as in History "A6.1b STOP" (0)-(10).


### A6.2 STOP (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A6, A7); decisions `questions.md` (untracked; "A6.1b decided", "A6.2 STOP").
- Done: A1-A5, A6.1a, the Held index, A6.1b and the lent family (History; ACCEPTED). **(b)** (this commit):
  `authSchemaSrv` hands out `authRdN - 1` tickets (AuthSrv.lean; ledger "the auth realization's premise hands out one
  reader ticket fewer"); supply checked, no consumer short. Server `Link.lean` regenerated: unchanged (it already
  names A5/A6.1 proofs); built (`/shared/tmp/auth-schema-srv/a6-link1.log`).
- **STOP (blocker, questions.md "A6.2 STOP"):** readers before the realization's first claim. The realization's
  update returns `authBackendOk` (readers usable at once: `authCur γc 1`, `T`, the tickets all handed out), but a
  reader can only learn what it reads in a claimed bucket (`rtHeldF_rbRd`); the claim (`batchLocked_claim`) needs
  the batch lock, which a ghost update does not have; the idle unclaimed part (`rbOwnIn`) has no readers' law (A1
  decision 1 (a)). Same on every snapshot backend (`Recover`'s `T`-read comes before any batch `Lock`).
- Next, after the decision: the per-backend realization invariant (sketch in History, "A6.1b STOP"), the write side,
  the auth-level read contract; then A7 HARD STOP.
- Pitfalls: as in History "A6.1b STOP" (0)-(10).


### A6.1b STOP (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A6, A7); decisions `questions.md` (untracked; "A6.1a decided", "A6.1b").
- Done: A1-A5 (History); A6.1a (b3ea959bf1, ACCEPTED); **the Held index** (952283bbfb, APPROVED): `Held : Loc →
  AuthData → IProp`, `GetUser`/`GetRole` take the caller's `Φ` as `GetAllUsers` (the stronger posts, done);
  **A6.1b** (a5cb6ded57) in `etcdserver/AuthRealRead.lean`: `heldR γ P b Y x D` (the token), `heldR_rdCap`
  (`rdB` → `rdCap`, a quarter of bbolt's tx lent), `heldR_point` ×3, `heldR_forEach`, `heldR_reader`,
  `authBE_real` (generic over the caller's ghost steps `Racq`/`Robs`/`Rrel`), `auth_isBucket` ×3; **the lent family**
  (this commit): `authRTx rt R L Held`/`authBE bi R L Held`, `L : ι → IProp` lent to `RLock` and given back (the
  realization borrows its open share against the caller's `authCur γc q`, or `T`); schema's six read specs take `L i`.
  Targeted build of the 7 modules green (`/shared/tmp/auth-schema-srv/held-build5.log`).
- **STOP (finding, questions.md "A6.1b"):** `authBackendReads`' read-transaction clauses (`GetUser`, `GetRole`,
  `GetAllUsers`: `{{T ∗ authOwn M hs}}`) take no reader ticket; schema's code runs `ReadTx().RLock()`, which needs
  an `rdTok`; the realization's only slots (`authRdSlots` = `authRdN` `rdTok`s) all back the premise's `authRdN`
  tickets `R`, any of which may be in use: the realization cannot supply the slot. Options (a)/(b) in questions.md.
- Next, after the decision: (1) the realization invariant per backend `γc` (design: questions.md "A6.1b", the
  sketch below); (2) the write side from A5's callee triples (claimed parts `rbOwnInR`/`rbRd`, `Unlock.spec`'s
  accessor at mask ⊤, receipts bound writes < receiptBound ≤ 2^48); (3) the auth-level read contract from schema's
  specs + post-processing (rtHeldF_rbRd at any time while held); then A7 HARD STOP.
- Realization sketch: `inv` per `γc` holding: `rbRd γB n ½ m_n` for the three auth buckets with each `m_n` the
  encoding of a recorded state (`authBucketsAre`-per-bucket), its index ≥ the published index (the realization's
  `authPubQ` quarter); `authWTok γc` when a batch is open (else the idle facts: every bucket = `authLockI`'s state);
  the `bOpen authOpenQ` vault, lent per `RLock` against `authCur γc q` (release needs `authCur 1`: none lent) or
  against `T`; the tickets ↔ `rdTok` exchange; the lifecycle (retired/released flags).
- Pitfalls: (0)-(7) as before (History, A5). (8) a spec binder `{ι : Type}` IS named by `intro` (`intro … Held ι L i`)
  but must NOT be passed explicitly when applying the spec (`hRT abe bi lg R Held L`). (9) the triple inside
  `authBE`'s `□ (…)`: `iintro !> %Φ !> - HΦ` (two `!>`); inside `authRTx`'s `□ (∀ i, …)`: `iintro !> %i !> %Ψ …`.
  (10) `wp_apply` of an Iris-hypothesis triple can fail silently into `sorry` under `--fast`: use
  `iapply H $$ %args %Ψ [pre] [post]`, then `inext`.


### A6.1a STOP (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A6, A7); decisions `questions.md` (untracked; "A5 done", "A6.1a").
- Done: A1-A4 (History); A5 (5cc3a07e4b, ACCEPTED by etcd-grove-03: callee triples, `authForEachSpec`, `GetAllUsers`'
  `Φ`); **A6.1a (this commit)**: `backend.readTx.UnsafeForEach` (the promotion wrapper, spec + proof, linked in the
  backend's `Link`); `etcdserver/AuthRealRead.lean`: `rtForEach_perm` (a read transaction's walk is a permutation of
  `bktEnts (rvBkt P rv bi.name)`: table bucket, `rv.2.Wf`), `rtForEach_mem`, `sorted_mem_iff`, `rvAuth P rv` (the
  auth buckets a reader at `rv` reads). Targeted build: `/shared/tmp/auth-schema-srv/a6-build1.log`.
- **Finding (internal contract, form to apply next, questions.md "A6.1a")**: `schema.authRTx rt R Held` with `Held :
  AuthData → IProp` is NOT realizable by the real `readTx`: `authReader rt (Held D) D` promises persistently that a
  returned slice is readable under any `Held D` (`rdCap`/`pointValsA`), but a slice is bbolt's transaction's bytes
  (`rdB rtx`), valid only in its own read session, and `Held D` does not determine the session (two sessions can read
  the same `D`). Fix: index the token by the session's bbolt transaction, `Held : Loc → AuthData → IProp` (`RLock`'s
  post `∃ x D`, `RUnlock` `∀ x D`, `GetAllUsers`' `Φ` premise `∀ x D`); 12 files (`InvAuthBackend` and the six
  `authBackend.{ReadTx,GetUser,GetRole,GetAllUsers}`/`authReadTx.{RLock,RUnlock}` specs and proofs), mechanical.
- Next, in order: (1) the `Held` index above; (2) A6.1b in `AuthRealRead.lean`: `rdCap` from `rdB` under `Held x D :=
  ∃ rv, ⌜rvAuth P rv = D ∧ rv.2.Wf⌝ ∗ rtHeld γ P b x rv ∗ Y rv` (`rtHeldF_lend'` at `rfrac.half = ½·½ + ½·½`,
  `rdB_acc`, `rtHeldF_return`); `authPointSpec` ×3 (`readTx.UnsafeRange` at `rtHeld_eq`, `rtRange_single`,
  `kvsOutRd_single`/`_nil`; auth `isBucket` lemmas from `schemaInit` as `mvcc.meta_isBucket`, conjuncts 10-12);
  `authForEachSpec` (backend `I i := Ic (take i es)`, `E := False`, `List.take_succ`, `rtForEach_perm`); `authBE_real`
  generic in the caller's ghost steps (`R ={⊤}=∗ rdTok ∗ bOpen qo ∗ C`; after `readTx.RLock` an observation
  `rtHeld ∗ bOpen qo ∗ C ={⊤}=∗ rtHeld ∗ Y rv ∗ ⌜authWf (rvAuth P rv)⌝`; `RUnlock`: `rdTok ∗ Y rv ={⊤}=∗ R`);
  (3) the realization invariant per backend `γc` (claimed `rbRd` halves of the three buckets with their recorded
  states, `authLockI`, the `bOpen authOpenQ` vault with deposits of `authCur`, the tickets ↔ `rdTok` exchange, the
  lifecycle), the write side from A5's callee triples, `GetUser`/`GetRole` stronger posts in place; then A7 HARD STOP.
- Pitfalls: (0)-(6) of A5 (History) still apply. (7) `backend.bktEnts_sorted` and other backend lemmas sit in sections
  with `hG`/`package_sem` instance variables: a client file needs the same `variable` block to use them.



### A5 done (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked; "A5 done").
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 (72c59c8aff, f546a2dbb9); A3 (7a843bfc54); A4 (846a7fedd9, ACCEPTED).
- **A5 (5cc3a07e4b, this commit; lean merged 22235f7e13)**: full build green (`/shared/tmp/auth-schema-srv/a5-build1.log`); tcb +2 (MarshalUser/Role; baseline 900, server collection; auth collections unchanged); bounds 391 = baseline; axiom-tok ok. schema's write side and walks, 22 functions specified and proved
  (`Spec|Proof/go_etcd_io/etcd/server/v3/storage/schema/{authBatchTx__*,authBackend__{BatchTx,ForceCommit,
  CreateAuthBuckets,GetAllUsers,GetAllRoles},authReadTx__UnsafeGetAllUsers,unsafeGetAll{Users,Roles}}.lean`), over
  callee triples of the backend transaction (A6 instantiates them); `InvAuthBackend`: `rdCap`, `authForEachSpec`
  (in `authReader`), `authRolesRange`/`rolesRangeEnts`, `usersOutD`/`rolesOutD`, `abtF`; linked in the server's
  `Link` (MarshalUser/MarshalRole now reached).
- Next: A6, the realization (`⊢ authSchemaSrv`, `authSchemaSnap` from one per-backend lemma): derive `authBE`/
  `authRTx`/`authReader` for the real backend (readTx per bucket, `rbOwnInR`/claimed parts), instantiate A5's callee
  triples from `batchTxBuffered.*` with the claimed parts (`rbPutR`), `Unlock.spec`'s accessor, the receipts
  (`receipt_add_one_lt`: writes < receiptBound ≤ 2^48), strengthen `GetUser`/`GetRole` with the `Φ` premise as
  `GetAllUsers` (questions.md "A5 done"); then A7 HARD STOP.
- Pitfalls: (0) a hypothesis holding a triple on an abstract interface (`methods t.ty m t.v`) breaks `wp_start`'s
  `rw [method_unfold]` (it unifies with that occurrence: "MethodUnfold t.ty"): `wp_start_folded as …`, then
  `rw [MethodUnfold.method_unfold (t := go.GoType.PointerType <T>.ty) (m := go!"M")]`, `wp_call`; in a visitor
  subgoal `iclear` such a hypothesis first. (1) `wp_if_destruct`/`wp_apply` run `wp_auto`, which drops a resolution's
  receipt: `wp_apply +noauto`. (2) `imod` of a `|==>` only while the goal is a WP (not after the last step of a loop
  body: before `wp_store`). (3) `generalize … at *` once gave a kernel error with `word`: use `obtain ⟨es, hes⟩ : ∃
  es, … = es := ⟨_, rfl⟩; rw [hes]`. (4) a hand-written `if m = n` picks `instDecidableEqString`: write
  `@ite _ (m = n) (Classical.propDecidable _) …`. (5) keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq,
  batteries, iris. (6) lean-check of a server file rebuilds its imports outside a slot: prefer the slot build.

### A4 done (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked; read "A4 STOP").
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 (72c59c8aff, f546a2dbb9); A3 (7a843bfc54, forms ACCEPTED by etcd-grove-03).
- **A4 (this commit)**: Route R (approved by etcd-grove-03): the six writes of `authBatchTxLk(R)` take `⧗ 1`; the
  store's proofs take it with `wp_take_receipt` (questions.md "A4 done"); axiom-tok entries for A2's ForEach axioms.
  Full build ok (`/shared/tmp/auth-schema-srv/a4-build1.log`); tcb --check matches (894/4); axiom-tok ok; bounds 391 =
  baseline; no interface changed.
- Next: A5 (schema's write side: `authBatchTx.*` over the backend's claimed parts `rbPutR`/kinds and `Unlock`'s
  accessor, `authBackend.{BatchTx,ForceCommit,CreateAuthBuckets,GetAllUsers,GetAllRoles}`, `unsafeGetAll*`,
  `authReadTx.UnsafeGetAllUsers`; A1 scope §9), then A6 (the realization: bounds a session's writes by the `⧗` it
  holds, `receipt_add_one_lt`); A7 HARD STOP.
- Pitfalls: (0) `wp_if_destruct`/`wp_apply` run `wp_auto`, which drops a resolution's receipt: `wp_apply +noauto`,
  or take the receipt at an earlier resolution. (1) `wp_join` cases end at the bare `R` (no update): to allocate an invariant in a case, make `R` an
  update `iprop(|={⊤}=> …)` and `imod` it in the continuation (`authStore__UserAdd*.lean`). (2) after `iunfold
  ownPermS`, name the field cells `#PermType, #Key, #RangeEnd`. (3) `BigSepL2.bigSepL_fupd E` is the list fupd lemma.
  (4) a hand-written `if m = n` picks `instDecidableEqString`: write `@ite _ (m = n) (Classical.propDecidable _) …`.
  (5) keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6) `etc/gen-interface.py
  --layout` builds every package module: build first. (7) lean-check of a server file rebuilds its imports outside a
  slot (EtcdServer__UserAdd: 450 s): prefer the slot build for many importers.


### A4 STOP (2026-11-17, superseded)


- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked; read "A4 STOP").
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 (72c59c8aff, f546a2dbb9); A3 (7a843bfc54, forms ACCEPTED by etcd-grove-03).
- A4: no Lean yet. The users-count route needs the fuel's base `b ≤ 2^61` (Fuel.lean `fuelOk`) tightened to
  `b ≤ 2^55`; b is the installed image's log length, bounded by raft's `readyFits` (`receiptBound + bootLen ≤ 2^61`)
  through the snapshot path, so tightening changes exported statements (raft `readyFits_intro`, `etcdstart.Alloc*`'s
  `Hrb2`, ...): STOPPED, questions.md "A4 STOP" has the chain. Alternative R (recommended): every write of the
  `authBatchTxLk(R)` contract costs `⧗ 1` (the store takes one at a Go step per loop iteration,
  `wp_go_step_receipt'`); the realization bounds a session's writes by the receipts it holds
  (`receipt_add_one_lt`: < receiptBound ≤ 2^48), so `pend0 + writes + hookMax < 2^57 + 2^48 + 2^16 < 2^58`.
- Next: the coordinator's choice (R, or the tightening with its exported changes); then A4, A5, A6; A7 HARD STOP.
- Pitfalls: (1) `wp_join` cases end at the bare `R` (no update): to allocate an invariant in a case, make `R` an
  update `iprop(|={⊤}=> …)` and `imod` it in the continuation (`authStore__UserAdd*.lean`). (2) after `iunfold
  ownPermS`, name the field cells `#PermType, #Key, #RangeEnd`. (3) `BigSepL2.bigSepL_fupd E` is the list fupd lemma.
  (4) a hand-written `if m = n` picks `instDecidableEqString`: write `@ite _ (m = n) (Classical.propDecidable _) …`.
  (5) keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6) `etc/gen-interface.py
  --layout` builds every package module: build first. (7) lean-check of a server file rebuilds its imports outside a
  slot (EtcdServer__UserAdd: 450 s): prefer the slot build for many importers.

### A3 done (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked).
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 (72c59c8aff, f546a2dbb9); **A3 (this commit)**: Draft
  `notes/auth-schema-srv-a3-draft.md` applied with the attack's MINORs (`notes/axiom-review/auth-a3-marshal.md`):
  `Buckets.lean` (`pbSizeCacheN`, the three predicates per field, `permSizeCache_alloc`, `ownPermS_freeze`,
  `ownPermW_freeze`, `userOptsIs_freeze`, persist lemmas → `|={E}=>`), axiom files `Proof/.../proto/Marshal{User,Role}.lean`,
  `MarshalIRR` docstring, callers (auth store, `EtcdServer.UserAdd`, schema `GetRole`, `InvAuthBackend`, client
  `PerTypeAuth`/`authClient.{UserAdd,RoleGrantPermission}`); ledger entry; full build green
  (`/shared/tmp/auth-schema-srv/a3-build1.log`); `tcb-report --check` matches unchanged (894: the two new axioms
  are reached by no root until A5); no interface changed.
- Next: A4, the put budget in `authBatchTxLk(R)` (Q6, decision 2). **Open point to settle first**: `RoleDelete` puts
  one user per holder of the role, the backend needs `pend + 1 < 2^58`, and `authSmall` bounds the users only through
  the revision (≤ k + b + 1, b ≤ 2^61): the budget needs a users-count bound below 2^58 (e.g. a users-count field in
  `authSmall`, ≤ revision, with a tighter base), or a budget not derived from the state. Then A5, A6; A7 HARD STOP.
- Pitfalls: (1) `wp_join` cases end at the bare `R` (no update): to allocate an invariant in a case, make `R` an
  update `iprop(|={⊤}=> …)` and `imod` it in the continuation (`authStore__UserAdd*.lean`). (2) the per-field
  predicates: after `iunfold ownPermS`, name the field cells `#PermType, #Key, #RangeEnd` (wp_load finds them).
  (3) `BigSepL2.bigSepL_fupd E` is the list fupd lemma (odd namespace). (4) a hand-written `if m = n` picks
  `instDecidableEqString`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (5) Stray Perennial clone: keep
  `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6) `etc/gen-interface.py --layout`
  builds every package module: build first. (7) lean-check of a server file rebuilds its imports outside a slot
  (EtcdServer__UserAdd: 450 s): prefer the slot build for many importers.

### A3 Draft written (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked).
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 (72c59c8aff, f546a2dbb9; forms ACCEPTED by etcd-grove-03, promotion
  wrappers and an `rtForEach`↔`rvBkt` law deferred to A5); **A3 Draft (this commit)**:
  `notes/auth-schema-srv-a3-draft.md` (exact texts §2, meaning moves §3, Go evidence §4, family check §5,
  findings §6, decisions §7); specs `Spec/google_golang_org/protobuf/proto/Marshal{User,Role}.lean` (NOT axioms:
  no `Proof/` file); restated predicates elaborated in `Scratch/A3Preds.lean` (untracked); Go tests
  `examples/authpbmarshal/marshal_test.go` (10, pass with `-race`, `GOTOOLCHAIN=go1.27.3`).
- Waiting on: an independent attack of §2 (axiom skill) and etcd-grove-03's decisions §7.
- Next after the go (A3 Freeze): §2.2 into `Buckets.lean` (+ `pbSizeCacheN`), constructors to `inv_alloc`
  (`PerTypeAuth`, `RoleGrantPermission`'s `newPerm`, `ownPermX_persist`/`ownRoleX_persist` → fupd), readers to
  per-field loads, axiom files, MarshalIRR docstring (§2.4), tcb +2 at A5, interfaces. Then A4, A5.
- Pitfalls: (1) a hand-written `if m = n` picks `instDecidableEqString`, the laws' `if S n` (open Classical)
  `Classical.propDecidable`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (2) `unfold` does not
  beta-reduce `(fun n => S n ∨ S' n) n`: `dsimp only`. (3) A theorem's default argument (`trkHalf_eq … I`) is
  filled with the default when omitted: pass it. (4) Macros: frame patterns as ``$(frameH `H)``. (5) Stray
  Perennial clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6)
  `etc/gen-interface.py --layout` builds every package module: build first. (7) simp normalizes
  `decide (a ∉ l)` to `!decide (a ∈ l)` inside Iris hyps. (8) Go tests: reading unexported fields with
  `reflect`+`unsafe` under `-race` needs `unsafe.Pointer(v.UnsafeAddr())` in one expression (checkptr).

### A2 done (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere (`.lake/package-overrides.json` = that manifest). Scope
  `notes/auth-schema-srv-scope.md` §3 (A2-A7); decisions `questions.md` (untracked); A2 Draft
  `notes/auth-schema-srv-a2-draft.md`.
- Done: A1 (52d85a42f6 … 6fe91f236f); A2 axioms (72c59c8aff, attacked: survive); lean 3cd4b72599 merged (1dbe00041f);
  **A2 backend side (this commit)**: `FeSide`/`feOwn` (InvBackend: the walked transaction, read or write),
  `rtForEach` (Model2: bbolt's entries whose keys the buffer lacks, then the buffer's); specs+proofs
  `unsafeForEach` (one spec, `sd : FeSide`), `batchTx.UnsafeForEach`, `baseReadTx.UnsafeForEach`; linked
  (`etc/link-lean-first-backend.txt`); full build ok (`/shared/tmp/auth-schema-srv/a2-build2.log`); tcb baseline
  +2 exactly (`bbolt.Bucket.ForEach_kvr.wp_proof`, `ForEach_kvw.wp_proof`); backend interfaces + layout baseline.
- Not done (on demand, A5): `readTx`/`concurrentReadTx`/`batchTxBuffered` reach `UnsafeForEach` by Go method
  promotion (no translated wrapper); a law `rtForEach` ~ `rvBkt` (each key once) when the realization needs it.
- Next: A3 — write its Draft (Marshal axioms of `authpb.User`/`Role` mirroring the Unmarshal ones, `sizeCache` out
  of `↦□`, precedent restart1/Requests.lean) and STOP at its new trusted texts with Go evidence for attack.
- Pitfalls: (1) a hand-written `if m = n` picks `instDecidableEqString`, the laws' `if S n` (open Classical)
  `Classical.propDecidable`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (2) `unfold` does not
  beta-reduce `(fun n => S n ∨ S' n) n`: `dsimp only`. (3) A theorem's default argument (`trkHalf_eq … I`) is
  filled with the default when omitted: pass it. (4) Macros: frame patterns as ``$(frameH `H)``. (5) Stray
  Perennial clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6)
  `etc/gen-interface.py --layout` builds every package module: build first. (7) simp normalizes
  `decide (a ∉ l)` to `!decide (a ∈ l)` inside Iris hyps: state filters in the `!decide` form; an iris hyp
  `iframe` will not match may still `iexact`. (8) Call an Iris-context spec with `wp_apply Hf $$ %a %b … [$H]`.

### A2 axioms (2026-11-17, superseded)

- Branch `auth-schema-srv`, worktree `/shared/etcd-grove-authschema`; Perennial pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json` everywhere. Scope `notes/auth-schema-srv-scope.md` §3 (A2-A7);
  decisions `questions.md` (untracked; **A1 decided by etcd-grove-03**); soundness `notes/auth-schema-srv-a1-soundness.md`.
- Done: A1.1-A1.9 (52d85a42f6 … 23e2504247); A1.10 (6fe91f236f): the coordinator's A1 decisions: one spec
  (`Unlock.spec` the claimed statement, `Unlock.wp_proof`; old text the corollary `Unlock.spec_free`, `UnlockBare.lean`;
  `UnlockClaimed.lean` gone); `trkSide_mode` private (`trkSide_mode_up`, `trkSide_mode_win` public); `rbPartR_idle`
  takes `tkI`; soundness §4.2/§5 updated. Full build ok (log `/shared/tmp/auth-schema-srv/a110-build1.log`), tcb
  baseline unchanged, interfaces regenerated.
- A2: (B) chosen by the user; attacked (SURVIVES, `notes/axiom-review/bbolt-foreach.md`), MINORs applied;
  axioms `bbolt.Bucket.ForEach_kvr.wp_proof`/`ForEach_kvw.wp_proof` added (72c59c8aff), reached by no root yet
  (the tcb baseline moves, +2, when the backend Link reaches them: rerun `etc/tcb-report.py --check --update`).
- Next, A2's backend side (Draft §4), specs as their `UnsafeRange` siblings:
  `unsafeForEach` (tx, bucket, visitor; read or write transaction: one spec, the transaction's side as a
  parameter, e.g. a disjunction of `txLive q ∗ rtxSnap D ∗ rtxStats` / `ownWTxG … S`, entries `bktEnts (bktOf D|S n)`,
  the visitor's spec as the axioms'); `batchTx.UnsafeForEach` (over `btW γ t st`, entries `bktEnts (bktOf st.S
  bi.name)`, as `batchTx.UnsafeRange`); `baseReadTx.UnsafeForEach` (over `baseRd`: buffer `ForEach` for the dups
  (`txReadBuffer.ForEach.spec`, `visitorSpec`), a `map[string]struct{}`, `unsafeForEach` under `txMu`, then the
  buffer's `ForEach`; the visitor sees bbolt's entries whose keys are not in the buffer, in order, then the
  buffer's (`bkOf rv.2.bks bi.id`), its bytes `rdB rtx`); then `readTx`/`concurrentReadTx` wrappers if the auth
  readers need them. Then A3 (its own Draft first, a stop). Merge lean (3cd4b72599 or later) before the next full
  build.
- Pitfalls: (1) a hand-written `if m = n` picks `instDecidableEqString`, the laws' `if S n` (open Classical)
  `Classical.propDecidable`: write `@ite _ (m = n) (Classical.propDecidable _) …`. (2) `unfold` does not
  beta-reduce `(fun n => S n ∨ S' n) n`: `dsimp only`. (3) A theorem's default argument (`trkHalf_eq … I`) is
  filled with the default when omitted: pass it. (4) Macros: frame patterns as ``$(frameH `H)``. (5) Stray
  Perennial clone: keep `.lake/package-overrides.json`; `ls .lake/packages` = Qq, batteries, iris. (6)
  `etc/gen-interface.py --layout` builds every package module (`AuthSplitDraft` too): build it first.


### A1.9 (2026-11-17, superseded)


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
