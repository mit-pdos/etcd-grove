# Compactor pilot: spec review, round 5 (before the freeze)

Reviewer: `spec-reviewer` (fresh, read-only). Worktree `/shared/etcd-grove-cp`, branch `compactor-pilot`.
Under review: the working tree on top of `45ba5db6f4`, with the freeze's coupling cleanup uncommitted. `HEAD` is
still `45ba5db6f4` (checked with `git log`), so no finding is stale. I read the rubric from `notes/spec-first-plan.md`
(Phase 1b and phase 3's no-cross-package-unfold rule). It matches the agent file. Nothing was built or run, as the
brief asked; every claim below comes from reading the files.

## Verdict

**Nothing in the first tier.** The round-5 changes leave the meaning of every compactor spec unchanged:
- the clock's three laws (`clockOk_ok`, `clockOk_Now`, `clockOk_After`) restate `clockOk` exactly;
- `compactReqIs` moved with the same body;
- `mvcc.ErrCompacted_target` is a sound consequence of mvcc's fact;
- `isLock` became `sync.isMutex`, which is Perennial's `sync` wrapper over the same `isLock`
  (`.lake/packages/perennial/Perennial/Proof/sync/Base.lean:57-59`). `Revision__Run` uses it through `sync.Mutex.wp_Lock`/`wp_Unlock`;
- the package-init instances moved into the two new `Base.lean` files.

**One cross-package unfold is missing from the known list:** `fmt.argsOk`/`fmt.argOk` in `New.lean:158`. By phase 3's
rule it must be removed (a law for it already exists) or justified before the freeze. Two minor tier-2 points
follow it.

## Ranked findings

1. **Phase-3 rule / caller burden (Tier 2; blocks the freeze by the rule). `New.lean:158` unfolds fmt's argument
   condition.**
   - Evidence: `simp only [fmt.argsOk, fmt.argOk]`, then a hand-built `ArgWf` proof (`:158-163`). It proves `Errorf`'s
     precondition for `fmt.Errorf("unsupported compaction mode %s", mode)` (`compactor.go`, `New`'s default arm).
   - `fmt.argsOk`/`fmt.argOk` are fmt's definitions (`Spec/fmt/Errorf.lean:47-61`), not the compactor's.
   - The owning module already exports the law: the tactic `fmt_args_ok` (`Spec/fmt/Errorf.lean:81-95`), whose
     `.cons_string` case is exactly this one. The cache uses it (`Proof/go_etcd_io/etcd/cache/v3/Cache__validateGet.lean:71`).
   - Restatement: replace `:158-163` with `fmt_args_ok`, after `iframe #; iframe Hasl`.
   - Not a spec defect: `New.spec` is unchanged.

2. **Abstraction (Tier 2). `Periodic.Run`'s loop invariant is in the public vocabulary module.**
   - What: `windowOk`, `windowOk_step`, `stampsOk` and its three laws, `firstOk`, `firstOk_step`,
     `perPermit_of_window` and `perPausedInv_fractional` were added to `Defs.lean` (`:105-143`, `:262-333`). Every
     `Spec/.../v3compactor/*.lean` imports that module, so every client imports them.
   - The section header calls them "its proof's; package-internal", but no module boundary enforces that. Only
     `Periodic__Run.lean` uses them; `retentions_bound` is also used by `newPeriodic.lean:58` and
     `Periodic__getRetentions.lean:42`.
   - Restatement: move the loop invariant into its own module (for example `.../v3compactor/PeriodicLoop.lean`),
     imported by `Periodic__Run.lean` only. Keep `retryOf`, `retentionsOf`, `retentions_bound` and `window_full_age`
     in `Defs`.
   - Affects no caller's proof; it is size and abstraction of what `interface/` would show.

3. **Hygiene (Tier 2, trivial).** `Defs.lean:46` still says `public import Perennial.Golang.Theory.Lock`. Nothing in
   `Defs` names `isLock` since the change to `sync.isMutex`. It is harmless, since `sync`'s `Base` imports it anyway.

No other finding. What I checked:
- **The clock laws, against `clockOk` (`Proof/github_com/jonboulle/clockwork/Defs.lean:90-104`).**
  - `clockOk_ok` only extracts the existential's pure part.
  - `clockOk_Now` and `clockOk_After` give exactly the two boxed triples, at `GoInterface.ok ci`, with the same
    `d`, `P` and `n` binders and the same post (`n ≤ T`, `stampAt γc (□ P) T`, the bag channel at
    `clockLb γc (T + d)`).
  - No strengthening. The trivial model stays as documented: `clockLb := True`, `stampAt P T := P`.
  - Against Go: `select` evaluates `ctx.Done()` and then `clock.After(retry)` after `revs = append(..., Rev())`
    (`periodic.go`, `Run`). So the stamp `T` of `RevLb v` comes after the sample, as `clockOk_After` requires, and
    `Periodic__Run.lean:222-229` follows that order.
- **`compactReqIs` (`Proof/go_etcd_io/etcd/api/v3/etcdserverpb/CompactReq.lean:26-27`).**
  - The same body as the removed `v3compactor.compactReqIs`.
  - `compactReqIs_of` is the introduction law that both `Run` proofs use (`Periodic__Run.lean:374`) instead of
    unfolding.
  - `EtcdServer.Compact`'s import closure no longer reaches `v3compactor.Defs`. I checked it by import closure: it
    reaches only the compactor's and the clock's `Base`/`GeneratedProof`, through `BaseApply`, as the Go import does.
  - Both modes, `spec` and `specOn`, take it.
- **`mvcc.ErrCompacted_target` (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/ErrLaws.lean:384-397`).**
  - It is stated over `isPkgInit mvcc` alone. The positional `icases` of `mvccInit` happens inside mvcc's own file,
    which is the right place.
  - Both `Run` proofs now take `ErrCompacted` from it (`Periodic__Run.lean:380`, `Revision__Run.lean:218`). The
    rest of the `errors.Is` argument is unchanged.
- **The `Base.lean` files.**
  - The instances are the ones removed from `BaseApply.lean`, with fact `True`.
  - `etc/gen-init.py` finds an instance's module by scanning `Proof/` (`instances()`, `:93-102`), so the hand-visible
    import changes in the two `Init.lean` files are what the generator produces. I could not run `--check`
    (read-only brief).
  - No compactor spec now imports any server module beyond `etcdserver/Base.lean` and `InvCindex`, which are
    cindex/schema instances reached through `mvcc.Base`. I checked by import closure of every
    `Spec/.../v3compactor/*.lean`.
  - `clockwork/Defs.lean` and `NewRealClock.lean` reach no etcd module at all, which closes round 3's coupling
    finding.

## Cross-package unfolds in the callers' proofs

**At the compactor's boundary** (the proofs of `New`, `newPeriodic`, `newRevision`, both `Run`s, and the
`Pause`/`Resume`/`Stop` stubs, which have no proof yet):

| proof | line | unfold | owner | status |
|---|---|---|---|---|
| `Periodic__Run.lean` | 222-224 | `iunfold context.isContextDef` (for `Done()`) | Perennial | known, justified (`notes/decisions.md`, freeze entry; `isContext_Done`, `notes/perennial-changes.md:119`) |
| `Revision__Run.lean` | 97-99 | `iunfold context.isContextDef` | Perennial | same |
| `New.lean` | 158 | `simp only [fmt.argsOk, fmt.argOk]` | `Spec/fmt/Errorf.lean` | **new: use `fmt_args_ok`** (finding 1) |

So `isContextDef` is not the only one: `fmt.argsOk` is a second.

What is not a cross-package unfold:
- every other `unfold`/`iunfold` in these files is of the compactor's own definitions (`isPeriodic`,
  `periodicRunTok`, `runPre`, `revGetterOk`, `compactableOk`, `errTreeOk`, `perPausedInv`, `revPausedInv`,
  `revPermit`, `compactorOk`, `modePermit`, `retentionsOf`, `revInterval`);
- `simp only [chan.blockingClausePre]` is a Perennial proof-mode pattern, which the rule exempts;
- the clock, mvcc's error and the request predicate go through laws only, with no `unfold clockOk`, `mvccInit` or
  `compactReqIs` left. I grepped the whole `Proof/` and `Spec/` trees for these. The only `unfold clockOk` outside
  the clock's own files is the k8s cacher's own, unrelated `clockOk` (`Proof/k8s_io/apiserver/pkg/storage/cacher/`).

**In the server's caller proofs.** None of these unfolds touches the compactor's package: the server's
`compactorOk` (`InvRun.lean:280`) is the server's own nil-only definition, so the unfolds of it at `InvRun.lean:284`,
`EtcdServer__start.lean:434` and `EtcdServer__run.lean:526` are fine. Taken literally, though, the rule flags these
existing unfolds of other packages' definitions. They are outside the compactor's boundary and do not block its
freeze; I list them because the brief asked for every one:
- `EtcdServer__start.lean`:
  - `api/v3/version`'s init fact, read through `isPkgInit_access` and destructured by position (`:241-246`);
  - `membership.membershipInit` by position (`:250-252`). This is the same pattern as the old mvcc 31st conjunct;
  - `context.cancelSpec` (`:397`, Perennial);
  - `waitMono` (`:158`, `pkg/v3/wait`);
  - `srvDoneOk`, `srvChanOk` and `bcastChan` (`:208-217`, the `read` package's contract, built here).
- `EtcdServer__run.lean`:
  - `schedule.schedRunning` (`:85`, `:162`, `:241`, `:318`) and `schedule.isFifo` (`:475`), both `pkg/v3/schedule`;
  - `ownSnapM` (`:457`), `smOpt` and `smPts` (`:462-465`), all raft's `InvPb`.
- `NewServer.lean`:
  - `bootInit` (`:363`, raft's `ApiVocab`);
  - `features.isFeatureGate` (`:468`);
  - `mvcc.watchReader` (`:574`, `:585`), `mvcc.isWatchableStore` (`:577`) and `mvcc.writerFrag` (`:591`, `:597`);
  - `txn.kvWriter` (`:589`, `:597`);
  - `backend.wbTok` (`:505`, `:657`, `:724`);
  - `lease.lessorIface` (`:705`);
  - `sync.atomic.ownUint64Def` (`:965`, Perennial);
  - the `method_unfold` of `mvcc.watchableStore`'s method (`:608`).
- The same `mvccInit`-by-position pattern also remains in `txn/checkRange.lean:37` and
  `v3rpc/serverWatchStream__recvLoop.lean:224`, which are outside the pilot. `mvcc/ErrLaws.lean` is where their laws
  belong.

## Strength margins (phase 2)

No caller needs any of them, so none is a finding.
- The callers of the compactor's specs are its own proofs. The server holds only a nil compactor (`InvRun.lean:280`).
- `EtcdServer.Compact.spec` takes any revision, so nothing downstream consumes C1 yet.
- Each margin:
  - the `retentions·retry` age;
  - the unused first-sample case;
  - no compaction while paused or after `Stop`;
  - monotone request revisions.
- Each margin becomes relevant only with C3 and the server side (M2, deferred: `notes/compactor-pilot-plan.md`, "The
  scope narrowed for now"). Even then, C3 (`σ.compacted ≤` the permitted revision) does not need monotone requests,
  because a lower compaction does not lower `compacted`.

## Per target (metrics)

- **`New`.**
  - Scope: 1 premise, `periodic → 10 ≤ ret` (plan "C2", narrowed in round 3).
  - Caller burden: no compactor caller yet (the server's `AutoCompactionRetention = 0`). The proof has 1
    cross-package unfold (finding 1).
  - Laws: `compactorOk_persistent`.
  - Trust: `clockwork.NewRealClock.wp_proof`, `zap.NewNop`, and the clock axioms.
  - Margin: none.
  - Round 4's T2-1 (`CompactEnv.γf`) is resolved: `γf` is now existential in the post.
- **`Periodic.Run`.**
  - Scope: 0.
  - Caller burden: `New`'s glue only, with no unfold of other packages. The proof has 1 Perennial unfold (known).
  - Trust: the clock axioms (`clockLb_init`, `clockLb_le`, `stampAt*`), and `errors.Is` and zap's specs.
  - Testability: `perPermit`'s pure part is tested (phase 2).
  - Margin: listed above, not needed.
- **`Revision.Run`.**
  - Scope: 0.
  - Caller burden: as for `Periodic.Run` (1 known Perennial unfold).
  - Trust: `clockOk_After` at `True`, so it rests on no clock fact for C1.
  - Margin: monotone requests, not needed.
- **`newPeriodic` / `newRevision`.**
  - Scope: `10 ≤ h` (periodic) and `lg ≠ null`, both established by `New`.
  - Caller burden: none.
  - Changed this round: `isRevision`'s mutex (`sync.isMutex`), with the same meaning.
- **`Defs.lean` vocabulary.** It passes the first tier. Finding 2 concerns its size. Laws: persistence of every
  predicate the callers carry; `firstSample_agree`; `perPausedInv_fractional`.
- **Clock (`Defs`, `NewRealClock`).** It passes. Laws: the three new ones cover every use. The trivial model is
  documented as the trust boundary. Coupling: no longer imports the server.
- **`CompactReq.lean`, `ErrLaws.lean`, the two `Base.lean` files.** They pass. There is no package API list for
  these packages (`etc/api/` holds only raft's), so `api-check` does not apply.

Ranking, most to least in need of revision: `New` (finding 1, its proof only), `Defs` (finding 2, 3), then the rest
(nothing).

## Uncertain

- I did not run `etc/gen-init.py --check` (read-only brief, build running). It would settle that the two edited
  `Init.lean` files and the eight `PkgTable.lean` files match the generator. From reading `instances()` I expect them
  to.
- Whether the working tree builds (the `Base.lean` moves, `sync.isMutex`) is the concurrent `lake build`'s to show.
  The instances that `v3compactor/Base.lean`'s `build_get_is_pkg_init_wf` needs (zap, etcdserverpb, mvcc, clockwork,
  and Perennial's packages) are reachable through its imports (`mvcc.Base` → `cache/v3/Base`).
