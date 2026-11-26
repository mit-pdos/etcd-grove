# `storage.OpenBackend` with a concrete `dbOpts`: survives (2026-11-25)

**Reviewed.**
- The axiom `storage.OpenBackend.wp_proof` (`Proof/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`,
  its triple in `Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`). Its text is unchanged, but
  its post's last conjunct `⌜cfg.UnsafeNoFsync' = false⌝ -∗ backend.dbOpts γ.db` now has content.
  - Until `73558d4d57`, `dbOptsRaw` was an opaque token. Now it is
    `onFs (bbolt.boltSyncs γ)` (`backend/DbOpts.lean`).
  - `bbolt.boltSyncs γ := ∃ db, dblAt (bnsOf γ.gs) db ∗ db.NoSync ↦□ false ∗ db.NoGrowSync ↦□ false`
    (`Spec/go_etcd_io/bbolt/Api.lean`).
  - So the axiom now claims that `γ.db`'s `DB` struct has `NoSync` and `NoGrowSync` persistently
    `false`.
- Its one consumer is the C-I1 law `dbCrashKeep_new` (`backend/CrashInterim.lean:189`).
- The pins:
  - branch `axiom/openbackend-dbopts` at `73558d4d57`, on the etcd_safe line;
  - etcd fork `e94f33b50` (`etc/goose.py`, project `etcd`), whose `go.mod` replaces bbolt by the fork's
    `19e0771`;
  - bbolt fork `ea5656d` (`etc/goose.py`, project `bbolt`: `7d335aa3` plus P13's init fix, which
    touches no option field);
  - `go1.27.3`.
- `73558d4d57` does not elaborate as it stands: `boltSyncs`'s field points-tos need `go.Semantics`.
  The fix `9f36497a5a` (`bbolt-crash-int/2026-11-25`) adds `[sem : go.Semantics]` to `dbOptsRaw`,
  `dbOpts` and the instance. It does not change their meaning. This review is of that meaning. No
  build: no counterexample was found.

**Verdict: survives.** The claim holds of etcd's real `OpenBackend` path, and the field is never
written again. `γ.db` names the `DB` struct that `Open` allocated, and that struct keeps its values
across defrag. No combination with bbolt's specs gives `False`. There is no `issues/` finding. Two
docstrings are stale (see "Doc fixes").

## (1) The value is right, and never changes

**Value.** The Go path, at the pins:
- `server/storage/backend.go:38`: `bcfg.UnsafeNoFsync = cfg.UnsafeNoFsync`. `cfg` is passed by value.
- `server/storage/backend/backend.go:219-231`:
  - `bopts := &bolt.Options{}` is a fresh options struct.
  - `*bopts = *boltOpenOptions` copies the platform defaults. On Linux these are `MAP_POPULATE` and
    `NoFreelistSync`, with no `NoSync`.
  - Then `bopts.NoSync = bcfg.UnsafeNoFsync` and `bopts.NoGrowSync = bcfg.UnsafeNoFsync`.
- `:236`: `bolt.Open(bcfg.Path, 0o600, bopts)`.
- bbolt `db.go:184-192`: `db = &DB{...}` (a fresh struct), then `db.NoSync = options.NoSync` and
  `db.NoGrowSync = options.NoGrowSync`.

These values are copied, not aliased. A later write to `*bopts` would not reach `db`, and none
happens on the live path. Defrag copies the struct (`options := *b.bopts`, `backend.go:524`) before it
sets `options.NoSync = true` (`:534`).

**Never written again.** Two greps at the pins, tests included:
- etcd: `grep -rn '\.NoSync\b\|\.NoGrowSync\b\|NoSync\s*=\|NoGrowSync\s*='` finds only
  `backend.go:230,231,534`. All three write an `Options`, none a `DB`. No etcd code or test writes
  `db.NoSync`.
- bbolt: the same grep finds only `db.go:191-192` (in `Open`) and `cmd/bbolt/command/command_bench.go:152`.
  The latter is the `bbolt bench` CLI's `main` package, which etcd does not link.

So each `DB` struct's two fields are written once, before `Open` returns, and never again. That is
what `↦□` says. bbolt's proof already discards both fields persistently (`dbFixed`'s
`∃ x, NoSync ↦□ x`, `Proof/go_etcd_io/bbolt/Open.lean:884-885`). `Open`'s translation stores the
options' value there, so in the model `x` is the Go value.

**Run.** A Go test was added in a scratch clone of the etcd pin, not in this repository:
`server/storage/backend/zz_dbopts_review_test.go`, `TestZZDbOptsReview`, `go test` in workspace mode.
It runs `backend.New` with `UnsafeNoFsync = false`, then a put, `ForceCommit`, `Defrag` and `Close`.
It reads `be.db.NoSync`/`NoGrowSync` of the original struct and of the struct defrag reopens:
```
after New: NoSync=false NoGrowSync=false
after Defrag: same struct=false; old NoSync=false NoGrowSync=false; new NoSync=false NoGrowSync=false
UnsafeNoFsync=true: NoSync=true NoGrowSync=true
--- PASS: TestZZDbOptsReview (0.01s)
```

## (2) `γ.db` names that struct

- **Where `γ.db` comes from.**
  - `γ : BNames` is `New`'s proved post, and `γ.db : DBNames = bbolt.BoltName` is bbolt `Open.spec`'s
    `γ` (`isDB db γ.db = onFs (isBolt db γ.db)`, `InvBbolt.lean:359`).
  - `Open`'s proof allocates `(bnsOf γ.gs).dbl` fresh, as a discarded ghost-map element at the key
    `()` valued `db`: this is `dblAt`, persistent and agreeing (`Inv/Bolt.lean:38`).
  - So every `dblAt (bnsOf γ.db.gs) db'` has `db' = db`, the location `Open` returned. That is the
    struct whose fields `newBackend` set from `bopts`.
- **Defrag.**
  - In Go, `finishDefrag` closes the old `*DB` and assigns `b.db` a new `*DB` (`backend.go:603`), with
    the same `b.bopts` and so the same `false` fields.
  - `boltSyncs γ.db` speaks of the old struct, whose fields `Close` does not write. It stays true (the
    test above).
  - In the model, defrag is names-only. `OptsM.ok` excludes its custom `OpenFile`
    (`Spec/go_etcd_io/bbolt/Options.lean`, "Options `Open` accepts"). `maintenanceServer.Defragment` is
    only a guarded contract (`authMaintenanceServer__Defragment.lean`). So no spec makes a `γ` for the
    reopened database or for the temporary one.
  - The temporary database (`NoSync = true`) has no `BNames` and no `dbOpts`. If a later proof gives
    it a `γ`, `dbOpts` is unprovable for it, by the agreement below.
- **Snapshot install.** `OpenSnapshotBackend` renames, syncs the directory, then calls `OpenBackend`
  (`server/storage/backend.go:66-79`). That is a fresh `bolt.Open` with a fresh `γ`, a fresh struct
  and the same `cfg`, so its own `dbOpts` holds for the same reason. The old backend's `γ.db` still
  names its own, closed or still-committing, struct with unchanged fields. Which inode the path names is
  `dbCrash`'s concern (`Named`), not `dbOpts`'s.

## (3) Nothing false follows

The attacks tried:
- **`dbOpts` against `isBolt`'s `dbFixed`.**
  - `dblAt` agreement gives the same location. Points-to agreement on `NoSync` turns `dbFixed`'s
    `∃ x` into `x = false`.
  - That is a contradiction only if `γ.db`'s struct had `NoSync = true`. Go never does this under the
    premise, and the model agrees, since `Open` stores the option's value.
  - `newBackend`'s two lines (`backend.go:230-231`) are translated and proved (`backend.newBackend`).
    The only untranslated link is `storage.newBackend`'s copy (`:38`), checked above.
- **Forging `dbOpts` for a database opened `NoSync` (for `dbCrashKeep_new`).**
  - A client could open bbolt directly with `NoSync = true`: `Open.spec` allows any `NoSync`.
  - To forge, it needs `dblAt` at that `γ`'s name, which agreement pins to the real struct, and
    `NoSync ↦□ false` there, which agreement with `dbFixed`'s `↦□ true` forbids.
  - A `γ'` whose ghost names the client chose itself has `boltSyncs γ'` over a zero `DB` struct of
    its own. But `dbCrashKeep_new` also needs `dbHalf γ' D` and `txLive tx γ' 1 _`, which only bbolt's
    `Open`/`Begin` give, at the names `Open` allocated. Blocked.
- **Widened producers.** Since `dbOpts` is concrete, it is no longer only `OpenBackend`'s. Any proof
  that knows a `γ`'s fields are `false` can build it, for example a future bbolt `Open.spec` post
  under `NoSync = NoGrowSync = false`. That is the intent, since the crash proof that retires C-I1
  must read these fields. It is sound, because each such `γ` really syncs.
- **Cross-world** (`SKILL.md`, step 3). `dbOpts` is a post resource, not an entailment from
  persistent cells to a pure fact. `dbCrashKeep_new`'s other premises (`dbHalf`, `txLive`) are
  exclusive ghost state that a fresh heap does not hold.
- **No file extension.** If `theFs GF = none`, `dbOpts = <pers> False`. But `OpenBackend`'s pre
  `fileHolds` is `onFs _`, which is then also `False`, so the post is never reached.
- **Not tried:**
  - `GOOS=openbsd`, where `common.IgnoreNoSync` makes bbolt sync regardless. That only strengthens
    the claim.
  - Writes through `unsafe`/`reflect`: none in either source.

## Optional trust shrinking (not required for soundness)

The `dbOpts` conjunct could be proved instead of asserted:
1. bbolt `Open.spec`'s post gains `⌜v.NoSync' = false ∧ v.NoGrowSync' = false⌝ -∗ boltSyncs γ`. This
   needs `optsVal`/`optsAt` to expose those two fields. `Open`'s proof already holds both
   `↦□`s (`Open.lean:884-885`).
2. `backend.New.spec`'s post then gains `⌜cfg.UnsafeNoFsync' = false⌝ -∗ dbOpts γ.db`, from
   `newBackend`'s translated lines 230-231.

`OpenBackend`'s conjunct would then be `New`'s proved post, like the rest of its post. The axiom would
add only `storage.newBackend`'s untranslated copy (`backend.go:38`), which the axiom already trusts for
the rest of `bcfg`. This fits S5's rule "the axiom creates nothing" (`notes/bbolt-integration-plan.md`).

## Doc fixes (no change in meaning)

- `DbOpts.lean`'s and `Spec/.../storage/OpenBackend.lean`'s line citations are stale at `e94f33b50`:
  - `backend/backend.go:227-228` is now `:230-231`;
  - `backend.go:531` (the temporary database's `NoSync = true`) is now `:534`;
  - `backend.go:594` (the reopen) is now `:603`;
  - `server/storage/backend.go:35` (the copy) is now `:38`; `:35` is `func newBackend`.
- `Spec/.../storage/OpenBackend.lean`'s header still calls `dbOpts` "an opaque token about the Go
  configuration".
- `CrashInterim.lean`'s header still lists `dbOpts` among the "three opaque predicates".
