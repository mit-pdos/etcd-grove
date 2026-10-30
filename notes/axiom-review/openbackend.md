# `storage.OpenBackend`: refuted as documented (premise gap, 2026-10-29)

**Reviewed.**
- The axiom `storage.OpenBackend.wp_proof`, its triple in
  `Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`, and the premise it shares with
  `OpenSnapshotBackend` (`openPre`, `dbOpensOk`, `Proof/go_etcd_io/etcd/server/v3/storage/InvOpen.lean`).
- It is reviewed as restated on branch `backend-cmp` in `2e49ff1aa9`: the wand
  `⌜noCmpData D⌝ -∗ bkNoCmp γ` dropped, and `newPost`/`newPostK` now carry `fkOwn γ (fkInit D)`,
  the client's half of the compaction keys' absence flag (`notes/backend-cmp-plan.md`, "The
  compaction keys' tracked absence").
- `storage.OpenSnapshotBackend` is not an axiom: it is proved from its body over this axiom and
  the rename's spec, so it is reviewed through it.
- etcd at the pin (the fork's `249d76bea`), bbolt v1.5.0.
- The review branch is `axiom/openbackend`, off `backend-cmp` at `a67a6b9056`, not off `lean`:
  the restated axiom exists only on `backend-cmp`.

**Verdict.**
- **The restatement survives.** The new claim, `fkOwn γ (fkInit D)`, adds no trust of its own.
- **The axiom is refuted as documented,** by a proved counterexample: its premise `dbOpensOk` is
  documented as a fact about the environment, but whether bbolt's `Open` succeeds also depends on
  the configuration.
- A program whose environment cooperates panics in Go, and the axiom proves it returns, no
  `sorry`.
- **Fixed (2026-10-29, the user's decision, on `backend-cmp`):** `openPre` gained `openMmapOk cfg`
  (below); the etcd finding is `issues/etcd-quota-backend-bytes-mmap-panic.md`.

## The claim

`OpenBackend(cfg, h)` returns the backend `backend.New` makes, `newPostK γ P W Pk K b D`. Its
precondition is the file holding `D` (`fileHolds`) and `openPre`:
- `⌜dbOpensOk⌝`;
- a non-nil logger;
- a nil or valid feature gate;
- `P.Wf`;
- `P.limit = openLimit cfg`;
- the hooks' contract;
- the creator's batch-lock step.

The axiom's docstring says why it is an axiom: `newBackend` runs on a goroutine, and its panic
on a failed bbolt `Open` cannot be excluded from `New`'s spec. "Under `dbOpensOk` it does not
panic."

`dbOpensOk` (opaque `Prop`) is documented as an environment premise (`InvOpen.lean`'s header):
"bbolt's `Open` succeeds on the database files the server opens after its start (the file
system, the disk and the file lock cooperate: no other process holds the file's lock, no I/O
error) ... True of the runs covered (one process per data directory, a local disk)."

## The gap

`newBackend` (`server/storage/backend.go:44-70`) does more than pass the environment through.
It also derives bbolt's options from the configuration:

```go
if cfg.QuotaBackendBytes > 0 && cfg.QuotaBackendBytes != DefaultQuotaBytes {
	// permit 10% excess over quota for disarm
	bcfg.MmapSize = uint64(cfg.QuotaBackendBytes + cfg.QuotaBackendBytes/10)
}
```

That `MmapSize` becomes bbolt's `InitialMmapSize`, and bbolt fails it:
- `Open` calls `db.mmap(InitialMmapSize)`;
- `mmapSize` returns `"mmap too large"` above `common.MaxMapSize` (`0xFFFFFFFFFFFF`, 256 TiB, on
  amd64; `bbolt@v1.5.0/db.go:590`);
- `Open` then fails, and `backend.New`'s `newBackend` panics
  (`bcfg.Logger.Panic("failed to open database", ...)`, `server/storage/backend/backend.go:235`),
  reached from `storage.newBackend`'s `backend.New(bcfg)` (`server/storage/backend.go:59`).

This happens for any quota above about 2.6·10^14 bytes. The sum `q + q/10` also overflows `int64`
near `MaxInt64`, which ends the same way. No environment makes such an `Open` succeed, so
`dbOpensOk` as documented holds while Go panics.

`openPre` constrains no other configuration field. The others were checked and found harmless:
- `MemoryMlock` can fail only on the environment's `RLIMIT_MEMLOCK`;
- `BackendFreelistType` defaults to bbolt's array freelist;
- `BackendBatchInterval` goes to a timer that takes any duration;
- `BackendBatchLimit` is constrained by `P.Wf` with `openLimit`.

## The counterexample

**Go** (`examples/axiomcx/openquota/openquota.go`):

```go
func Open(lg *zap.Logger, dir string) {
	cfg := config.ServerConfig{Logger: lg, DataDir: dir, QuotaBackendBytes: 1 << 50}
	storage.OpenBackend(cfg, nil)
}
```

**It panics** (`openquota_test.go`, `GOTOOLCHAIN=go1.27.3`, etcd at the pin):
- The panic is on `OpenBackend`'s goroutine, which kills the process. So `TestOpenPanics` runs
  `Open` in a child process, over a fresh data directory, and checks the output.
- The control `TestOpenDefaultQuota` opens the same kind of directory, in the same environment,
  with the default quota: it succeeds.
- Three runs, all alike:

```
openquota_test.go:41: the child panicked (exit status 2): panic: failed to open database
--- PASS: TestOpenPanics (0.02s)
--- PASS: TestOpenDefaultQuota (0.00s)
```

The child's log has bbolt's `"error":"mmap too large"`, which the test checks.

**The proof**
(`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/openquota/Open.lean`, goose project
`axiomcx-openquota`):

```
dbOpensOk → {{ isPkgInit openquota ∗ ⌜lg ≠ null⌝ ∗ fileHolds (config.backendPathOf dir) ∅ }}
  Open(lg, dir) {{ RET #(); True }}
```

- **`Open.wp_proof`** takes `dbOpensOk` and `storage.OpenBackend.spec` as hypotheses. It chooses
  parameters `P0` (no buckets, no hooks, the default batch limit 10000, `P0_wf`), the nil hooks
  and `W = Pk = K = True`, and discharges `openPre`.
- **`Open.wp_axioms`** instantiates the spec with the axiom.
- **Checks:** `lake build` of the module (against `/shared/perennial-ad74ee4`) passes;
  `etc/gen-init.py --check` and `etc/goose.py --check --project axiomcx-openquota` pass.

`#print axioms`:
- **`Open.wp_axioms`** prints exactly `Open.wp_proof`'s list plus
  `storage.OpenBackend.wp_proof`.
- **`Open.wp_proof`'s list (1180 names):** Lean's three, plus the opaque declarations of the
  imported translations and of bbolt's model, which make no claim (`fileHolds`, `ownDB`, `isDB`,
  `ownWTxG`, `rBkt`, `rtxSnap`, `rtxStats`, `txDB`, `txLive`, `backend.optsAt`). There is no
  `sorryAx`.
- **`dbOpensOk`** is a hypothesis of both theorems, not an axiom. The refutation therefore rests
  on its documented meaning, and the control test shows the run satisfies that meaning.

## What rests on it

Every result through a backend the server opens rests on the axiom: `NewServer.spec`'s
bootstrap, `applySnapshot` through `OpenSnapshotBackend`, and the closed theorems.
- `NewServer.spec` quantifies over the configuration, so as documented it claims no panic for
  quotas like this one.
- The closed theorems' examples build their configuration with etcd's default quota. As far as
  their configuration goes they are not affected, but that was not checked in detail.

## The restated part: what was tried (survives)

`fkOwn γ (fkInit D)` is not the axiom's own claim. It is `New`'s post, proved from bbolt's
`Open_kv` (the opened database holds `D`) in `InvNew.lean`, where the batch lock's half
(`fkHalf`) is allocated with `fkAbsSt` of the initial state.
- **What it rests on:** its truth reduces to bbolt's axioms (reviewed in `bbolt.md`; `Open_kv`
  survives) and to `fileHolds`, the environment's claim about the file.
- **bbolt's freelist and pending pages, and crash recovery:** `D` is bbolt's logical data from the
  valid meta page. A partially written file is the environment's `fileHolds` claim, not the
  axiom's.
- **A second `OpenBackend` on the same path:**
  - In the model, `fileHolds` is an exclusive opaque resource with no duplication law, and
    `Open_kv` consumes it.
  - In Go, the second `Open` waits on the file lock forever: no panic, so no counterexample.
  - Another process holding the lock is excluded by `dbOpensOk`'s documented meaning.
- **`OpenSnapshotBackend`'s rename onto the open backend's path:**
  - The rename's spec moves `fileHolds` from the snapshot's path to the backend's.
  - In Go, the old backend keeps its inode, and the new `Open` locks the new file.
  - `fkInit` is computed from the received `D`, whatever it holds.
  - Not attacked here: that the received image has no compaction key (`keyImage`'s last two
    conjuncts, D22's chain). Once compaction runs on the leader (M2), its snapshot database holds
    `finishedCompactRev`, so that claim of D22's needs revisiting then.
- **Defragmentation's file swap:** it copies the data into a new file and renames it. Keys are
  copied, never created, so absence is kept. It is not in the model's specs today.
- **The fixed key set:** `fkKey` (`Model2.lean:407`) names `"meta"` and the two keys, as
  `schema/bucket.go` does. A client bucket with `Meta`'s name must have `Meta`'s id (`P.has`,
  `P.Wf`'s distinct ids), so no second bucket aliases it.

Not tried: the closed adequacy form; 32-bit platforms (where `MaxMapSize` is `0x7FFFFFFF`, and
the bound starts at about 2 GB); the `Mlock` and freelist options under an unusual environment.

## The restatement (applied 2026-10-29 on `backend-cmp`, the user's decision)

Applied as recommended: `storage.openMmapOk cfg` (`InvOpen.lean`) is a conjunct of `openPre`, next
to `dbOpensOk`. `NewServer.spec`, `specCompact` and `specM` take it as `"%Hmmap"`, and the server
keeps it for the snapshot path (`srvSnapRO`); `applySnapshot.specSnap` and `applySnapshot_walk` take
it as `hmmap`. The examples' configurations (quota `0`) discharge it with `openMmapOk_of_quota_zero`.
The counterexample's precondition no longer meets the axiom's.

The proposal as it was:

Recommended: **`openPre` gains a configuration premise**, `⌜openMmapOk cfg⌝`. It requires either
that `newBackend` sets no mmap size (`QuotaBackendBytes ≤ 0` or the default), or that
`q + q/10` fits in an `int64` and is at most `0xFFFFFFFFFFFF`. The closed theorems' default
quota discharges it, and `NewServer.spec` would take it from its caller.

Alternative: **redocument `dbOpensOk`** to cover the configuration ("`Open` succeeds with the
options `newBackend` derives"). That is cheaper, but it hides a checkable fact behind an opaque
premise.

This is a trust-boundary change, and `NewServer.spec`'s premises are the user's.
