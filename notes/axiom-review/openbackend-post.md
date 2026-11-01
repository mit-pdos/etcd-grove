# `storage.OpenBackend` after the compaction-keys post: refuted as documented again (`openMmapOk` too weak, 2026-10-29)

**Reviewed.**
- The axiom `storage.OpenBackend.wp_proof` (`Proof/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`),
  its triple (`Spec/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`) and its premise `openPre`
  (`Proof/go_etcd_io/etcd/server/v3/storage/InvOpen.lean`), as on branch `backend-cmp` at
  `aaa22d3714`. The post is `newPostK γ P W Pk K b D`; `newPost`
  (`Proof/go_etcd_io/etcd/server/v3/storage/backend/InvNew.lean`) now ends with
  `dlInit γ ∗ fkCl γ P D ∗ srSlot b`.
- The earlier review (`openbackend.md`) refuted the axiom by a quota above bbolt's `MaxMapSize`;
  `openPre` then gained `openMmapOk cfg`. This review re-checks that fix, and attacks what is new in
  the post.
- etcd at the pin (the fork's `249d76bea`), bbolt v1.5.0, `GOTOOLCHAIN=go1.27.3`, Linux amd64
  (4-level paging, `ulimit -v` unlimited).
- The review branch is `axiom/openbackend-post`, off `backend-cmp` at `aaa22d3714`.

**Verdict.**
- **The new post survives.** `fkCl γ P D`, `srSlot b` and `dlInit γ` are `backend.New`'s proved
  post (through `newBackend.wp_proof`, linked in `Link.lean`'s `wp_New`, no `sorry`). The axiom
  adds nothing to them but the mapping of `openPre` onto `New`'s premise, which is faithful.
- **The axiom is refuted as documented, again,** by a proved counterexample: `openMmapOk` bounds the
  mmap size by bbolt's `MaxMapSize` (256 TiB), but bbolt maps that size with one `mmap(2)`, and a
  Linux process on amd64 has 128 TiB of address space. A quota of `2^47` meets `openMmapOk` and
  `dbOpensOk`'s documented meaning, and `newBackend` panics.

## The gap: `openMmapOk` is bbolt's bound, not the kernel's

`openMmapOk cfg` (`InvOpen.lean`) says the quota `q` is not positive, is the default, or
`q + q/10 ≤ 0xFFFFFFFFFFFF`. Its docstring claims this is "a quota whose mmap size bbolt can map".
That is only bbolt's own software check:
- `mmapSize` (bbolt `db.go:581-613`) fails with "mmap too large" above `common.MaxMapSize`.
  Otherwise it rounds the size up to a whole GiB and caps it at `MaxMapSize`.
- `mmap` (bbolt `bolt_unix.go:55-60`) then maps that many bytes at once:
  `unix.Mmap(fd, 0, sz, PROT_READ, MAP_SHARED|flags)`.
- On Linux amd64 the user address space is 47 bits (128 TiB). Without a hint address it stays
  47 bits even with 5-level paging. A map larger than the free address space fails with `ENOMEM`.
  Measured in a Go test process: the largest single mapping is about 105 TiB.
- bbolt's `Open` fails. `backend.newBackend` then panics (`lg.Panic("failed to open database")`,
  `server/storage/backend/backend.go:235`) on `OpenBackend`'s goroutine.

So any quota with `q + q/10` between about 105 TiB and 256 TiB passes `openMmapOk` and panics.
Nothing in the environment is at fault:
- the directory is fresh;
- no other process holds the lock;
- the disk is local;
- `ulimit -v` is unlimited.

The same environment opens the same kind of directory with the default quota, and with a quota of
64 TiB (`q + q/10 = 64.0 TiB`, measured: it opens).

## The counterexample

**Go** (`examples/axiomcx/openva/openva.go`):

```go
func Open(lg *zap.Logger, dir string) {
	cfg := config.ServerConfig{Logger: lg, DataDir: dir, QuotaBackendBytes: 1 << 47}
	storage.OpenBackend(cfg, nil)
}
```

**It panics** (`openva_test.go`, `GOTOOLCHAIN=go1.27.3`, etcd at the pin):
- `TestOpenPanics` runs `Open` in a child process, over a fresh data directory, and checks that
  the child panicked with bbolt's "cannot allocate memory". A panic on a goroutine kills the
  process.
- The control `TestOpenDefaultQuota` opens the same kind of directory with the default quota.
- Three runs, all alike:

```
openva_test.go:41: the child panicked (exit status 2): panic: failed to open database
--- PASS: TestOpenPanics (0.01s)
--- PASS: TestOpenDefaultQuota (0.00s)
```

The child's log:

```
{"level":"error","logger":"bbolt","msg":"[GOOS: linux, GOARCH: amd64] mmap failed, size: 154812096184320, error: cannot allocate memory"}
{"level":"panic","msg":"failed to open database","path":".../member/snap/db","error":"cannot allocate memory"}
```

**The proof** (`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/openva/Open.lean`, goose
project `axiomcx-openva`): the earlier counterexample's proof, now discharging `openMmapOk` too.
```
dbOpensOk → {{ isPkgInit openva ∗ ⌜lg ≠ null⌝ ∗ fileHolds (config.backendPathOf dir) ∅ }}
  Open(lg, dir) {{ RET #(); True }}
```
- `Open.wp_proof` takes `dbOpensOk` and `storage.OpenBackend.spec` as hypotheses.
- `openMmapOk` is its third disjunct: `2^47 + 2^47/10 ≤ 0xFFFFFFFFFFFF`, by `decide`.
- `Open.wp_axioms` instantiates the spec with the axiom.

`#print axioms`:
- `Open.wp_axioms` prints exactly `Open.wp_proof`'s list plus `storage.OpenBackend.wp_proof`.
- `Open.wp_proof`'s list (1180 names, as the earlier counterexample's) is:
  - Lean's three;
  - the opaque declarations of the imported translations (types' `underlying`/`zero_val`, ...);
  - bbolt's opaque model (`fileHolds`, `backend.optsAt`, ...), which makes no claim.
- There is no `sorryAx`.

**Checks:**
- `lake build` of the module (against `/shared/perennial-ad74ee4`) passes.
- `etc/goose.py --check --project axiomcx-openva` and `etc/gen-init.py --check` pass.

## What is new in the post: the attacks (all fail)

The common reason: the post is `backend.New`'s. In Go, `OpenBackend` returns what `newBackend`
returns, and `newBackend` returns `backend.New(bcfg)`. `New`'s spec is proved
(`Proof/.../backend/New.lean` over `newBackend.wp_proof`, linked as `wp_New` in
`Proof/go_etcd_io/etcd/server/v3/storage/backend/Link.lean`). Its only axioms are bbolt's
(`bbolt.wp_Open_kv`, reviewed in `bbolt.md`) and Perennial's. So an attack on `fkCl`, `srSlot` or
`dlInit` is an attack on those axioms, or on `New`'s premise as `openPre` supplies it. That premise
was checked field by field:
- **The file.** `fileHolds (config.backendPathOf cfg.DataDir') D`, against `New`'s
  `fileHolds bcfg.Path' D`. `bcfg.Path = cfg.BackendPath()`, whose proved spec
  (`ServerConfig__BackendPath.lean`) returns `backendPathOf c.DataDir'`. The same `D` reaches
  `fkCl γ P D`.
- **The batch limit.** `P.limit = openLimit cfg` against `P.limit = bcfg.BatchLimit'`.
  `DefaultBackendConfig` sets `defaultBatchLimit = 10000` (`backend.go:36`), and `newBackend`
  overrides it only when `cfg.BackendBatchLimit != 0`. That is `openLimit`.
- **The hooks.** `bcfg.Hooks = hooks`, the same interface `h`, so `hooksOk P W Pk h` is `New`'s.
- **The creator's batch-lock step.** It is the same formula.

The specific attacks:
- **`fkOwn γ 0` for a file that holds a compaction key.** `fkInit D` is `0` exactly when `fkAbsD D`:
  no `dget D "meta" k` at `scheduledCompactRev` or `finishedCompactRev`. `D` is the file's data by
  `fileHolds`. `New`'s proof (`NewAlloc.lean:499-514`) allocates the flag at `fkInit D` with
  `fkOk_init` of the initial state. A file holding the keys gives `fkOwn γ 1`, which says nothing.
  To get `0` for such a file the program would need a `fileHolds` with a false `D`. That is the
  environment's claim, or the claim of the axiom that produced it, not this one's. The open item
  from `openbackend.md` stays open, outside this axiom: a received snapshot image's claim to have
  no compaction key (D22's `keyImage`).
- **`fkV γ true` with values that violate `P.FV`.** `fkWInit P D = decide (fkWfD P D)`, computed
  from the same `D` and allocated as a persistent ghost variable that never changes. `P` (and so
  `P.FV`) is the caller's choice: a weak `FV` makes `true` say little, and the strong one the store
  uses makes it `false` on bad data. The bit stays true afterwards because `UnsafePut`/`UnsafeSeqPut`
  of an `fkKey` need `P.FV v` (`batchTxBuffered__UnsafePut.lean`) and `fkPut`. Both are proved, so
  that is not this axiom's to defend.
- **Two `srSlot b`s.** `newBackend`'s proof (`newBackend.lean:196-201`) runs `init_RWMutex` on the
  fresh `safeRangeDeleteMu` and takes one reader share (`rep_one` of `actualMaxReaders`). It gives
  that share out once and drops the rest, so no proof can take the write lock either.
  - Each `OpenBackend` allocates a fresh `b`, so a second open (or `OpenSnapshotBackend`'s) gives a
    slot of a different mutex.
  - In Go, two opens of the same path block on bbolt's file lock: no panic.
- **Breaking the mutex with the slot.** `UnlockForSafeRangeDelete` needs `srHeld b`, which only
  `LockForSafeRangeDelete` returns (proved, over Perennial's `RWMutex` specs). An `RUnlock` without
  an `RLock` (Go's fatal "RUnlock of unlocked RWMutex") cannot be proved. The write side
  (`backend.go:699`) needs shares no proof has.
- **`dlInit`.** It is the whole fraction of the deletable-keys registration, minted by `New`'s
  proof and given once. The same argument applies.
- **Combining with `backend.New`.** A program that calls `New` directly and also calls
  `OpenBackend` gets two backends. Each needs its own `fileHolds`, an exclusive opaque resource
  with no duplication law.

## The earlier hole

`openMmapOk` does close the earlier counterexample (`openquota`'s `2^50`: `q + q/10 > 2^48 - 1`)
and the `int64` overflow (the bound is on the mathematical sum). But the bound is the wrong one,
as shown above.

## What rests on it

The same as in `openbackend.md`:
- `NewServer.spec` (bootstrap) and `applySnapshot` through `OpenSnapshotBackend` take
  `openMmapOk` from their caller, so as documented they claim no panic for quotas like this one.
- The closed theorems' examples use quota `0`, which `openMmapOk_of_quota_zero` discharges: they
  are not affected. Their run still maps the default `InitialMmapSize` (10 GiB), which is an
  environment matter (below).

## Proposed restatement (not applied: the user's decision)

1. **Tighten `openMmapOk`'s third disjunct** to a size the platform's address space holds. The
   recommended bound is `q + q/10 ≤ 2^46` (64 TiB, half of the 47-bit space; measured to open).
   A tighter one, etcd's `MaxQuotaBytes·11/10` (8.8 GiB), would match etcd's own warning
   threshold (`quota.go:33`) and cover nearly all real configurations.
2. **Document the address space in `dbOpensOk`** (`InvOpen.lean`'s header): "... and the process's
   address space can hold the database map (no `RLIMIT_AS` below it, room left by the other
   mappings)". No configuration bound guarantees this. Even the default 10 GiB `InitialMmapSize`
   fails under a small `ulimit -v`, which is an environment fact like the file lock. Item 1 keeps
   what is checkable about the configuration out of the opaque premise, as the first fix intended.
3. The issue `issues/etcd-quota-backend-bytes-mmap-panic.md` is amended. The real limit on amd64
   Linux is the 47-bit address space, not `MaxMapSize`, so the fix it proposes (validate against
   `MaxMapSize·10/11`) is not enough.

Not tried: 32-bit platforms; `MemoryMlock` with a large file under `RLIMIT_MEMLOCK` (an
environment fact); the closed adequacy form.
