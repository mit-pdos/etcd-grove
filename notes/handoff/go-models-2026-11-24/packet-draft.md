# Go-model overlays S2–S7 (perennial#692): combined review packet (DRAFT, assembled by the lead)

Perennial: branch `goose-model-overlay-rest` (integration: lean + xtools + units). etcd-grove: branch
`go-models-rest/2026-11-24` (+ `go-models-rest-egnet/2026-11-24` for net), pinned to the Perennial branch.
Per-unit packets follow in <details>; this section is the summary and the decisions to check.

## Summary per package

| package | became real Go | became Go model (overlay) | stays hand-written Lean | trusted Lean removed |
|---|---|---|---|---|
| internal/sync | — | `Mutex.Lock/TryLock/Unlock` over Go's own `state int32` (CAS spin; `fatal` = `gomodel.Stuck`) | — | `TrustedCode/internal/sync.lean` (106) |
| sync | (RWMutex, WaitGroup, Once, Cond already real) | semaphores (runtime's `cansemacquire` loop), `notifyList*` (ticket algorithm, after review), `registerPoolCleanup`, `Pool.Get/Put` (absorbs `goose/model/pool`) | `copyChecker`/`check` (overlay API check forbids changing an unexported type's kind; follow-up a'); new stub `poolModelAt` (identity) | `TrustedCode/sync.lean` 207→67, `goose/model/pool/**`, `go.Semantics.pool_sem` field (one premise fewer on every result) |
| primitive | — | — | `Mutex` spin lock (relocated `Golang/Defn/Lock.lean` → `TrustedCode/primitive.lean`), `Assume` (GOMODCACHE overlay refusal: follow-up B) | 9 dead `.impl`s deleted |
| strings | `Count`, `Index` | `Split` stays S1's model (real Split's len 2^63-1 overflow would need a premise; option (a) offered) | — | — |
| internal/bytealg | — | `MakeNoZero`, `init.0`, `Count`/`CountString` (verbatim count_generic.go; asm blanked) | — | `TrustedCode/internal/bytealg.lean` (81) + ManualProof stub |
| fmt | `Errorf`, `Fprint` (+ D1=A) | formatting helpers moved from `model_test.go` into the overlay; `Fprintf` over the real `sync.Pool` buffer; `Printf` over an `os.Stdout` writer model; `Print` stuck | `underlyingAs[T]` | `TrustedCode/fmt.lean` ~4100 → ~15 (PENDING: unit running) |
| time | `Timer.Stop/Reset`, `AfterFunc`, `when`, `Now`, … (unchanged) | runtime timers, `NewTimer`, `After`, `NewTicker`, `Ticker.*`, clock (Go global + CAS) | `now`, `Sleep`, `newRuntimeTimer`/`newRuntimeTicker`/`runtimeTimerFire`/`runtimeTimerAlloc` | `TrustedCode/time.lean` +41 −310 |
| runtime | — | `Gosched`, `Frames.Next` | `callers` (one-line `.impl` over translated `callersModel`, with lean's 2^40 bound), `buildVersion` (lean's opaque value) | 213 lines |
| os, syscall (Perennial) | syscall `init.0`, `Getrlimit`, `setrlimit`, `errnoErr`, `origRlimitNofile` (over a Go model of `prlimit1`) | — | `runtime_args`, `runtime_envs` (one line each over `gomodel.ChooseStrings`), `Exit` | `arbitraryStrings` |
| log | — | `Printf`, `Println`, `init.0` (old no-op Lean never called String/Error: unsound, fixed) | — | |
| internal/gomodel | `ChooseString`, `ChooseStrings` (translated over Choose/ChooseUint64) | — | `Choose`, `ChooseUint64`, `Stuck`, `StartRead` (S0) | |
| crypto/rand | DEFERRED (not in this packet) | | | |
| etcd-grove os/syscall/durable | | (egos: PENDING) | | |
| etcd-grove net | `OpError.Error/Timeout/Temporary`, `isConnError`, `conn`/`TCPConn`/`TCPListener`, poll/syscall error methods | netFD-level model | 8 net-extension stubs | (egnet: PENDING) |
| etcd-grove crc32, go/token | | crc32's 3 arch hooks, `IsExported` | | `TrustedCode/hash/crc32.lean`, `Net/TrustedCode/go/token.lean` |

## Decided overnight by the lead (Upamanyu asleep; redo any in the morning)
1. **net `Conn.Read`/`Conn.Write` premises (spec preconditions, not top-level).** The real `conn.Read` compares
   the error with `io.EOF`, and `conn.Write` wraps only a non-nil error, so their specs need the dynamic types of
   `io.EOF` and `poll.ErrDeadlineExceeded`. Read/specLc take `isPkgInit io ∗ isPkgInit internal.poll`, Write takes
   `isPkgInit internal.poll`; poll's package fact is strengthened (proved from its translated initializer). One
   droppable commit. Alternatives: pure premises on the two values; keep Lean models of `conn.Read/Write`. Check:
   no top-level statement changes (tcb-report; PENDING).
2. **`Cond.Wait` (UNSOUND, found by review):** the `notifyListWait` no-op let `Cond.Wait` return where Go blocks
   forever (no spurious wakeups in Go). Fixed with the runtime's ticket algorithm (PENDING: sync unit).
3. **GODEBUG mid-run:** time's timer channel kind is fixed at make, gc re-reads `asynctimerchan` on cap/len.
   Unreachable: `Setenv`/`Unsetenv`/`Clearenv` stay untranslated (stuck); the rule is in `syscall.toml`; a
   KNOWN_LIMITATIONS entry with the witness. No new trusted `.impl`s.
4. **runtime vs lean's newer commits:** lean's `buildVersion` (opaque `buildVersionValue`, named by etcd-grove's
   approved UTF-8 premise) and `callers` 2^40 bound win over the unit's models.
5. **`runtime.callers`** stays a trusted one-line `.impl` (over the translated `callersModel`) rather than a pure Go
   model: its gc body must walk the real stack (testing panics on an empty one).
6. **crypto/rand.Int (D3) deferred:** FIPS self-test modelling question + ~1.5k lines of math/big proofs.
7. **os `ownFile` gains `nonblock ↦□ false`** (the real `File.fd()` reads it).
8. **`x/sys/unix` stays Lean** (not std: no `internal/gomodel`; `Mmap` returns `unsafe.Pointer`; `Munmap`'s registry is a skipped variable).

## Adversarial reviews (fresh agents, model vs real Go)
- sync: 1 UNSOUND (Cond.Wait, item 2), 1 framework gap (below), 1 DOC; rest no divergence (differential program
  identical under real Go and the overlay).
- time: no reachable divergence; latent GODEBUG (item 3); 2 DOC (fixed).
- fmt: 1 UNSOUND (the pooled printer buffer, aliased by a writer that keeps its slice: Go's `errorf` formats into
  a pooled `p.buf` and Go writes it directive by directive between user-method calls; the model did neither).
  Fixed: the model printer writes into `p.buf` as Go does (PENDING: fmt-fix unit). Rest no divergence (user-method
  calls, order and count matched Go on 15 differential cases; `%w`; writer errors; `Printf`/stdout; the stubs).
- split, egrest, rt, egos, egnet: PENDING.

## Framework-level gap (documented, not new)
Go's deadlock detector turns a global deadlock into a fatal throw; the models spin where Go parks (`Mutex.Lock`,
`Semacquire`, `notifyListWait`, `primitive` lock), so a robustness theorem says nothing about a program that
deadlocks. Same as the hand-written Lean lock before. KNOWN_LIMITATIONS entry + MODEL comments.

## Mechanism follow-ups
- Overlays cannot replace a file beneath GOMODCACHE (`go: overlay contains a replacement for …/pkg/mod/…`):
  `primitive.Mutex`/`Assume` and etcd-grove's J3 `JSONModel*` stay on the old route. Fix: materialize such
  packages outside GOMODCACHE (as `goroot.py farm` does for GOROOT) or point the fork's modules at the checkout.
- Overlay API check: let an unexported type change kind when it is unreachable from the exported API (a'), for
  `copyChecker`.
- A model can change which functions a package-variable initializer reaches, so the init order can differ from
  the real program's (crc32: `IEEETable` vs `castagnoliInitOnce`; unobservable there): a review-trusted checklist line.

- Perennial: no `go.NotInterface` instance for the predeclared named types (`uintptr`), so a `MethodResolve` on
  a named type over one (`syscall.Errno`) does not step; etcd-grove's net proof uses a local instance.
- fmt: `kindIs` stays a stub (equal to lean's); translating it needs a semantics fact that an interface's value is
  never a panic value.

## Goose translator commits (trusted)
867d5adb3 / cf08c93dd (allow the toolchain's `asm_amd64.h` in a blanked assembly file), fb61fea3d / 3595eb024 (blank the
runtime's push linkname of a replaced function), 02ff0ea6c / 78d6ef937 (CheckAPI compares types without parameter
names), x/tools v0.51 bump. (PENDING: diff summary.)

## Statement changes (all)
- time: `runtimeNano.spec`, `when.spec` post `True` → `⌜0 < sint.Z x⌝` (stronger); `NewTimer.spec`, `NewTicker.spec`,
  `After.spec` take `isPkgInit time` (approved).
- primitive: `init_Mutex` restated over `zero_val Mutex` (was `zero_val Bool`; same meaning today).
- net: Read/Write premises (item 1). PENDING: fmt, egos.
- Removed: `go.Semantics.pool_sem`; `[os.file.FieldAssumptions]`, `[os.fileStat.FieldAssumptions]` (169 files),
  `[net.FieldAssumptions]` (549 files); etcd-grove `backend/MutexLit.lean` axiom `wp_mutexLit` (deleted at the bump).

## Evidence (PENDING: integration build, #print axioms, trusted-delta, tcb-report before/after)
- Interim (integration 11a2209e2 = lean + xtools + split + time + rt; sync, fmt not yet merged): regeneration
  matches the committed translations (except lean's known non-go1.26.11 `strconv.lean`); the cone of every
  changed package (strings, bytealg, time, runtime, os, syscall, log, gomodel, context, errors, bytes) builds on
  the VM. `etc/trusted-delta.py origin/lean..HEAD`: TrustedCode −755/+81 lines (bytealg −81, log −26,
  runtime −166, syscall −63, time −259); Go model overlay +737 lines (translated and verified; its claim
  reviewed as Go); goose/util `model.go` +105/−4 (asm_amd64.h, linkname blanking, CheckAPI parameter names).
  Full report: tmp/gmr-lead/trusted-delta.txt (to be regenerated after sync and fmt).
- Integration 9bd58c78a (lean + xtools + split + time + rt + sync): the whole Perennial library (`Perennial`,
  `PerennialMeta`) builds on the VM, exit 0.
- model-tests (`etc/model-tests.sh`) pass on the integration branch: Go's own tests of strings, errors, sync,
  internal/sync, bytes, time, syscall, log, os, sort, runtime/debug under the overlay, plus the models' own tests
  (Cond.Wait without a signal blocks, ...), with the skips listed in the script, each with its reason.
- Found by those runs: rt's first Go model of `runtime.Gosched` (an empty body) replaced it for the runtime's own
  callers too in gc builds; `runtime.GC` loops on `Gosched`, so every test waiting for a GC cleanup hung. Fixed:
  `Gosched` is trusted again (lean's one-line `.impl`), so gc keeps the real one. Lesson for review-trusted: an
  overlay must not replace a runtime function the runtime itself calls unless its gc body behaves like Go's.
