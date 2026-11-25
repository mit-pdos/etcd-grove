# Go-model overlays, basic slice: review packet (perennial#692)

For Upamanyu's review; nothing lands without it. The slice ships the plan and the models of the
basic libraries ahead of the elaborate work (fmt's stdout model, etcd-grove os/syscall = egos,
net = egnet), which stays on `goose-model-overlay-rest` / `go-models-rest/2026-11-24`.

| repo | branch | base |
|---|---|---|
| Perennial | `goose-model-overlay-basic` | `lean` fce59af75 |
| etcd-grove | `go-models-basic/2026-11-24` | `lean` e920f5c393, Perennial pin bumped to the branch above |

Full side-by-side of every replaced declaration (model Go next to `go doc -u -src` of the real
Go) and every trusted diff: `notes/go-models-basic-trusted-delta.md` (Perennial
`etc/trusted-delta.py origin/lean..HEAD`, run with go1.26.11).

## Summary

| package | became real translation | Go model (trusted Go, `goose/model/overlay/…`) | stays hand-written Lean | trusted Lean removed |
|---|---|---|---|---|
| internal/sync | the type `Mutex` (`struct{state int32; sema uint32}`, was `go.bool`), `mutexLocked` | `Mutex.Lock/TryLock/Unlock` (CAS spin on `state`; TryLock may fail by `Choose`), `fatal` (= `Stuck`) | — | `TrustedCode/internal/sync.lean` (106) |
| sync | the type `notifyList` (was axiomatized) | `runtime_Semacquire*`/`Semrelease` (the runtime's `cansemacquire` loop), `runtime_notifyList*` (the runtime's ticket algorithm, after the review), `runtime_registerPoolCleanup`, `Pool.Get/Put` (absorbs `goose/model/pool`) | `copyChecker`/`check`; new stub `poolModelAt` (identity) | `TrustedCode/sync.lean` 207→67; `goose/model/pool/**`; `Golang/Defn/Lock.lean`; field `go.Semantics.pool_sem` |
| primitive | — | — | `Mutex` spin lock (moved unchanged from `Golang/Defn/Lock.lean`), `Assume` (GOMODCACHE refuses the overlay) | 9 dead `.impl`s |
| internal/bytealg | — | `MakeNoZero` (cap `≥ n` by `ChooseUint64`, bytes arbitrary), `init.0` (`MaxLen` 63/31 by `Choose`) | — | `TrustedCode/internal/bytealg.lean` (81) + ManualProof stub |
| strings, bytealg Count | **lean's fce59af75 kept** (`Count`, `Index`, `IndexAny`, `IndexRune` real; `Count`/`CountString` models): equivalent to `-split`'s, so `-split`'s duplicates are dropped | `Split` stays S1's model (comment: genSplit's `len(s)+1` overflow) | — | — |
| time | (unchanged: `Timer.Stop/Reset`, `AfterFunc`, `when`, `Now`, …) | `runtimeNow/Nano/IsBubbled`, `newTimer/stopTimer/resetTimer`, `NewTimer`, `After`, `NewTicker`, `Ticker.Stop/Reset` + translated additions (clock global with CAS, timer goroutines) | stubs `now`, `Sleep`, `newRuntimeTimer`, `newRuntimeTicker`, `runtimeTimerFire` | `TrustedCode/time.lean` +51 −310 |
| runtime | (`Caller`, `Callers`, `CallersFrames`, `Version` as on lean) | `Frames.Next` (arbitrary frames) | `callers` = one-line `.impl` over the translated addition `callersModel`; `Gosched`, `buildVersion` (lean's) | `TrustedCode/runtime.lean` +20 −176 |
| internal/gomodel | `ChooseString`, `ChooseStrings` (translated Go over `Choose`/`ChooseUint64`) | — | `Choose`, `ChooseUint64`, `Stuck`, `StartRead` (S0, unchanged) | — |

Not in this slice (and why):
- **fmt**: its Printf stdout model imports `io/fs`, `internal/poll`, `syscall`, which etcd-grove
  translates itself under the same `Perennial.*` names ("environment already contains").
- **os, syscall** (runtime_args/runtime_envs over `ChooseStrings`, syscall `init.0` real over a
  `prlimit1` model): left out by scope; Perennial's os/syscall stay as on lean.
- **log** (`-rt`'s `Printf`/`Println`/`init.0` models): it does separate from os/syscall and
  imports nothing etcd-grove translates, but its model formats through `fmt.Fprintf`, so its
  proof rests on fmt's specs, which the fmt slice replaces (the integration proves log over the
  fmt overlay); and etcd-grove's log users (Net `log.Println`, ~20 Dsverify proofs) would need
  porting twice. It belongs with fmt. **Owed soundness fix**: lean's `log.Printf`/`Println` are
  no-op Lean that never call the arguments' `String`/`Error` methods (Go does; they can panic).
  That gap stays open until the fmt slice.
- **crypto/rand.Int**: deferred (parked on `goose-model-overlay-rest-rt-rand`).
- The x/tools v0.51 bump of `-xtools`: not needed (lean's goose already serves etcd-grove's go1.27.3).

## Infrastructure (trusted translator changes, `goose/util/model.go`)
1. The `go build -overlay` map also drops the runtime's push `//go:linkname <local> P.<Name>`
   of a replaced function (gc builds of the model tests only; goose's translation unchanged).
   Needed by `sync` (runtime_Semacquire*, notifyList*, registerPoolCleanup), `bytealg.MakeNoZero`,
   `time`'s runtime hooks. Test `model_linkname_test.go`.
2. CheckAPI compares a replaced function's type without parameter names (the models rename
   parameters). Test in `model_test.go`.
3. (`asm_amd64.h` in a blanked assembly file: lean's fce59af75 has it already; `-split`'s copy dropped.)

## Model next to real Go (short form; full text in the trusted-delta file)
- **internal/sync.Mutex.Lock**: Go: CAS 0→locked, else `lockSlow` (parks on bodyless runtime
  hooks, racy plain loads). Model: `for !CAS(&m.state, 0, mutexLocked) {}`. **TryLock**: Go fails
  if locked/starving or its CAS loses; model: `if Choose() {return false}; return CAS(0→1)`.
  **Unlock**: Go `AddInt32(-locked)`, `fatal` on unlocked; model: `CAS(1→0)` else `fatal` (=`Stuck`).
- **sync semaphores**: Go bodyless (runtime). Model: the runtime's `cansemacquire` loop retried;
  `Semrelease` = `AddUint32(s,1)`.
- **sync notifyList**: Go bodyless (runtime/sema.go). Model = the runtime's ticket algorithm:
  `Add` = `AddUint32(&l.wait,1)-1`; `Wait(t)` spins while `int32(t-l.notify) >= 0`;
  `NotifyOne/All` advance `l.notify` by CAS; `Check` empty.
- **sync.Pool.Get/Put**: Go pins to a P, `uintptr`→pointer arithmetic, `eface` casts (stuck in
  goose). Model: a `poolModel{mu; items}` installed in `p.local` by CAS; `Put` may drop
  (`Choose`), `Get` may miss (`Choose`) or takes an arbitrary element (`ChooseUint64`), then Go's
  own `New` fallback.
- **bytealg.MakeNoZero**: Go bodyless (runtime `mallocgc(needzero=false)`). Model: cap
  `max(n, ChooseUint64()>>1)`, every byte up to cap arbitrary. **init.0**: Go reads
  `cpu.X86.HasAVX2` (set by the runtime's cpuid); model `MaxLen = 63 or 31` by `Choose`.
- **time**: Go's timers are the runtime's (bodyless push linknames; `*Timer`↔`*Ticker` through
  `unsafe.Pointer`; a synchronous channel by GODEBUG). Model: a goroutine per timer that sleeps
  on a model clock (Go global + CAS over `runtimeNano`) and sends `Now().Add(-delta)` (Go's
  `sendTime` value), channel capacity 0 or 1 (`Choose`), `Stuck` where `timer.modify` throws
  (`when <= 0 || period < 0`); `Stop`/`Reset` do not cancel armed firings (only adds schedules).
- **runtime.Frames.Next**: Go reads the binary's symbol tables (goose: `uintptr` inc
  unsupported). Model: every field arbitrary (`ChooseUint64`/`ChooseString`, `new(Func)` under
  `Choose`), `more` arbitrary. **callers**: trusted `.impl` calling the translated
  `callersModel` (an arbitrary prefix of pcbuf, < 2^40 frames).

## Statement and premise changes (Perennial)
- Removed premise: `go.Semantics.pool_sem` (every result's class loses a field: stronger).
- time (approved, Upamanyu decision 1): `NewTimer.spec`, `NewTicker.spec`, `After.spec` take
  `isPkgInit time`; `After.spec_pkgInit` (what callers use) unchanged. Stronger posts:
  `runtimeNano.spec`, `when.spec` give `0 < x`.
- sync internal hooks: `runtime_notifyList{Add,Wait,NotifyAll,NotifyOne}.spec` over the new sealed
  `isNotifyList l` (were over `l ↦ l_v`); used only by `Cond`'s proofs; `Cond`/`NewCond`
  statements unchanged. `internal.sync.init_lock` restated over `zero_val Mutex` (the type changed).
- Spec files added for the translated additions (sync `poolModelOf/At`; time `now_`,
  `newTimer_`, `stopTimerAt`, …; gomodel `Choose*`). No other statement changes.

## etcd-grove at the bump
- Regenerated: goose (no change), gen-init (runtime's Init steps `internal/gomodel`'s
  initializer; PkgTables renumber), copy-part, raft-tla, specs-pkginit (stale `goose/model/pool`
  removed), kitgen: every `--check` passes.
- Ported (from go-models-rest 2d4884fb10, 7f6c88e143): `Proof/sync/MutexOwned`, kvreconf
  `MutexFresh`, mvcc `RWMutexWLocked`/`PlainRWMutex`, bbolt `Commit/CheckChan`, dsverify swift
  `ShInv`, workqueue `newQueue` (+ its Link), clockwork `Defs`/`realClock__After` (`isPkgInit time`).
  `backend/MutexLit.lean` (`wp_mutexLit`) is not on lean (nothing to delete).
- **Deleted** `Proof/sync/MutexLitSemantics.lean`, a premise class (`sync.Mutex{}` as a `go.bool`
  literal step): six workqueue results lose the premise (stronger).

## Evidence
**Perennial** (`goose-model-overlay-basic` 66a2b585e, VM key 564a3bcd639f4381, fresh):
- Full build of every module (`find Perennial -name '*.lean'`, 2500 modules + PerennialMeta, 4
  chunks of 650): **exit 0**, twice (full1 during assembly, full2 at the final head).
- `#print axioms` of the 224 linked theorems of internal/sync, sync, primitive, internal/bytealg,
  strings, bytes, internal/gomodel, time, context, runtime, errors, internal/stringslite and the
  testMutexLiteral examples (`notes/go-models-basic-axioms.txt`): each
  `[propext, Classical.choice, Quot.sound]`, except `strings.wp_Fields`, which rests on lean's own
  `axiom strings.Fields.wp_proof` (on origin/lean, not from this slice). **No new axiom, no sorry.**
- `etc/model-tests.sh` (go1.26.11, Go's own tests under the overlay; runtime's model spliced into
  every overlay as a dependency's): strings, errors, sync, `goose/model/overlaytests`, bytes,
  internal/stringslite, internal/bytealg, internal/sync, time: **ok** (skips listed in the script,
  each with its reason). `go test ./goose/...`: **ok**.
- Regeneration (`etc/update-goose-new.py --std-lib --models`, goose from the tree): reproduces the
  committed translations (only lean's known non-go1.26.11 `strconv.lean` churn, restored);
  `etc/gen-link.py --check`, `etc/meta-lib.py --check`: ok.
- `etc/trusted-delta.py origin/lean..HEAD`: `notes/go-models-basic-trusted-delta.md`. Tier 0:
  TrustedCode +127/−859 lines (bytealg −81, internal/sync −106, sync −157/+17, time −310/+51,
  runtime −176/+20, primitive +39/−27 = the relocated spin lock and 9 dead `.impl`s);
  `Golang/Defn/Lock.lean` −39; Go model overlays +907/−4 lines (translated and verified Go, its
  claim reviewed as Go); `goose/util/model.go` +100/−2 (the two translator changes above).

**etcd-grove** (`go-models-basic/2026-11-24`, VM key 3ebda268791704cc, fresh):
- **Decisive check: the whole default build at the new pin succeeds (28819 jobs), no
  "environment already contains".**
- `etc/gates.sh` (VM): build ok; links, goose (74 projects up to date), gen-init, copy-part,
  raft-tla, kitgen, specs-pkginit, axiom-tok, errorf-wrap, model-param, every other section ok.
  The one FAILED section is `merge-status`'s selftest, which runs `git log` and the VM sync dir is
  not a git checkout (environmental; unrelated to this change).
- **tcb-report before/after**: before = `etc/tcb-baseline.txt` on lean (329 axioms, 0 sorries);
  after: "trust base matches etc/tcb-baseline.txt (329 axioms, 0 sorries)", all 63 collections
  match. The trust delta is empty on axioms/sorries; one premise class fewer
  (`MutexLitSemantics`, six workqueue results). Report: 1138 results, 0 `sorry`.
- Fixes found by the build beyond packet-sync's list (all internal, no statement change):
  Net `ConnReaderLemmas` (its own NewCond proof allocates the notify-list invariant), bbolt
  `Commit/AssembleEnd` (an `omit`), gryff server boots (regenerated by `etc/dsv/_gryff_boot.py`,
  which gates does not check), k8s `utils/clock` 5 proofs and dsverify quepaxanet `Linked`
  (Perennial's linked time results instead of `wp_proof`s, which now take callee specs; time's
  `isPkgInit` by `iPkgInit`), raxos `SharedLoop` (a Countable instance for `internal/sync.Mutex`).

## Adversarial reviews (fresh agents trying to find a Go program where the model is more defined than Go)
- **sync** (lead's sub-agent, `gmr-adv-sync`): 1 UNSOUND — the first `notifyListWait` was a no-op,
  so `mu.Lock(); c.Wait()` returned where Go blocks forever → **fixed** (the ticket algorithm,
  Perennial 66369f153, in this slice; `goose/model/overlaytests/cond_test.go`). Framework gap
  (not new): spinning models vs Go's deadlock detector → `docs/KNOWN_LIMITATIONS.md` "Blocking and
  deadlock". NOTE: nil `Pool` gc panic value (gc-only). The `primitive` diff deletes dead `.impl`s.
- **time** (`gmr-adv-time`): no reachable divergence. Latent: a mid-run `GODEBUG=asynctimerchan`
  change (gc re-reads it on `cap`/`len`) → unreachable while `Setenv`/`Unsetenv`/`Clearenv` stay
  untranslated; recorded in `syscall.toml` and KNOWN_LIMITATIONS "time". 2 DOC, fixed.
- **split / bytealg** (handoff 2026-11-24): no unsafe divergence. IMPRECISE: `MakeNoZero`'s cap
  is exactly `n` under gc's Go body (not the size class); DOC: commit 8a86dc88f's subject
  ("strings.Split real") is wrong (Split stayed a model; that commit is not in this slice).
- **runtime / gomodel** (rt review, handoff 2026-11-24): UNSOUND (narrow) — `ChooseStrings` never
  returned a non-nil empty slice (Go's `runtime_args`/`runtime_envs` do, e.g. argc = 0) →
  **fixed** (63e056987, in this slice). IMPRECISE: `Frames.Next` stores `ci.callers` on an
  exhausted `Frames` (model-only race) → documented (7feebc84a, in this slice).
- **Owed**: no independent review of (a) the slice's reconciliation (which `-split` pieces were
  dropped in favour of lean's fce59af75: lean's Count/Index/CountString were Zeldovich's, reviewed
  with lean's own landing) and (b) the two `goose/util` translator changes (tests only, self-review).

## Resume / what is left
- Nothing lands: Upamanyu reviews this packet, then the two branches (Perennial first; etcd-grove's
  pin then points at whatever lands).
- Owed reviews (above). log's soundness fix waits for the fmt slice.
- If Perennial `lean` moves before landing: merge it into `goose-model-overlay-basic`, rerun
  `etc/update-goose-new.py --std-lib --models` (restore `strconv.lean`), the full build, and the
  etcd-grove regeneration (`etc/goose.py`, `gen-init`+`copy-part` to a fixed point, `gen-raft-tla`,
  `gen-specs-pkginit`, `etc/dsv/kitgen.py`, `etc/dsv/_gryff_boot.py`) with `PERENNIAL_DIR`.
