# klog's `printf` axioms: the arguments restricted (klog-args-fix, 2026-11-14)

A soundness fix of two landed trust-boundary axioms, `klog.Errorf.wp_proof` and
`klog.Verbose.Infof.wp_proof` (`Proof/k8s_io/klog/v2/{Errorf,Verbose__Infof}.lean`, statements in
`Spec/k8s_io/klog/v2/`). Found by etcd-grove-81's independent review of the k8s 7f-5a draft (lens
T5-f, on `klog.Warningf`); branch `klog-args-fix`, worktree `/shared/etcd-grove-auth3`. The audit
row: `notes/audit.md`, "Refuted by the 7f-5a review (klog-args-fix)".

## The refutation

Both specs said the call returns for **any** format and **any** arguments (`∀ f args`, premise
`isPkgInit` only, post `True`). klog v2.140.0 formats the arguments with `fmt.Fprintf(buf, format,
args...)` in `loggingT.printfDepth` (`klog.go:764-784`), which `Errorf` (`klog.go:1641`) and an
enabled `Verbose`'s `Infof` (`klog.go:1480`) both reach, and which recovers no panic. Go refutes
the claim two ways (`examples/premisefix/klogargs/klogargs_test.go`, own Go module, klog v2.140.0;
run by `etc/gates.sh`'s premisefix section):

1. **A nested panic escapes.** An argument whose `Error()` panics with a value whose `String()`
   panics too: `fmt`'s `catchPanic` recovers the first panic, prints the panic value with `%v`,
   and re-panics when that panics as well (`p.panicking`); the panic leaves `klog.Errorf`
   (`TestErrorfNestedPanicEscapes`, with the compactor's own format) and `Verbose.Infof` at `-v=4`
   (`TestInfofNestedPanicEscapes`). A one-level panic is recovered by `fmt`
   (`TestErrorfPlainPanicRecovered`): the fix's condition (a method that returns) is stronger than
   Go needs, which is sound.
2. **A map written concurrently** while klog formats it: `fmt` iterates it by reflection and the
   runtime throws `fatal error: concurrent map iteration and map write`, which no `recover`
   catches (`TestErrorfConcurrentMapFatal`, in a child process).

No closed theorem's program passes such an argument (the callers pass strings, an `int64`, a fresh
`[]string` and the client's errors: below), but the axioms as stated were false.

## The texts, old → new

`klog.argsOk` is new (`Spec/k8s_io/klog/v2/Args.lean`), on the pattern of `fmt.argsOk`
(`Spec/fmt/Errorf.lean`, premise fixes 6 D): the format's directives parse (`fmt.fmtDirectives`),
and each argument is `klog.argOkAt` its directive (those left over under `%v`):

```lean
def klog.strSliceArg (a : GoInterface) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ss : List GoString) (dq : DFrac),
    ⌜a = interface.mkOk (go.GoType.SliceType go.string) #sl⌝ ∗ sl ↦*{dq} ss)
def klog.argOkAt (d : fmt.Directive) (a : GoInterface) : IProp GF :=
  iprop(fmt.argOkAt fmt.methodVerbs d a ∨ klog.strSliceArg a)
def klog.argsOk (format : GoString) (xs : List GoInterface) : IProp GF :=
  iprop(∃ ds, ⌜fmt.fmtDirectives format = some ds⌝ ∗ klog.argsOkAt ds xs)
```

An argument is `nil`; a predeclared basic value (`fmt.ArgWf`: a string, an integer, ...); an
integer of a named type without `Format` under a non-method verb; under a method verb (`v s x X q`)
other than `%#v`, an error without `Format` whose `Error()` returns, or a `Stringer` with neither
`Format` nor `Error` whose `String()` returns (`fmt.argOk`: `fmt.stringMethodSpec`, persistent: it
returns some string needing nothing); or a `[]string` the caller owns at some fraction
(`fmt` prints it by reflection under any verb, calling no method, reading the elements, which the
ownership keeps from being written). A map, a struct, a pointer, an error whose `Error()` may
panic: none is admitted.

| axiom | old | new | Go evidence |
|---|---|---|---|
| `klog.Errorf.wp_proof` | `∀ f args, {{ isPkgInit klog }} Errorf f args {{ RET #(); True }}` | `∀ f args xs dq, {{ isPkgInit klog ∗ args ↦*{dq} xs ∗ klog.argsOk f xs }} Errorf f args {{ RET #(); args ↦*{dq} xs ∗ klog.argsOk f xs }}` | `TestErrorfNestedPanicEscapes`, `TestErrorfConcurrentMapFatal` refute the old; `TestCallersArgs` runs the callers' calls |
| `klog.Verbose.Infof.wp_proof` | `∀ v f args, {{ isPkgInit klog }} v.Infof f args {{ RET #(); True }}` | `∀ v f args xs dq, {{ isPkgInit klog ∗ args ↦*{dq} xs ∗ klog.argsOk f xs }} v.Infof f args {{ RET #(); args ↦*{dq} xs ∗ klog.argsOk f xs }}` | `TestInfofNestedPanicEscapes` (at `-v=4`, the level the store and `Compact` log at) |

What klog does beyond formatting stays the boundary's assumption, now said in the spec headers: with
its default flags (`logtostderr`) and no `SetLogFilter` (a filter's `FilterF` would run on the
format and arguments first), the line goes to standard error and a failed write is ignored.
(The review's `TestWarningfExitsOnLogDirError`: with `logtostderr=false` and an unwritable log file,
the first line exits the process with status 2. A configuration the examples do not use; recorded,
not modeled.)

### The other klog axioms (audited, unchanged)

| axiom | verdict |
|---|---|
| `klog.V.wp_proof` (`∀ l : w32`, some `Verbose`) | true: `VDepth` reads the verbosity (atomic) and, with `-vmodule`, the caller's file under klog's own lock; no argument is formatted |
| `klog.Background.wp_proof` (some `Logger`) | true: returns the global logger or `klogLogger` |
| `k8s_io.apiserver.pkg.storage.etcd3.klogWrapper_toLoggerV2` (the conversion returns some interface) | true: a struct converted to an interface; it formats nothing. grpc's later calls of the wrapper's `Infof`/... (`logger.go:35-48`) run in grpc's code, which the model does not run |
| `k8s_io.klog.v2.initFuncsOk`, `opaqueInitsOk` | package initialization, no arguments: not affected |

`klog.FromContext.spec`, `klog.KObj.spec` and `logr.Logger.{Info,Info_ptr,Error_ptr,V_ptr}.spec`
are named hypotheses (not axioms, `?` in their link files). **`logr.Logger.Info`/`Info_ptr`/
`Error_ptr` have the same "any arguments" form** (`kvs ↦*{dq} xs` and nothing on the values);
klog's text logger formats the values (their `String`/`Error`/`MarshalLog`), and a map written
concurrently throws there too. Not fixed here (outside the trust base); to fix before they become
axioms (phase 4/5 of `notes/k8s-daemonset-plan.md`), with a `klog.argsOk`-like condition on the
values.

## The axiom review's MAJOR: the format parser (pre-existing, fixed here)

etcd-grove-81's axiom review of this fix (2026-11-14; journal
`.../subagents/workflows/wf_32c275a9-bb7/journal.jsonl`, Go test
`/shared/tmp/coord-81/klog-review/review_test.go`) found one MAJOR, in `fmt.fmtDirectives`
(`Spec/fmt/Errorf.lean`), which `klog.argsOk` and every `fmt.argsOk` user (`fmt.Errorf`, `Printf`,
`ErrorfPlain`, `SprintfArgs`, `Duration.String`, `context.Err`, the cache's `Base.lean`) share: the
width and precision phases read any digit run, but go1.27.3's `parsenum` (`fmt/print.go:350-362`)
checks `tooLarge(num)` (`num > 1e6`) before adding each digit and gives up past it; `doPrintf` then
writes `%!(NOVERB)`, stops, and prints every argument as `EXTRA` under `%v`, calling its `String()`.
So `klog.Errorf("rev %99999999d", hangInt(5))` (a named integer, admitted under `%d` whatever its
`String` does) met the pre and hangs, or with a nested-panicking `String` panics.

**The fix (conservative):** `fmt.DirPhase.width`/`.prec` count the digits of the run, and a run of
more than `fmt.maxNumDigits = 7` digits makes `fmt.fmtDirectives` `none`. Exact would be: before
adding a digit, the value read so far `> 10^6`. A run of at most 7 digits never trips it (before the
`k`-th digit the value has `k - 1 ≤ 6` digits, `≤ 999999`); the conservative bound also refuses a
few formats Go accepts (`%.00000001d`), which is sound. Every caller's literal format still parses
(the full build). Go tests `examples/premisefix/klogargs/fmtparse_test.go`: `TestWidthOverflowHangs`,
`TestPrecisionOverflowHangs`, `TestWidthOverflowPanicEscapes`, `TestWidthOverflowNoVerb` (what Go
prints), `TestSevenDigitWidth` (the bound's control). Checked and not a gap: an unknown verb (`%z`) of
a named integer reaches `badVerb`, which prints under `%v` with `p.erroring` set, so `handleMethods`
calls no method (`print.go:374-393, 614-617`; `TestBadVerbNoString`): `fmt.argOkAt`'s integer
disjunct is right for every non-method verb.

## The callers

| caller | arguments | discharged by |
|---|---|---|
| `compactor.runCompactLoop` (`compact.go:207`) | `c.client.Endpoints()`, Compact's `err` | `Client.Endpoints.spec`'s `sl ↦* eps` (a fresh copy), `klog.argOkAt_strSlice`; `Compact.spec`'s new `fmt.argOk err`, `klog.argOkAt_of_argOk` |
| `compactor.runWatchLoop` (`compact.go:265, 273`) | `Endpoints()`, `getCompactRev`'s / `fromWatchResponse`'s `err` | the same; `getCompactRev.spec`'s and `fromWatchResponse.spec`'s new `fmt.argOk err` in the error disjunct |
| `Compact` (`compact.go:250`) | `rev : int64`, `Endpoints()` | `klog.argOkAt_int64`, `klog.argOkAt_strSlice` |
| `StartCompactorPerEndpoint` (`compact.go:60`) | `Endpoints()` | `klog.argOkAt_strSlice` |
| `store.updateOnce`, `store.deleteOnce` (`store.go:620, 478`) | the key, a `string` | `klog.argOkAt_string` |

Internal posts strengthened (form-only: stronger posts of proved internal specs, their proofs and
their one caller each in this branch): `Compact.spec` (`... ∗ fmt.argOk err`: the client's errors,
`kvErr`'s `statusErrOk`, `fmtArgOk_of_statusErrOk`), `compactor.getCompactRev.spec` (`fmt.Errorf`'s
error), `compactor.fromWatchResponse.spec` (`Err()`'s `errStrOk`, from the close error's
`statusErrOk`, `fmtArgOk_of_errStrOk`). The two lemmas are in `CompactorDefs.lean`. The macro
`klog_args_intro` (`Args.lean`) turns `klog.argsOk` of a literal format into one goal per argument.

## For 7f-5a: the restricted `Warningf`

`klog.Warningf` (`klog.go`, `logging.printf(severity.WarningLog, ...)`: the same `printfDepth`) must
take the same form. For the watch cache's `klog.Warningf("watch chan error: %v", err)`, a single
error argument whose `Error()` returns:

```lean
abbrev klog.Warningf.spec : Prop :=
  ∀ (f : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗ args ↦*{dq} xs ∗ klog.argsOk f xs }}
    (App (App (Val (@! k8s_io.klog.v2.Warningf)) (Val #f)) (Val #args))
  {{ RET #(); args ↦*{dq} xs ∗ klog.argsOk f xs }}
```

discharged with `klog_args_intro`, then `klog.argOkAt_of_argOk` (`%v` is a method verb, not `%#v`)
from `fmt.argOk err` (from `statusErrOk`/`errStrOk`: `fmtArgOk_of_statusErrOk`,
`fmtArgOk_of_errStrOk`; or `fmt.Errorf.spec`'s post), then `itrivial`.

## Reach and checks

Roots reaching the axioms (`.lake/tcb.json` after the build, 2026-11-14):

- `klog.Errorf.wp_proof` (12 roots): the closed theorems `k8s_compactor_safe`,
  `k8s_compactor_partition_safe`, `k8s_compactor_Main`, `k8s_compactor_MainPartition` (and
  `k8s_compactor.wp_{Main,MainPartition,apiserver}`, the etcd3 links).
- `klog.Verbose.Infof.wp_proof` (29 roots): the compactor's as above, and `k8s_etcd3_safe`,
  `k8s_etcd3_cluster_safe`, `k8s_etcd3_partition_safe`, `k8setcd3_{Main,MainCluster,MainPartition}`
  (through the store's `updateOnce`/`deleteOnce`).

No closed statement changed: no `Results`/`MainLinked`/`Link` file is edited, and the new premise is
discharged inside the callers' proofs (every argument is a string, an `int64`, a fresh `[]string`
or a client error). No new premise reaches a closed theorem.

Checks (commit `6613efc5b6`): full build (`lake build`, 17495 jobs) passed; `etc/tcb-report.py
--check` matches the baseline (870 axioms, 4 sorries, unchanged); 56 collections match, none updated;
`etc/gates.sh` passed all sections (axiom-tok, errorf-wrap, interfaces, premisefix incl. this
module, ...) except `k8s client error types`, which failed three times on `StartCluster failed` (a
port taken under the parallel load, the gate's known flake); rerun alone it passed
(`TestClientErrorTypes`, `TestCredentialNilError`, 208s). No interface diff (the etcd3 and klog
packages have no `etc/api` list).

## Handoff

- Done: the Go tests; `Args.lean`; the two spec texts; the three internal posts; the callers; build,
  tcb, gates (above).
- Next: etcd-grove-81's axiom review, then land (`etc/land.sh`, after the go).
- Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake
  --packages=/shared/tmp/manifest-ddc.json build`; Go: `cd examples/premisefix/klogargs && GOWORK=off
  go test -count=1 .`.
