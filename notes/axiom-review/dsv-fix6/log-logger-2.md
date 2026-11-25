# Review: `log.Default` and `*log.Logger`'s `Printf`/`Println` over the narrowed `argOk` (dsv-fix6, second review)

Reviewed 2026-11-25 by the `axiom` skill, worktree `/shared/etcd-grove-dsvfix6` (branch `dsv-fix6`) at
`662a685a08`, read-only (no branch, translation or Lean file: the counterexample is a Go test, run,
and a Lean proof argued below, not built); Perennial `fce59af75`; Go go1.27.3 (`src/log/log.go`,
`src/fmt/print.go`). Of the dsv-fix4 review (`../dsv-fix4/log-logger.md`) only its attack list was
read beforehand.

## The axioms

In `Dsverify/Proof/github_com/despreston/go_craq/Craq/LogAx.lean`, their statements in
`Craq/LogHyp.lean`:

- `github_com.despreston.go_craq.LogDefault.wp_proof`:
  `{{ isPkgInit log }} log.Default #() {{ (l : Loc), RET #l; ⌜l ≠ null⌝ }}`.
- `github_com.despreston.go_craq.LoggerPrintf.wp_proof`: **for every `l ≠ null`**, `msg`, `arg`, `xs`,
  `dq`: `{{ isPkgInit log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }} l.Printf msg arg
  {{ RET #(); arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}`.
- `github_com.despreston.go_craq.LoggerPrintln.wp_proof`: the same without `msg`.

`argOk v`: `nil`; `fmt.ArgWf` (Perennial `Proof/fmt/Base.lean:774`: a predeclared basic type, or a
named integer/string type without `Format`/`GoString`/`Error`/`String`); a `*store.Item` with `Key`,
`Version`, `Value` and `Value`'s bytes `↦□` (not `Committed`); a `*transport.NodeMeta` with
`p ↦{dq} m`; or `models_lab.errPlain v` = `errAny v` (a persistent WP of `Error()`) ∗ `errFmt`:
`NoFmtMeth ty` (implements neither `fmt.Formatter` nor `fmt.GoStringer`) and one of `rpc.ServerError`,
`*errors.errorString` (`s ↦□`), `*pbcodec.Error`/`*jsoncodec.Error` (`↦□`), `*net.OpError`
(`↦□`, `Source`/`Addr` `errLeaf`, `Err` `errLeaf` or the value of `poll.ErrDeadlineExceeded`);
`errLeaf`: `nil`, or a `NoFmtMeth` value of a pointer type, of `poll.errNetClosing` or of
`textproto.ProtocolError`.

Claims in plain words: `Default` returns non-nil; `Printf`/`Println` on **any non-nil `*Logger`**, with
`argOk` operands, do not panic, touch no caller memory beyond reading what `argOk` names, and give the
operands back.

## Verdict: **refuted in Go** (Lean argued, not built): the two method axioms; `LogDefault` survives. The operand condition `argOk` survives.

The false claim is not about operands: it is the receiver. The specs quantify over every `l ≠ null`,
but only a `Logger` made by `log.New` (or `std`) has an output. The zero `Logger` (`new(log.Logger)`,
`var lg log.Logger; lg.Printf(...)`, `&log.Logger{}`) has `out == nil`, and `output`
(`log.go:244`) calls `l.out.Write(*buf)` on the nil interface: a nil-pointer panic, outside
`fmt`'s `catchPanic`.

### The program (Go, run)

    func Main() {
        lg := new(log.Logger)   // non-nil: LoggerPrintf.spec's premise l ≠ null holds
        lg.Printf("hi")
    }

Test (`/shared/tmp/axrev-log2/lc/lc_test.go`, scratch, deleted after the review; `GOTOOLCHAIN=go1.27.3`),
deterministic:

    === RUN   TestZeroLoggerPrintf
        new(log.Logger).Printf: PANIC: runtime error: invalid memory address or nil pointer dereference
        new(log.Logger).Println: PANIC: runtime error: invalid memory address or nil pointer dereference
    --- FAIL: TestZeroLoggerUnrecovered (0.00s)
    panic: runtime error: invalid memory address or nil pointer dereference [recovered, repanicked]

### The proof (argued, not built)

`{{ isPkgInit log }} Main #() {{ RET #(); True }}`: Goose translates `new(log.Logger)` to
`GoAlloc log.Logger.ty` of its zero value; Perennial's `Code/log.lean` declares `Logger` with
`ZeroVal`, and `GeneratedProof/log.lean` gives `TypedPointsto log.Logger` and
`IntoValTypedUnderlying log.Logger log.Logger.underlying` (from `translate_types = true`), so
`wp_alloc` (`tac_wp_alloc`, `Golang/Theory/Mem.lean:244`) gives `l ↦ zero_val`, whence `l ≠ null`
(`typedPointsto` carries it, `PostLifting.lean:847`). Build the empty variadic slice
(`[∗list]` over `[]` is `emp`); apply `LoggerPrintf.wp_proof l "hi" arg [] 1 hl`, framing `l ↦ _`.
Done. `#print axioms` would show `LoggerPrintf.wp_proof` and the generic ones (no `LogDefault`
needed). The same with `Println`.

### go-craq meets the missing condition

Not a bug in go-craq: `node.New` (`node/node.go:69-74`) uses `opts.Log` or `log.Default()`, and the
kit's deployment passes no `Log` (so `std`, which `New(os.Stderr, …)` initialized). The
coordinator and the store use the package-level `log.Printf`/`Println` (proved over Perennial's
no-op model, not these axioms).

### Proposed restatement (not applied)

Tie the receiver to `Default`: `LogDefault.spec`'s post gives `isStdLogger l` (a persistent opaque
predicate of the `log` package, no laws: no cross-world risk, like zerolog's `loggerMade`), and
`LoggerPrintf.spec`/`LoggerPrintln.spec` ask `isStdLogger l` instead of `l ≠ null`. craq's node keeps
`isStdLogger n.log` in its persistent invariant where it now keeps `l ≠ null` (`opts.Log` is `nil` in
the kit; a non-nil `opts.Log` would need a spec of `log.New`, `New(w,…)` with `w` a writer whose
`Write` has a WP). Alternatively `l = std`'s value, but `std` is a trusted variable with no points-to
(`TrustedCode/log.lean`), so the opaque predicate is simpler.

## Attacks on `argOk` (all fail)

Run: `TestStdAllVerbs`, `log.Default().Printf(v, a, a, a, a)` for each verb `v` of `%v %+v %#v %s %q
%x %X %d %t %p %T %w %e %c %U %b %*d %.*s %[3]v %!`, `"%v %v %v %v"`, `""`, and each `argOk` shape
`a` (`nil`, string, int, uint64, bool, float64, `*store.Item`, `*transport.NodeMeta`, nil `*Item`,
`rpc.ServerError`, `errors.New`, `*pbcodec.Error`, `*jsoncodec.Error`, `*net.OpError` with
`Err = os.ErrDeadlineExceeded` (poll's value) and `Source` a `*TCPAddr`, `Addr` a nil `*TCPAddr`;
with `Err = net.ErrClosed` (`errNetClosing{}`); with `Err = textproto.ProtocolError`), all of them at
once, and `Println(all...)`: 397 calls, no panic. (`*net.OpError{Err: nil}`, whose `Error()` panics,
was included as a control: `catchPanic` prints `%!v(PANIC=Error method: …)` and it does not panic
either; it is not `argOk` anyway, `errAny` asks a WP of `Error()`.)

1. **Methods `fmt` calls, top level.** `handleMethods` (`print.go:614-670`): `Format` (any verb),
   `GoString` (`%#v`), `Error`/`String` (`v s x X q`). `ArgWf` types have none (`NoFmtMethods`, by
   `methodSet`); `Item`, `NodeMeta` and their pointers have no methods (`store.go:57`,
   `transport.go:64`; goose's `MethodSetIs` is empty, which craq's `go_type_set` proofs use); errors:
   `NoFmtMeth` rules out `Format`/`GoString` by implements-check (the same test `fmt` makes: a method
   of another signature is not called), and `Error()` has `errAny`'s WP. `Stringer` of an error is not
   reached (the `error` case comes first).
2. **Depth > 0.** Only reached by `printValue` when the top-level operand's methods did not handle it:
   `%#v` (all operands), or non-string verbs (`%d`, `%t`, ...) for errors. `*Item`/`*NodeMeta`:
   depth-0 pointer dereferenced, fields basic (`uint64`, `bool`, `[]byte`, `string`), no methods.
   `*errors.errorString`: one unexported field (not `CanInterface`, no method call). `*pbcodec.Error`/
   `*jsoncodec.Error`: one exported `string`. `ServerError`: a string. `*OpError`: `Op`/`Net` strings;
   interface fields at depth 2: `handleMethods` with the outer verb, so `Format`/`GoString` (excluded by
   `errLeaf`'s `NoFmtMeth`) and, only for `v s x X q`, which never reach here for an error operand
   (it is handled at depth 0 by `Error()`), nothing else; a pointer at depth ≥ 1 prints as an address
   (`fmtPointer`, no read); `errNetClosing{}` is empty; `ProtocolError` a string. So `(*TCPAddr).String`
   is never called (`%#v` prints `(*net.TCPAddr)(0xc…)`), nor `(*DeadlineExceededError).Error`.
3. **`badVerb`** (`print.go:374`): `erroring = true` makes `handleMethods` return at once, then reprints
   the same operand with `%v` by kind: the same memory as (2), no method.
4. **`%w` in `Printf`**: `wrapErrs` is false, so `badVerb` (3).
5. **`*Item` reads `Committed` without permission.** `TestItemCommittedRace`: a goroutine flips
   `item.Committed` while 200000 `Printf("%+v %#v", item, item)` run: no panic. Under `-race` (5000
   calls): three `WARNING: DATA RACE` reports and the test failed by the detector (`race detected
   during execution of test`), no panic. A racy read of a
   one-byte `bool` observes some written value (Go memory model, word-sized locations), and the read
   value only reaches the output, which the model does not observe. The other fields are `↦□`, so no
   write races with the slice header (a torn `Value` header was the dsv-fix4 worry, now closed).
6. **`*NodeMeta`**: a fraction of its points-to is held, so no one writes it during the call; it is
   given back.
7. **`errFmt`'s `OpError.Err` as `poll.ErrDeadlineExceeded`'s value**: in Go the variable is
   `&DeadlineExceededError{}` (`internal/poll/fd.go:51`), set once; `internal/poll` cannot be imported
   by user code, and `os.ErrDeadlineExceeded` is a copy, so reassigning it does not change poll's. A
   pointer without `Format`/`GoString`, printed as an address under `%#v`. No pure fact is concluded
   from the `↦□`, so the cross-world check does not apply.
8. **`textproto.ProtocolError`/`errNetClosing` at depth 2**: string/empty struct, no
   `Format`/`GoString` (`noFmt_protocolError`, `noFmt_errNetClosing`, and in Go). Fine.
9. **Nil pointers**: a nil `*Item`/`*NodeMeta` prints `<nil>` (and `argOk` asks a points-to, so
   non-nil anyway); nil `Source`/`Addr` interfaces print `<nil>`; a nil pointer in an interface field is
   printed as an address.
10. **`Error()` panics**: excluded by `errAny`'s WP; and recovered by `catchPanic` anyway, unless
    printing the panic value panics again (nested panic), which a WP of `Error()` excludes.
11. **Concurrent use of one logger**: `output` reads `prefix`/`flag` atomically, `fmt`'s `pp` comes from
    a pool per call, the buffer from `bufferPool`, the write is under `outMu`. No panic.
12. **Redirecting `std`'s output to code that panics** (`log.SetOutput`, `slog.SetDefault`,
    `(*Logger).SetOutput`): none has a body or spec reachable from a proof here (`log.toml` trusts only
    `Printf`, `Println`, `std`, `init.0`; `Dsverify/Spec/log/slog/Logger.lean` has no `SetDefault`).
    A future spec of any of them breaks these axioms unless it keeps the writer's `Write` total.
13. **`Default` returns nil**: `log.go:87` `std = New(os.Stderr, "", LstdFlags)`, never reassigned by
    `log`. Survives.
14. **Closed/broken stderr**: `Write`'s error is ignored; `EPIPE` on fd 2 is a `SIGPIPE` kill, not a
    panic. Not a counterexample.
15. **Huge widths** (`%*d` with a large `int`): `fmt` caps width/precision at 1e6 (`%!(BADWIDTH)`); no
    panic. Out-of-memory from a huge format string is not modelled anywhere (every allocation).
16. **Cross-world entailment**: none (no entailment from bare points-tos to a pure fact).

Not tried: a machine-checked Lean counterexample (the brief is read-only); a receiver obtained other
than by allocation (copying `*log.Default()` needs a points-to of `std`'s pointee, which nothing
gives).
