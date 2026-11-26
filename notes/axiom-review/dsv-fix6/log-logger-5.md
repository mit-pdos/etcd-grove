# go-craq's `log` axioms, round 5: `LogDefault`, `LoggerPrintf`, `LoggerPrintln`

Reviewed 2026-11-25 (independent: no earlier review of these axioms read).

- Worktree `/shared/etcd-grove-dsvfix6`, branch `dsv-fix6`, head `38dbbc96bf`.
- Perennial `/shared/perennial-fce59af75` (`Perennial/TrustedCode/log.lean`, `Perennial/Code/log.{lean,toml}`,
  `Perennial/Proof/fmt/Base.lean`, `Perennial/Golang/Defn/Interface.lean`).
- Go go1.27.3 (`fmt/print.go`, `fmt/format.go`, `log/log.go` of that toolchain).

## The axioms

`Dsverify/Proof/github_com/despreston/go_craq/Craq/LogAx.lean`:
`github_com.despreston.go_craq.LogDefault.wp_proof`, `LoggerPrintf.wp_proof`, `LoggerPrintln.wp_proof`, over
the statements of `Craq/LogHyp.lean`:

- `LogDefault.spec`: `log.Default()` returns `l` with `l ≠ null ∧ StdLogger l` (`StdLogger` opaque, no law).
- `LoggerPrintf.spec`: for `StdLogger l` and `FmtVerbsOk msg`, `l.Printf(msg, arg...)` with `arg ↦*{dq} xs`
  and `[∗list] argOk` does not panic and gives both back.
- `LoggerPrintln.spec`: the same without the format.
- `argOk v`: `nil` | `fmt.ArgWf` | `*store.Item` with `Key`, `Version`, `Value` and its bytes `↦□` (`Committed`
  unowned) | `*transport.NodeMeta` with `p ↦{dq} m` | `models_lab.errPlain` (= `errAny` ∗ `errFmt`: `NoFmtMeth`
  of the dynamic type and one of `rpc.ServerError`, `*errors.errorString` (`s ↦□`), `*pbcodec.Error`/`*jsoncodec.Error`
  (`↦□`), `*net.OpError` (`↦□`, `Source`/`Addr`/`Err` `errLeaf`, or `Err` the value of `poll.ErrDeadlineExceeded`)).

## Attacks tried

1. **Receiver.** `StdLogger` is `opaque` with no law; only `LogDefault`'s post yields it. Every other way to
   get a `*log.Logger` (`log.New`, the methods of `Logger`, `new(log.Logger)`) has no body in the model
   (`Code/log.toml`: only `Printf`, `Println`, `std`, `init.0` trusted; `Logger` an opaque type), and so do all
   writers of `std` (`log.SetOutput`, `SetFlags`, `SetPrefix`, `Default().SetOutput`): a proof cannot change
   `std.out` to a nil or panicking writer. `std` is never reassigned in `log.go`. Blocked.
2. **Format grammar vs `doPrintf`.** Compared `FmtVerbsOk.go` with go1.27.3's `doPrintf` byte by byte:
   flags (fast path: a lower-case letter after flags is the verb, the same verbs), width (`parsenum`, a `0`
   after flags is a digit in both), `.` only with something after it (`i+1 < end`; `FmtVerbsOk` rejects a
   directive ending in state 2/3), no `*`, no `[n]` (so `badArgNum`, `intFromArg`, `reordered` unreachable),
   flags after width rejected (`%1+v`), a second `.` rejected, ASCII verbs only. `tooLarge` widths make
   `parsenum` jump to the end (`%!(NOVERB)`), no argument used. `%` as verb takes no operand. Missing
   operands print `%!v(MISSING)`; extra ones `%!(EXTRA T=…)` through `printArg(…, 'v')`, which `argOk` covers
   as `%v`. No mismatch found.
3. **Per-shape, per-verb (`v s q x X d`, with `#`/`+`).**
   - `nil`, `ArgWf` (basic types, named int/string without `Format`/`GoString`/`Error`/`String`): no method,
     no memory; `badVerb` reprints a value. Huge widths/precisions only allocate.
   - `*store.Item` (no methods, no pointer/interface fields): every verb dereferences at depth 0 and reads
     the four fields; three are `↦□`, `Committed` is a racy bool read (no torn value, no crash).
   - `*transport.NodeMeta`: fraction held for the call, no writer.
   - errors under `v s q x X` (`#` without `v`): top-level `Error()` (`errAny`'s WP); under `%#v` and `%d`
     the fields are visited: at depth ≥ 1 `handleMethods` checks only `Formatter` (and `GoStringer` under
     `%#v`), excluded by `NoFmtMeth`; `%d` calls no `Error`/`String`; interface fields' pointers are at
     depth 2, printed as an address (`fmtPointer` under `v d x X`). The `badVerb` reprint of a depth-≥1
     pointer (`fmtPointer` under `s`/`q`) is unreachable: the only operands with pointer-valued fields are
     errors, whose `Error()` handles `s`/`q` at the top. Memory read is `↦□` (strings immutable).
   - `NoFmtMeth` evaluation: `typeSetContains` reads the generated `ptr_method_set` facts, which goose writes
     from `go/types` even for types-only packages (checked `math/big`, `errors`), promoted methods included; a
     type embedding `*big.Int` (Format promoted) is not `NoFmtMeth`. Blocked.
4. **Ownership, post.** The post is the pre (`arg ↦*{dq} xs`, the same `argOk`s, re-existentialized): nothing
   gained. `fmt` reads `len` elements of `arg`, retains nothing. `Logger.output` formats outside `outMu` and
   writes `os.Stderr`; a write error is ignored.
5. **Lean level.** `StdLogger` not derivable; `errPlain` needs a concrete `errFmt` shape and `errAny`;
   `argOk`'s `ArgWf` disjunct is pure but only of real interface values; no persistent fact claims a pure
   equation of an opaque function of a location (no cross-world entailment). `FmtVerbsOk` is a decidable
   Bool function, its `example`s check the cases named.
6. **Empirical.** A Go program (go1.27.3) logging 200,000 random `FmtVerbsOk` formats (flags, widths,
   precisions, all seven verbs, 1-4 directives, 0-4 operands) and `Println`s through `log.Default()`, over
   operands of every `argOk` shape: basic and named values, an `Item` whose `Committed` another goroutine
   toggles in a loop, a `NodeMeta`, `rpc.ServerError`, `errors.New`, a `pbcodec`-shaped error, real
   `*net.OpError`s (`Err` = `poll.errNetClosing{}`, `*os.SyscallError`, `*poll.DeadlineExceededError`) and
   hand-built ones (`*net.TCPAddr` fields, `textproto.ProtocolError`): exited 0.
7. **Out of scope, noted.** Through Net's trusted `(*OpError).Error` model (calls nothing where Go calls
   `Err.Error()` and `Addr.String()`; tracked separately): with `Err` an `errLeaf` pointer of a user type whose
   `Error` panics with a value whose own `Error` panics,
   `log.Default().Printf("%v", error(&net.OpError{Op: "read", Net: "tcp", Err: &Boom{}}))` dies in Go with
   `fatal error: panic while printing panic value: inner` (fmt's `catchPanic` re-panics while `panicking`).
   Likewise a cyclic `pe.Err = pe` overflows the stack. Both need `errAny` of that `OpError`, which only the
   unfaithful model makes provable (a faithful one would need `Boom.Error`'s WP; the cycle is the generic
   partial-correctness/stack-overflow gap, not these axioms'). Also not counted: SIGPIPE on a broken-pipe
   stderr (a signal exit), memory exhaustion by 10^7-wide paddings.

## Verdict

**Survives.** No program found that these three axioms admit and that panics in Go; every attack above is
blocked by `StdLogger`'s provenance, `FmtVerbsOk`'s agreement with `doPrintf`, `NoFmtMeth`, or the
persistence of what `fmt` reads. The one panic found goes through the separately-tracked `(*OpError).Error`
model, not these axioms.

Not tried: a Lean proof of anything (none needed without a Go panic); concurrent `log` use from untranslated
packages (`log/slog`) that the model does not reach.
