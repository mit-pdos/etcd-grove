# Review: `log.Default` and `*log.Logger`'s `Printf`/`Println` on `StdLogger` (dsv-fix6, third review)

Reviewed 2026-11-25 by the `axiom` skill, worktree `/shared/etcd-grove-dsvfix6` (branch `dsv-fix6`) at
`662a685a08` plus the uncommitted `Craq/LogHyp.lean` that brings `StdLogger` (the version reviewed),
read-only (no branch, translation or Lean file: the counterexample is a Go test, run, and a Lean proof
argued below, not built); Perennial `fce59af75`; Go go1.27.3 (`src/log/log.go`, `src/fmt/print.go`).
Of the earlier reviews (`../dsv-fix4/log-logger.md`, `log-logger-2.md`) only their attack lists were
read, to avoid repeating them.

## The axioms

In `Dsverify/Proof/github_com/despreston/go_craq/Craq/LogAx.lean`, their statements in
`Craq/LogHyp.lean`:

- `github_com.despreston.go_craq.LogDefault.wp_proof`:
  `{{ isPkgInit log }} log.Default #() {{ (l : Loc), RET #l; ⌜l ≠ null ∧ StdLogger l⌝ }}`.
- `github_com.despreston.go_craq.LoggerPrintf.wp_proof`: for every `l` with `StdLogger l`, `msg`, `arg`,
  `xs`, `dq`: `{{ isPkgInit log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }} l.Printf msg arg
  {{ RET #(); arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}`.
- `github_com.despreston.go_craq.LoggerPrintln.wp_proof`: the same without `msg`.

`StdLogger : Loc → Prop` is `opaque`, with no law and no parameter (not `GF`, not the semantics
instance). `argOk v`: `nil`; `fmt.ArgWf` (Perennial `Proof/fmt/Base.lean:774`); a `*store.Item` with
`Key`, `Version`, `Value`, `Value`'s bytes `↦□`; a `*transport.NodeMeta` with `p ↦{dq} m`; or
`models_lab.errPlain v` = `errAny v` (a persistent WP of `Error()`) ∗ `errFmt`
(`Net/Proof/models_lab/ErrFmt.lean`): `NoFmtMeth` and one of `rpc.ServerError`, `*errors.errorString`
(`s ↦□`), `*pbcodec.Error`/`*jsoncodec.Error` (`↦□`), `*net.OpError` `pe ↦□ v` with `v.Source'`,
`v.Addr'` `errLeaf` and `v.Err'` `errLeaf` or `poll.ErrDeadlineExceeded`'s value. **`errLeaf i`**:
`nil`, or **any** value of a type without `Format`/`GoString` that is a pointer type (nothing about the
pointee), `poll.errNetClosing` or `textproto.ProtocolError`.

Claims in plain words: `Printf` on the standard logger, with any format string and `argOk` operands,
does not panic and reads no memory beyond what `argOk` names (persistent, or a fraction held); the
claim behind `errLeaf`'s pointer case (ErrFmt.lean's header) is that "a pointer is printed as an
address (nothing read)" at depth ≥ 2.

## Verdict: **refuted in Go** (Lean argued, not built): `LoggerPrintf.wp_proof`. `LoggerPrintln.wp_proof`, `LogDefault.wp_proof` and the receiver condition `StdLogger` survive.

The false claim is `errLeaf`'s "a pointer at depth ≥ 2 is printed as an address". That holds for the
verbs `v`, `p`, `b`, `o`, `d`, `x`, `X` only. Under any other verb (`%t`, `%e`, `%f`, `%g`, `%c`,
`%U`, an unknown `%z`, ...) `fmt` **dereferences** it:

- an error operand under a non-method verb is not handled by `Error()` (`handleMethods` calls it only
  for `v s x X q`), so `printValue` (`print.go:905`) dereferences the top-level `*OpError` and visits
  its fields; the interface field `Err` reaches its pointer at depth 3;
- `printValue` sends a pointer at depth > 0 to `fmtPointer(nil, f, verb)` (`print.go:915`), whose
  `default:` (a verb other than `v p b o d x X`) calls `badVerb` (`print.go:576`);
- `badVerb` prints the value again with `printValue(value, 'v', 0)` (`print.go:387`): **depth 0**, so
  the pointer is dereferenced (`print.go:905`) and its pointee's fields are printed, maps iterated
  (`internal/fmtsort` over `reflect.MapIter`), slices' elements read (`erroring` is set, so no method is
  called).

`errLeaf` asks nothing of that pointee. A program can keep it (a map in it) owned by another goroutine
that writes it, hand the `*OpError` to `Printf("%t", op)` as `errPlain` (persistent: the `*OpError`
cell only), and Go iterates the map while the writer writes it: `fatal error: concurrent map iteration
and map write`, an unrecoverable crash the model treats as undefined behaviour.

`Println` formats every operand with `%v` (method verb for errors, `fmtPointer` case `'v'` otherwise):
not reached. go-craq's own `Printf` formats use only `%s %v %+v %#v %d` (examples/dsverify/craq), none
of which dereferences a depth-≥1 pointer: craq meets the missing condition; the statement does not say
it.

### The program (Go, run)

    type myErr struct{ m map[int]int }

    func (e *myErr) Error() string { return "myErr" }

    func Main() {
        e := &myErr{m: map[int]int{}}
        op := &net.OpError{Op: "read", Net: "tcp", Err: e}   // errPlain: op ↦□, Err errLeaf (a pointer)
        go func() {                                           // owns e.m
            for i := 0; ; i++ {
                e.m[i%64] = i
            }
        }()
        for i := 0; i < 2000000; i++ {
            log.Default().Printf("%t", op)
        }
    }

Test (`/shared/tmp/axrev-log3/lx/lx_test.go`, scratch, deleted after the review; `GOTOOLCHAIN=go1.27.3`,
`go test -vet=off`: vet rejects `%t` of a `*net.OpError`, the compiler does not):

    TestDeref (deterministic, no race; the logger prints to stdout):
    &{%!t(string=read) %!t(string=tcp) <nil> <nil> %!t(*lx.myErr=&{map[1:2 3:4]})}
    &{%!e(string=read) %!e(string=tcp) <nil> <nil> %!e(*lx.myErr=&{map[1:2 3:4]})}
    &{%!c(string=read) ...  %!c(*lx.myErr=&{map[1:2 3:4]})}      (%U the same)
    read tcp: myErr                                              (%s, %v: Error())
    &net.OpError{..., Err:(*lx.myErr)(0x323be82180a8)}           (%#v: an address)
    &{%!d(string=read) %!d(string=tcp) <nil> <nil> 55232878969000}  (%d: an address as an integer)

    TestRace (the program above, std logger, 5 runs): 5/5
    fatal error: concurrent map iteration and map write
    goroutine 8 [running]:
    internal/runtime/maps.fatal(...)
    internal/runtime/maps.(*Iter).Next(...)
    reflect.mapIterStart(...)                 (from fmt's printValue of the dereferenced *myErr)
    after 3, 22, 7, 4 and 33 Printf calls

The same dereference reads `Source`'s and `Addr`'s pointees (any `NoFmtMeth` pointer is `errLeaf`): a
pointee with a slice header written concurrently is a torn read of a slice, an out-of-bounds read.

### The proof (argued, not built)

`{{ isPkgInit pkg }} Main #() {{ RET #(); True }}`, from `LogDefault.spec` and `LoggerPrintf.spec`:

1. `e := &myErr{...}`: `wp_alloc` and a map `make` (Perennial's map specs): `e.m ↦ mp`, `own_map mp`.
2. `op := &net.OpError{...}`: `wp_alloc`, then persist the cell (`pe ↦□ v`), with `v.Err' =
   interface.mkOk (PointerType myErr.ty) #e`, `v.Source' = v.Addr' = interface.nil`.
3. `errPlain (op)`: `errAny` from `net.wp_OpError_Error pe v` (Net's trusted model of `(*OpError).Error`,
   which reads only `pe ↦□ v`; as `ServeLoopLemmas.opError_argOk` does) and `go_type_set` for
   `typeSetContains (*OpError) error`; `errFmt`: `noFmt_opError`, the `OpError` case with
   `errLeaf_nil` twice and `errLeaf_ptr myErr.ty #e` (`NoFmtMeth (*myErr)` by `go_type_set`: its method
   set is `{Error}`).
4. `go func`: `wp_fork`, giving the goroutine exclusive ownership of the map (`e.m ↦ mp`, `own_map mp`):
   no one else may touch it, which is what Go's `fmt` violates; its infinite loop of map stores has a WP with that loop invariant.
5. The loop: `LogDefault.spec` gives `l` with `StdLogger l`; build the one-element variadic slice
   `[op]`; `LoggerPrintf.spec l "%t" arg [op] 1 hl` with `argOk op` from (3) (`errPlain` is persistent,
   so every iteration has it). Loop invariant `□ errPlain op`.

`#print axioms` would show `LogDefault.wp_proof`, `LoggerPrintf.wp_proof` and the generic ones (Net's
`OpError.Error.impl` is trusted code, a definition, not an axiom). No `sorry`, no other axiom.

### What rests on it

`craq_remote_robust` (through `logSpecs_holds`). Its proof uses only go-craq's formats (verbs `s v d`,
flags `+ #`), so the result's proof is not unsound in what it derives about go-craq; but the axiom, as
stated, proves a panicking program safe.

### Proposed restatement (not applied)

Either suffices; (A) is the smaller change and matches what go-craq does:

- **(A) A format premise on `Printf`**: `FmtVerbsOk msg`: every directive of `msg` ends in one of
  `v s q x X d` (any flags, width and precision digits; no `*`, no `%[n]`), and `%%`. Under these
  verbs no `argOk` shape reaches `badVerb` with a pointer: errors are handled by `Error()` (`v s q x X`),
  or by `printValue` whose depth-≥1 pointers go to `fmtPointer` case `'d'` (an integer) or `'v'` (an
  address); `*Item`/`*NodeMeta` have no pointer field; a string/bool/integer under `%d`/`%x` is
  `badVerb` of a non-pointer (`%!d(string=…)`), no dereference. go-craq's every format meets it (a
  `decide` on each literal). `Println` needs nothing.
- **(B) `errLeaf`'s pointer case asks the pointee persistent and pointer-free** (or list the concrete
  types craq meets: `*net.TCPAddr` with `IP` bytes `↦□`, `*os.SyscallError`, `*poll.DeadlineExceededError`)
  — wider in `msg`, but every producer of an `errPlain` `*OpError` (Net's dial/read errors) must then
  carry those points-tos.

ErrFmt.lean's header ("a pointer is printed as an address (nothing read)") needs the verb qualifier in
either case.

## `StdLogger`: can it be had other than from `log.Default()`? (no)

The brief's question. `StdLogger` is a pure, global, law-free `Prop` (no `GF`, no semantics instance,
no heap): the shape the cross-world check (SKILL.md step 3) looks at.

1. **No law, no unfolding.** `opaque` with no definition the kernel can unfold (its `Inhabited`
   witness is hidden); `grep StdLogger`: only `LogHyp.lean`'s three specs and craq's node, which take
   it as a hypothesis or keep it in `Node/Defs.lean`'s invariant (`⌜… ∧ StdLogger lg⌝`, from
   `Default`). Nothing proves it or derives it from another fact.
2. **Cross-world (entailment).** No entailment concludes `StdLogger` from points-tos: it appears only in
   a WP's postcondition, so `crossWorld` (a fresh heap with chosen cells, `bupd_soundness`) does not
   apply.
3. **Cross-execution / cross-instance.** To have `StdLogger L` for a chosen `L` as a Lean fact, a proof
   would run `log.Default` in some execution it exhibits and read the post off adequacy. `log.Default`
   is untranslated (no `FuncUnfold` in Perennial's `Code/log.lean`: its body is the semantics'
   `functions "log.Default" []`, unknown), so no execution of it can be exhibited in the abstract
   instance; a concrete instance where it returns `L` would need a full `go.Semantics` (Perennial
   builds none; every result is over an abstract instance). Not derivable today. It is the one
   residual risk: `StdLogger` being instance- and execution-independent, any future concrete
   `go.Semantics` with a `log.Default` body returning a chosen location would make it true of that
   location for good. A per-execution form (a persistent `IProp GF` predicate, or a fact tied to
   `isPkgInit log`'s ghost state) would not have it.
4. **Within one execution.** A program holds `std`'s location only through `Default`; any other
   `*Logger` (`new(log.Logger)`, `&log.Logger{}`, `log.New(...)`, a copy `*p = *log.Default()`, which
   needs a points-to of `std`'s pointee that nothing gives) is a different location, and the proof has
   no `StdLogger` of it. Pointer equality cannot help: the proof cannot learn a fresh allocation equals
   `std`.
5. **Across machines and crashes** (`Robust`'s `DistCrashNstepsBelow`): a `Loc` cannot be sent over the
   network (values are marshalled; Go cannot make a pointer from an integer without `unsafe`, which
   Goose does not translate) nor survive a crash in memory; a restarted machine's `new(log.Logger)` at
   the old `std`'s address is a location the proof cannot identify.
6. **Changing `std` after `Default`**: `log.SetOutput`, `(*Logger).SetOutput`, `SetFlags`,
   `slog.SetDefault` have no spec or body reachable from a proof (`log.toml` trusts only `Printf`,
   `Println`, `std`, `init.0`); a store into `*l` needs a points-to nothing gives. (A future spec of any
   of them must keep `out`'s `Write` total, or these axioms break.)

`LogDefault.wp_proof` (returns non-nil `std`, `log.go:87`, never reassigned) survives as in the second
review.

## Other attacks tried (fail)

1. **`Println`'s operands, every shape** (only `%v`): covered by the second review's 397 calls; the
   depth-≥1 pointer reaches `fmtPointer` case `'v'`. Survives.
2. **`fmt.ArgWf`'s values** (`IsBasicType`, named integer/string types with `NoFmtMethods`, checked by
   name in `methodSet`, so a method named `Error`/`String` of any signature excludes the type; pointer
   methods are not in a value type's method set, and `fmt` checks the value's dynamic type): no method
   called, no pointer; `%t`/`%e` on them is `badVerb` of a non-pointer. Survives.
3. **`*Item`/`*NodeMeta` under bad verbs** (`%t`, `%e`): fields `string`, `uint64`, `bool`, `[]byte`, no
   pointer, no map: `badVerb` of each, reading only the held memory. Survives.
4. **`errorString`, `pbcodec`/`jsoncodec` `Error`, `ServerError` under bad verbs**: a string field or a
   string: no dereference. `poll.ErrDeadlineExceeded`'s value: a pointer to an empty struct; its
   dereference reads nothing. Survives.
5. **The dereferenced pointee's own pointers**: printed by `printValue(…, 'v', 0)` at depth ≥ 1 through
   `fmtPointer` case `'v'` (an address): only one level is read. (The finding needs only that level.)

## Related finding, outside these axioms: Net's `(*OpError).Error` model

`Net/TrustedCode/net.lean:664` `OpError.Error.impl` returns `e.Op ++ s1 ++ ": " ++ s2` for arbitrary
`s1`, `s2` and calls nothing; Go's `(*OpError).Error` (`net.go`) calls `e.Source.String()`,
`e.Addr.String()` and `e.Err.Error()` of whatever the program stored. So `errAny` of any `*OpError`
(`wp_OpError_Error`) holds whatever `Err`'s `Error()` does. Run: with `Err` a `*wErr` whose `Error()`
writes a map another goroutine writes, `log.Default().Printf("%v", op)` dies `fatal error: concurrent
map writes` (3/3); so would `_ = op.Error()` alone, with no `log` call. That refutes Net's trusted
model, not these axioms' statement (they inherit it through `errAny`), and reaches `Println` too. Not
reviewed further here; it needs its own review of `Net/TrustedCode/net.lean` (the model is faithful only
when `Source`, `Addr` and `Err` are values whose methods are net's own or proved safe: a premise its
specs would carry, or `wp_OpError_Error` asking `errAny`/a `String` WP of the fields).

Not tried: a machine-checked Lean counterexample (the brief is read-only); a concrete `go.Semantics`
instance to test (3) above.
