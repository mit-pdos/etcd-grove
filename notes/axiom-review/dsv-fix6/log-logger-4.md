# Review: `log.Default` and `*log.Logger`'s `Printf`/`Println` under `FmtVerbsOk` (dsv-fix6, fourth review)

Reviewed 2026-11-25 by the `axiom` skill, worktree `/shared/etcd-grove-dsvfix6` (branch `dsv-fix6`) at
`4c0b808f0b`, read-only (no branch, translation or Lean file: the counterexample is a Go test, run, and
a Lean proof argued below, not built); Perennial `fce59af75`; Go go1.27.3 (`src/log/log.go`,
`src/fmt/print.go`, `src/fmt/format.go`). Of the earlier reviews (`../dsv-fix4/log-logger.md`,
`log-logger-2.md`, `log-logger-3.md`) only their attack lists were read, to avoid repeating them.

## The axioms

In `Dsverify/Proof/github_com/despreston/go_craq/Craq/LogAx.lean`, their statements in
`Craq/LogHyp.lean`:

- `github_com.despreston.go_craq.LogDefault.wp_proof`:
  `{{ isPkgInit log }} log.Default #() {{ (l : Loc), RET #l; ⌜l ≠ null ∧ StdLogger l⌝ }}`.
- `github_com.despreston.go_craq.LoggerPrintf.wp_proof`: for every `l`, `msg`, `arg`, `xs`, `dq` with
  `StdLogger l` and **`FmtVerbsOk msg`**: `{{ isPkgInit log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
  l.Printf msg arg {{ RET #(); arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}`.
- `github_com.despreston.go_craq.LoggerPrintln.wp_proof`: the same without `msg` and `FmtVerbsOk`.

New since the third review: `FmtVerbsOk msg := FmtVerbsOk.go false msg = true`, a two-state scan: outside
a directive any byte but `%` is skipped; inside one (after `%`), a byte of `v s q x X d %` ends it, a byte
of `+ - # space 0-9 .` keeps it open (**in any order, any number of times**), anything else fails; the
string must not end inside a directive. `argOk`, `errPlain`/`errFmt`/`errLeaf` and `StdLogger` are as
the third review read them.

Claim in plain words: with every directive made of flag/width/precision characters followed by one of
`v s q x X d %`, the verb `fmt` applies is one of those six (or `%`), so no `argOk` operand reaches
`badVerb` with a pointer at depth ≥ 1 and nothing beyond `argOk`'s memory is read.

## Verdict: **refuted in Go** (Lean argued, not built): `LoggerPrintf.wp_proof`. `LoggerPrintln.wp_proof`, `LogDefault.wp_proof` and `StdLogger` survive (unchanged from the third review).

`FmtVerbsOk` checks the **set** of characters between `%` and the verb, not their **order**. Go's
`doPrintf` (`print.go:1007`) parses a directive in a fixed order: flags `# 0 + - space` (`:1033-1070`),
then the width digits (`parsenum`, `:1093`), then `.` and the precision digits (`:1100-1125`), and then
takes **the next character, whatever it is, as the verb** (`:1136`). A flag after a width digit, or a `.`
after the precision, is not a flag: it is the verb. So `"%1+v"` (accepted: `%`, `1`, `+` keep the
directive open, `v` closes it) is the verb `+` on the operand followed by the literal text `v`; likewise
`"%1-v"`, `"%1#v"`, `"%1 v"`, `"%.+v"`, `"%1.2.v"` (verb `.`), `"%.5 s"`, `"%3.3-d"`.

A verb `+ - # space .` is a non-method, non-pointer verb, so the third review's path is open again:
`handleMethods` calls no `Error()` for it, `printValue` dereferences the top-level `*net.OpError` and
visits its fields, the `Err` field's pointer (depth 2) goes to `fmtPointer`'s `default:` and `badVerb`,
which reprints it with `printValue(value, 'v', 0)` at depth 0 and dereferences it. `errLeaf` asks nothing
of that pointee.

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
            log.Default().Printf("%1+v", op)                  // FmtVerbsOk "%1+v"
        }
    }

Test (`/shared/tmp/axrev-log4/lx/lx_test.go`, scratch, deleted after the review; `GOTOOLCHAIN=go1.27.3`,
`go test -vet=off`). The test checks each format with a Go transcription of `FmtVerbsOk.go` first.

    TestDeref (deterministic, a log.New(os.Stdout) logger; same formatting as std):
    "%1+v"   &{%!+(string=read) %!+(string=tcp) <nil> <nil> %!+(*lx.myErr=&{map[1:2]})}v
    "%1-v"   &{%!-(string=read) ... %!-(*lx.myErr=&{map[1:2]})}v
    "%1#v"   &{%!#(string=read) ... %!#(*lx.myErr=&{map[1:2]})}v
    "%1 v"   &{%! (string=read) ... %! (*lx.myErr=&{map[1:2]})}v
    "%10v"   read tcp: myErr                                   (well-ordered: Error())
    "%.+v"   &{%!+(string=) ... %!+(*lx.myErr=&{map[1:2]})}v
    "%1.2.v" &{%!.(string=re) ... %!.(*lx.myErr=&{map[01:02]})}v
    "%.5 s"  &{%! (string=read) ... %! (*lx.myErr=&{map[00001:00002]})}s
    "%3.3-d" &{%!-(string=rea) ... %!-(*lx.myErr=&{map[001:002]})}d

    TestRace (the program above, std logger, stderr; 5 runs of the compiled test): 5/5
    fatal error: concurrent map iteration and map write
    internal/runtime/maps.(*Iter).Next(...)
    reflect.mapIterStart(...)
    reflect.(*MapIter).Next(...)
    fmt.(*pp).printValue(..., 0x76 /* 'v' */, 0x2)
    fmt.(*pp).printValue(..., 0x76, 0x1)                (badVerb's depth-0 reprint of the *myErr)
    after 33, 4, 30, 1 and 5 Printf calls

### The proof (argued, not built)

As the third review's, with the format `"%1+v"` for `"%t"`: (1) allocate `e` and its map; (2) allocate
`op`, persist its cell, `v.Err' = interface.mkOk (PointerType myErr.ty) #e`; (3) `errPlain op` from
`net.wp_OpError_Error` and `errFmt`'s `OpError` case (`errLeaf_nil` twice, `errLeaf_ptr myErr.ty #e`,
`NoFmtMeth (*myErr)` by `go_type_set`); (4) `wp_fork` with the goroutine owning `e.m ↦ mp`, `own_map mp`;
(5) the loop, `LogDefault.spec` then `LoggerPrintf.spec l "%1+v" arg [op] 1 hl hfmt`, `hfmt :
FmtVerbsOk "%1+v"` by `decide` (`FmtVerbsOk.go` is a structural recursion over a 4-byte literal: `%` →
true, `1` and `+` in the flag list → true, `v` → false, end → `true`). `#print axioms` would show
`LogDefault.wp_proof`, `LoggerPrintf.wp_proof` and the generic ones.

## Attacks that fail (the rest of the brief's list)

With the directive **well ordered** (the grammar proposed below) every case holds. A Go test
(`TestGrammar`, same scratch package) ran all 5760 combinations of 8 flag sets (`""`, each flag,
`+#`, `#0- +`), 5 width/precision choices (`""`, `5`, `.`, `.3`, `12.0`), the 6 verbs and 3 argument
counts (one operand, an `%!(EXTRA …)` second, none: `%!v(MISSING)`), on `nil`, an `int`, a `string`, a
`bool`, a string-typed error, `*Item`- and `*NodeMeta`-shaped pointers and an `*OpError` whose `Err` is
a pointer to a map and whose `Source`/`Addr` are `*TCPAddr`: no output prints a depth-≥1 pointee and no
`PANIC`.

1. **Flags in order** (`%+v`, `%#v`, `%-5.3s`, `%#x`, `% d`, `%0q`): `%#v` sets `sharpV`, so no
   `Error()`, and `printValue` reads the `*OpError` cell (`↦□`) and prints depth-≥1 pointers through
   `fmtPointer` case `'v'` (`(*T)(0x…)`); the other flags change padding and form only.
2. **`%x`/`%X`/`%q` on errors**: method verbs, `Error()` (`errAny`'s WP), output hex/quoted.
3. **`%d` on errors**: not a method verb; `printValue` reads the top-level cell, the string fields are
   `badVerb` of a non-pointer, the interface fields' pointers go to `fmtPointer` case `'d'` (an
   integer); `errNetClosing` prints `{}`, `ProtocolError`/`ServerError` a `%!d(…=…)` of a string.
4. **`*Item`/`*NodeMeta` under any of the six verbs**: top-level pointer dereferenced (the held
   points-tos; `Committed`'s racy byte read as in the second review); no pointer, map or interface
   field.
5. **`nil`**: `<nil>` under `v`, `%!s(<nil>)` etc. otherwise; nothing read.
6. **`fmt.ArgWf` values**: basic or method-free named integer/string values; at worst `badVerb` of a
   non-pointer.
7. **Argument count**: `%!d(MISSING)` reads no operand; `%!(EXTRA type=value)` prints extras with
   `printArg(arg, 'v')` (`Error()` for errors, as `Println`). `%[n]` and `*` are excluded by
   `FmtVerbsOk` (`%!(BADINDEX)` and `intFromArg`, which reads an operand as an `int`, unreachable).
8. **`%%` and a trailing `%`**: `%%` (and `%5%`) prints `%` and takes no operand; a format ending inside
   a directive is rejected (Go would print `%!(NOVERB)`, harmless anyway).
9. **Huge width/precision digits**: `parsenum` stops at 1e6 (`tooLarge`); harmless.
10. **Non-ASCII bytes after `%`**: rejected by `FmtVerbsOk`.
11. **`Println`**: every operand under `%v`; unaffected by the format. Survives.
12. **`LogDefault`, `StdLogger`**: unchanged since the third review; its analysis (opaque, global, only
   from `Default`'s post, no cross-world entailment) stands.

go-craq's own formats (`examples/dsverify/craq`: 164 `%#v`, 98 `%v`, 44 `%s`, 14 `%d`, 4 `%q`, 2 `%+v`)
are all well ordered, so `craq_remote_robust`'s proof derives nothing false about go-craq; the axiom as
stated still proves the program above safe.

## What rests on it

`craq_remote_robust` (through `logSpecs_holds`), as before.

## Proposed restatement (not applied)

Make `FmtVerbsOk` follow `doPrintf`'s order: a directive is `%`, flags `[+ - # space 0]*`, width
`[0-9]*`, optionally `.` and precision `[0-9]*`, then one of `v s q x X d %`. A phase in place of the
`Bool`:

    inductive Ph | out | flags | width | prec
    def FmtVerbsOk.go : Ph → List w8 → Bool
      | .out, [] => true
      | _, [] => false
      | .out, c :: r => if c = 37 then go .flags r else go .out r
      | ph, c :: r =>
        if c ∈ verbs then go .out r                                   -- v s q x X d %
        else if ph = .flags ∧ c ∈ [43, 45, 35, 32, 48] then go .flags r  -- + - # space 0
        else if (ph = .flags ∨ ph = .width) ∧ isDigit c then go .width r
        else if (ph = .flags ∨ ph = .width) ∧ c = 46 then go .prec r     -- .
        else if ph = .prec ∧ isDigit c then go .prec r
        else false

(`0` in `.flags` is Go's flag, a digit after it starts the width: both safe.) A `.` is always followed by
a verb byte, so Go's `i+1 < end` test before the precision holds. Every go-craq format still passes
(`decide` per literal). `LogHyp.lean`'s docstring ("only flags ..., width and precision digits and `.`
before it") should say "in this order".
