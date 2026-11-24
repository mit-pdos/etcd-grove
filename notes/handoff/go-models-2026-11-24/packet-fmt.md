Stage **S3 (fmt)** of the Go-model overlays plan (#692). Branch `goose-model-overlay-rest-fmt` (Perennial). Not to be landed by its author.

## What changed

**Before (lean 54a29571e):** `TrustedCode/fmt.lean`, 4114 lines: hand-pasted goose output of a Go model printer (`intVerb`, ..., `doPrintf`, `visitArg`), plus `Errorf.impl`, `Printf.impl`, `Fprintf.impl`, `Fprint.impl`, `Print.impl`, and a hand-written printer pool (`printerBuf`, `printerAlloc`, `fillArbitraryBytes`, `retire`, `retireLoop`). `trusted = ["Errorf", "Fprint", "Fprintf", "Print", "Printf"]`.

**After:** `TrustedCode/fmt.lean` is 2 primitive stubs (~30 lines). Everything else is goose output: the real `fmt` and the Go model overlay `goose/model/overlay/fmt/` (`[model] replaces = ["errorf", "Fprintf", "Printf", "pp.doPrint"]`).

### Became real translations (no trust)
- `Errorf`: Go's own (`errorf`, then `errors.New(format)` when it returns nil). Go's shortcut (no argument, no `%`) is proved too (`fmt.SprintfOut_noPct`, `fmt.fmtDirectives_noPct`).
- `Fprint`: Go's own (`newPrinter`, `p.doPrint`, `w.Write(p.buf)`, `p.free()`), over the real pool.
- `Fprintf` and `Fprint` now use the real printer, the real `ppFree` pool, and `free`. The hand-written `printerBuf`/`retire` pool model is gone (`wp_printerBuf`, `wp_retire`, `wp_retireLoop`, `wp_fillArbitraryBytes`, `wp_printerAlloc` deleted).

### Go models (trusted Go; side by side with the real Go below)
| model | why not the real Go |
|---|---|
| `errorf` | Go's body with `p.doPrintf` + `string(p.buf)` + `p.wrappedErrs` swapped for the model printer's `doPrintf(format, a, true)` and `errorfResult` (the same switch on the `%w` count). The real printer is stuck on floats, complex numbers, `%q` of an integer, `%T`/`%p`/bad verbs/`EXTRA` (`reflect.TypeOf`), and named types (`printValue`), while the `Errorf` spec admits them (`argsOk`). |
| `Fprintf` | Go's body with one line swapped (`p.doPrintf` becomes model `doPrintf` + `p.buf.writeString`). Same reason. |
| `Printf` | `Fprintf(stdout{}, ...)`. The model of `os` has no `Stdout` (os.toml, #663). `stdout.Write` is a model of `(*os.File).Write` on fd 1: `(len(b), nil)`, or `n ≤ len(b)` with `*fs.PathError{"write", "/dev/stdout", e}`, where `e` is `ErrClosed`, `ErrDeadlineExceeded`, `ErrNotPollable`, `ErrUnexpectedEOF` or an Errno in 1..4095. EPIPE may loop for ever (SIGPIPE). |
| `pp.doPrint` | Go tells strings by `reflect.TypeOf(arg).Kind()` (stuck) and `printArg` is stuck as above. The model calls each operand's methods as `printArg(·,'v')` would (`visitArg`), then appends `chooseString()`. |

The additions (`printmodel.go`: the model printer, `chooseString`, `notModelled`) carry no claim of their own.

### Primitive stubs (`TrustedCode/fmt.lean`)
```lean
def underlyingAs.impl (T : go.GoType) : val :=
  λ: "x", TypeAssertUnderlying2 T "x"
def kindIs.impl (T : go.GoType) : val :=
  λ: "y", Snd (TypeAssertUnderlying2 T "y")
```
These are reflection (`reflect.ValueOf(x).Kind()`), which is irreducible. Both stubs are stuck for any `T` other than the integer types and `string`.

**Decision D-S3a (taken): `kindIs` is a stub, not translated.** Its Go body `_, ok := underlyingAs[T](x); return ok` translates. But the translation binds `x`'s raw value, and `wp_auto` cannot step past a `let:` of a raw `val`: it needs `v.isPanic = false`, and nothing gives that for an arbitrary interface's value. `isIntKind`/`isStrKind` (through `inert`, `visitKind`) call `kindIs` on arbitrary arguments, so their specs could not be proved without a new premise.

The stub's `.impl` is exactly lean's old `TrustedCode` `kindIs`, so the trust is unchanged from lean. `underlyingAs` is still needed by `namedIntArg`/`strArg`; there, `ArgWf` gives the value's shape.

Alternative (follow-up): a semantics lemma that interface values are never panic values, then translate `kindIs`.

### Other trusted-base-adjacent changes
- `Code/fmt.toml` `imports`: adds `internal/stringslite`, `internal/gomodel`, `io/fs`, `syscall` and `internal/poll`, the model's callees.
- `Print` drops out of `trusted` and is no longer translated (stuck, like `Println`). It had no spec.

## Premise / statement changes
**None.** Unchanged statements:
- `fmt.{Errorf,Printf,Fprintf,Fprint,Sprintf,initialize'}.spec`;
- `Results.lean`'s `wp_Fprintf_bytes`, `wp_Sprintf_render`, `wp_Sprintf_walName`, `wp_Printf_argsWf`, `wp_Errorf_argsWf`;
- `argsOk`, `printArgOk`, `SprintfOut`, `errorfErr`, `writeSpec`.

`wp_Fprintf_bytes` moved from `BytesResults.lean` to `Results.lean`, because it now uses linked results. Its statement is unchanged.

The `wp_proof`s take more callee specs, which `Link.lean` passes:
- `newPrinter`, `buffer.writeString`, `pp.free`;
- `stringslite.IndexByte`;
- `gomodel.Choose`/`ChooseUint64`;
- `Printf` takes `Fprintf`'s spec.

`internal/poll`'s `isInit` gains `ErrNotPollable` (`errors.newVar`, proved in poll's `initialize'`), which `stdout.Write`'s proof loads. It is a proved strengthening; nothing in Perennial destructured that `isInit`.

## Evidence
- `go test ./goose/...` passes, including `goose/model/fmt`. These are the differential tests of the model printer and the replaced declarations against the real fmt: `TestModelSprintf`, `TestModelErrorf`, `TestModelFprintf`, `TestModelFprint`, `TestModelPrintf`, `TestModelCopy`, method-panic.
- `etc/model-tests.sh` does not run Go's own fmt tests, by design (reason recorded in the script). With `gomodel`'s Go bodies, the arbitrary output is empty, so Go's tests of `Errorf`/`Fprint(f)`/`Printf`/`Sprint` fail, and stuck points block.
- Builds (vmlake, at 2cc4ef285, with lean's fmt stage 1.5 merged): `Perennial.Proof.fmt`, `Perennial.Proof.internal.poll`, and every module that imports `Code.fmt`, `Proof.fmt.Base` or `Proof.internal.poll`. That is 185 modules, built through the leaves `Proof.{fmt,bytes,log,math.big,crypto.rand,internal.poll}`, the unittest examples and `ProgramLogic.TypeSetTest`: 2359 jobs, no errors, no new `sorry`.
- `etc/gen-link.py --check`: OK. `etc/model-tests.sh`: OK.
- R2 goose runs:
  - `underlyingAs` translates to calls of `reflect.TypeOf`/`ValueOf`, which are untranslated (no reflect semantics): irreducible.
  - `kindIs` translates; it stays a stub by decision D-S3a above.
- `#print axioms` gives `propext, Classical.choice, Quot.sound` only, for:
  - `fmt.wp_{Errorf,Printf,Fprintf,Fprint,Sprintf,initialize'}`;
  - `fmt.wp_{Fprintf_bytes,Sprintf_render,Sprintf_walName,Printf_argsWf,Errorf_argsWf}`;
  - `internal.poll.wp_initialize'`.

<details><summary>Model Go next to the real Go (etc/trusted-delta.py)</summary>

## Go model overlays (TRUSTED: model Go is reviewed as Go, rule R12)

For each replaced declaration: every behaviour of the real one (gc, linux/amd64, the pinned Go), under every use by the program and the real package, must be a behaviour of the model's translation. Compare the two sources line by line; every `gomodel.Choose`/`ChooseUint64`/`Stuck` needs a reason in the doc comment.

### Perennial/Code/fmt.toml  (package `fmt`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/fmt', replaces = ['errorf', 'Fprintf', 'Printf', 'pp.doPrint'], added_methods = []
- model files: goose/model/overlay/fmt/print.go, goose/model/overlay/fmt/printmodel.go; changed: goose/model/overlay/fmt/print.go, goose/model/overlay/fmt/printmodel.go

#### `fmt.Fprintf` (new)

Model (goose/model/overlay/fmt/print.go:53):

```go
// MODEL: Fprintf is Go's, but for one line: Go's p.doPrintf(format, a) is the model printer's
// doPrintf(format, a, false), whose string goes into p.buf (see the file comment for what the
// model printer covers and where it is stuck; TestModelFprintf checks the bytes Write receives
// and the methods called). The printer, its pool (ppFree), the one w.Write(p.buf) and p.free()
// are Go's own.
func Fprintf(w io.Writer, format string, a ...any) (n int, err error) {
	p := newPrinter()
	s, _, _ := doPrintf(format, a, false)
	p.buf.writeString(s)
	n, err = w.Write(p.buf)
	p.free()
	return
}
```

Real (`go doc -u -src fmt.Fprintf`):

```go
package fmt // import "fmt"

// Fprintf formats according to a format specifier and writes to w.
// It returns the number of bytes written and any write error encountered.
func Fprintf(w io.Writer, format string, a ...any) (n int, err error) {
	p := newPrinter()
	p.doPrintf(format, a)
	n, err = w.Write(p.buf)
	p.free()
	return
}
```

#### `fmt.Printf` (new)

Model (goose/model/overlay/fmt/print.go:67):

```go
// MODEL: Printf is Go's Fprintf(os.Stdout, format, a...) with the writer stdout{} for os.Stdout:
// the model of os has no Stdout (os.toml: its variable is not allocated, so a program that reads
// or assigns os.Stdout is stuck), and Printf always writes to the file Go opens as os.Stdout
// (descriptor 1, "/dev/stdout"); stdout.Write has every result Go's (*os.File).Write of it has.
func Printf(format string, a ...any) (n int, err error) {
	return Fprintf(stdout{}, format, a...)
}
```

Real (`go doc -u -src fmt.Printf`):

```go
package fmt // import "fmt"

// Printf formats according to a format specifier and writes to standard output.
// It returns the number of bytes written and any write error encountered.
func Printf(format string, a ...any) (n int, err error) {
	return Fprintf(os.Stdout, format, a...)
}
```

#### `fmt.errorf` (new)

Model (goose/model/overlay/fmt/print.go:36):

```go
// MODEL: errorf is Go's, but for its printer: Go formats with p.doPrintf (p.wrapErrs set) and
// reads the message from p.buf and the %w arguments from p.wrappedErrs and p.reordered; the model
// formats with the model printer, doPrintf (format, a, true), which gives the message (Go's,
// with an arbitrary suffix from the first directive it does not format) and the indices of the %w
// arguments (or that they are unknown), and builds the error from them (errorfResult) as Go's
// switch on len(p.wrappedErrs) does: errors.New, a *wrapError, a *wrapErrors (see the file
// comment for what the model printer covers and where it is stuck; TestModelErrorf compares the
// error's kind, message and wrapped errors with Go's). Go's newPrinter/free pair is left out: the
// printer and its pool (ppFree) are not observable outside fmt.
func errorf(format string, a ...any) error {
	if len(a) == 0 && stringslite.IndexByte(format, '%') == -1 {
		return nil
	}
	s, wrapped, unknown := doPrintf(format, a, true)
	return errorfResult(s, wrapped, unknown, a)
}
```

Real (`go doc -u -src fmt.errorf`):

```go
package fmt // import "fmt"

// Errorf formats according to a format specifier and returns the string as a
// value that satisfies error.
//
// If the format specifier includes a %w verb with an error operand,
// the returned error will implement an Unwrap method returning the operand.
// If there is more than one %w verb, the returned error will implement an
// Unwrap method returning a []error containing all the %w operands in the
// order they appear in the arguments.
// It is invalid to supply the %w verb with an operand that does not implement
// the error interface. The %w verb is otherwise a synonym for %v.
func Errorf(format string, a ...any) (err error) {
	// This function has been split in a somewhat unnatural way
	// so that both it and the errors.New call can be inlined.
	if err = errorf(format, a...); err != nil {
		return err
	}
	// No formatting was needed. We can avoid some allocations and other work.
	// See https://go.dev/cl/708836 for details.
	return errors.New(format)
}
// errorf formats and returns an error value, or nil if no formatting is required.
func errorf(format string, a ...any) error {
	if len(a) == 0 && stringslite.IndexByte(format, '%') == -1 {
		return nil
	}
	p := newPrinter()
	p.wrapErrs = true
	p.doPrintf(format, a)
	s := string(p.buf)
	var err error
	switch len(p.wrappedErrs) {
	case 0:
		err = errors.New(s)
	case 1:
		w := &wrapError{msg: s}
		w.err, _ = a[p.wrappedErrs[0]].(error)
		err = w
	default:
		if p.reordered {
			slices.Sort(p.wrappedErrs)
		}
		var errs []error
		for i, argNum := range p.wrappedErrs {
			if i > 0 && p.wrappedErrs[i-1] == argNum {
				continue
			}
			if e, ok := a[argNum].(error); ok {
				errs = append(errs, e)
			}
		}
		err = &wrapErrors{s, errs}
	}
	p.free()
	return err
}
```

#### `fmt.pp.doPrint` (new)

Model (goose/model/overlay/fmt/print.go:118):

```go
// MODEL: pp.doPrint prints the operands under %v, a space between two that are not strings. Go
// tells a string by reflect.TypeOf(arg).Kind() == reflect.String (reflection, which is stuck) and
// prints each with p.printArg, which is stuck on the operands of the file comment; Fprint's spec
// admits them (fmt.printArgOk). The model calls of each operand what Go's printArg calls under %v
// (visitArg: its Error() or String(), stuck where the model printer is) and appends an arbitrary
// string to p.buf, which stands for Go's output (TestModelFprint checks the calls). Fprint and
// Sprint, Go's own, print with it.
func (p *pp) doPrint(a []any) {
	for _, x := range a {
		visitArg(x, 'v', false, false)
	}
	p.buf.writeString(chooseString())
}
```

Real (`go doc -u -src fmt.pp.doPrint`):

```go
package fmt // import "fmt"

func (p *pp) doPrint(a []any) {
	prevString := false
	for argNum, arg := range a {
		isString := arg != nil && reflect.TypeOf(arg).Kind() == reflect.String
		// Add a space between two non-string arguments.
		if argNum > 0 && !isString && !prevString {
			p.buf.writeByte(' ')
		}
		p.printArg(arg, 'v')
		prevString = isString
	}
}
```

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `stdout` (type, goose/model/overlay/fmt/print.go:75, new)
- `stdout.Write` (method, goose/model/overlay/fmt/print.go:78, new); a method: of a model-only type, or a config error
- `chooseString` (func, goose/model/overlay/fmt/print.go:132, new)
- `notModelled` (func, goose/model/overlay/fmt/print.go:142, new)
- `underlyingAs` (func, goose/model/overlay/fmt/print.go:147, new); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `kindIs` (func, goose/model/overlay/fmt/printmodel.go:15, new)
- `intVerb` (func, goose/model/overlay/fmt/printmodel.go:22, new)
- `intArg` (func, goose/model/overlay/fmt/printmodel.go:40, new)
- `namedIntArg` (func, goose/model/overlay/fmt/printmodel.go:71, new)
- `anyIntArg` (func, goose/model/overlay/fmt/printmodel.go:111, new)
- `formatInt` (func, goose/model/overlay/fmt/printmodel.go:119, new)
- `formatHex` (func, goose/model/overlay/fmt/printmodel.go:140, new)
- `strArg` (func, goose/model/overlay/fmt/printmodel.go:161, new)
- `formatArg` (func, goose/model/overlay/fmt/printmodel.go:174, new)
- `hexNibble` (func, goose/model/overlay/fmt/printmodel.go:202, new)
- `quoteByte` (func, goose/model/overlay/fmt/printmodel.go:213, new)
- `quoteBytes` (func, goose/model/overlay/fmt/printmodel.go:247, new)
- `decBytes` (func, goose/model/overlay/fmt/printmodel.go:262, new)
- `hexBytes` (func, goose/model/overlay/fmt/printmodel.go:275, new)
- `joinStrings` (func, goose/model/overlay/fmt/printmodel.go:284, new)
- `formatSlice` (func, goose/model/overlay/fmt/printmodel.go:297, new)
- `isBasic` (func, goose/model/overlay/fmt/printmodel.go:340, new)
- `isIntKind` (func, goose/model/overlay/fmt/printmodel.go:353, new)
- `isStrKind` (func, goose/model/overlay/fmt/printmodel.go:361, new)
- `hasFmtMethod` (func, goose/model/overlay/fmt/printmodel.go:366, new)
- `inert` (func, goose/model/overlay/fmt/printmodel.go:384, new)
- `allInert` (func, goose/model/overlay/fmt/printmodel.go:403, new)
- `parseDirective` (func, goose/model/overlay/fmt/printmodel.go:413, new)
- `visitKind` (func, goose/model/overlay/fmt/printmodel.go:462, new)
- `callError` (func, goose/model/overlay/fmt/printmodel.go:474, new)
- `callString` (func, goose/model/overlay/fmt/printmodel.go:488, new)
- `visitArg` (func, goose/model/overlay/fmt/printmodel.go:498, new)
- `visitRest` (func, goose/model/overlay/fmt/printmodel.go:546, new)
- `doPrintf` (func, goose/model/overlay/fmt/printmodel.go:584, new)
- `errorfResult` (func, goose/model/overlay/fmt/printmodel.go:631, new)

## Trusted models vs the Go source

### Perennial/TrustedCode/fmt.lean: `underlyingAs.impl`

(the docstring quotes no Go code: the model must be read as GooseLang)

(`go doc -src fmt.underlyingAs` found nothing: fetch the source yourself)



</details>
