# S4 part rt: runtime, os, syscall, log (+ internal/gomodel ChooseString/ChooseStrings)

Branch `goose-model-overlay-rest-rt` (Perennial). `crypto/rand` (D3) is **not** in it: parked,
unproved, on `goose-model-overlay-rest-rt-rand` (see "Open").

## Per package
- **internal/gomodel**: `ChooseString`, `ChooseStrings`: translated Go (loops over `Choose`/
  `ChooseUint64`), with specs and proofs. They replace the hand-written Lean
  `syscall.arbitraryStrings` (pasted goose output). Standalone commit for fmt:
  `goose-model-overlay-rest-gomodel-choosestring` 1ba3cdff2.
- **runtime**: Go models `Gosched` (empty: `checkTimeouts` is empty on Linux, `mcall(gosched_m)` is asm
  plus the scheduler), `buildVersion` (`= gomodel.ChooseString()`: the linker sets it; the real
  translation gives `""`), `Frames.Next` (arbitrary frames; `new(Func)` under Choose; goose rejects
  the real one: `inc or dec statement with unsupported type uintptr`). `callers` stays **trusted**:
  `callers.impl := λ skip pcbuf, callersModel skip pcbuf`, where `callersModel` is translated Go added by the
  overlay (writes an arbitrary prefix). Why not a replacement: under gc its body (Choose = false)
  finds no frame, and `testing.callerName` panics ("zero callers found"), so every
  `etc/model-tests.sh` run failed, for every unit, since runtime's overlay is always included.
  The real `callers` reaches `getg`/`sys.GetCallerPC` (intrinsics). Deleted: 213 lines of
  `TrustedCode/runtime.lean` (pasted goose output); 1 trusted one-liner left.
- **os**: `runtime_args.impl` = one call of `gomodel.ChooseStrings` (was `syscall.arbitraryStrings`).
- **syscall**: `init.0`, `Getrlimit`, `setrlimit`, `adjustFileLimit`, `errnoErr`, `origRlimitNofile`
  are now **real** translations, over a Go model of `prlimit1` (RawSyscall6 of
  `uintptr(unsafe.Pointer(..))`: reads `*newlimit`, may write arbitrary limits to `*old`, returns
  `errnoErr` of an arbitrary errno). The old Lean `init.0` was a no-op. `runtime_envs.impl` = one call
  of `ChooseStrings`. Deleted: `arbitraryStrings` (about 40 lines of pasted goose output) and the
  no-op `init.0`.
- **log**: Go models `Printf`/`Println` (`if Choose() { fmt.Fprintf(modelDiscard{}, ...) }`: they run fmt's
  formatting, and so the arguments' `String`/`Error` methods, which the old no-op Lean skipped. That was
  unsound, since those methods have effects) and `init.0` (empty: it writes `log/internal`, which only
  the untranslated slog reads). `std.init` stays trusted, as before.
- **internal/synctest**: unchanged (`Run`/`IsInBubble` stay trusted, with gc's real bodies).

## New primitives
None. The trusted additions are `runtime.callers.impl` (one line, above). `os.runtime_args.impl` and
`syscall.runtime_envs.impl` became one-line calls of translated Go.

## Premise and statement changes
None. The spec statements are unchanged. Callee hypotheses were added to `wp_proof`s:
`runtime.callers`/`Frames.Next` take `Choose`/`ChooseUint64`/`ChooseString`, `log.Printf` takes
`Choose`/`Fprintf`/`modelDiscard.Write`, and `syscall.initialize'` takes `atomic`/`gomodel` init,
`ChooseStrings`/`Choose`/`ChooseUint64` and `atomic.Pointer.Store`. `math/big`: no change on this branch.

## Evidence
- `etc/model-tests.sh`: ok. The strings/errors/bytes runs now include runtime's models. With the choice
  overlay (runtime, syscall, log):
  - `syscall` runs without `TestPrlimitFileLimit` (the model leaves the limit unchanged).
  - `log` runs without `TestAll` (no output) and `TestCallDepth`/`ExampleLogger`/`ExampleLogger_Output`
    (`Lshortfile` gets empty file and line from `Frames.Next`'s gc body).
  - `os`, `sort`, `runtime/debug` run in full.
  - `runtime`'s own tests are not run.
- `go test ./goose/...`: ok.
- VM builds: every touched `Link` (internal/gomodel, runtime, os, syscall, log, internal/synctest,
  math/big, crypto/rand). Full `etc/lean-ci.sh`: one FAIL, `Proof.os.Models` (a no-progress `wp_auto`). I fixed it in d5b625198, but did not rebuild it: the rerun was stopped at the lead's request. The run also had many SKIPs; I did not check why.
- review-trusted: I did a self-review only (no adversary subagent: the takeover rules forbid spawning one).
  I compared every replaced declaration line by line with the real Go (`trusted-delta.py` output
  below). One finding, fixed: `callers` as a replacement broke gc programs, so it became trusted over
  `callersModel`.

## `#print axioms`
`propext, Classical.choice, Quot.sound` for every result: `runtime.{wp_callers, wp_Callers,
wp_CallersFrames, Frames.wp_Next, wp_Gosched, wp_Version}`, `syscall.{wp_initialize', wp_Exit}`,
`os.wp_Exit`, `log.{wp_Printf, wp_initialize', modelDiscard.wp_Write}`,
`internal.gomodel.{wp_ChooseString, wp_ChooseStrings}`.

## Open
1. **D3, crypto/rand.Int real**: parked on `goose-model-overlay-rest-rt-rand` (c6d26e15a). It has the
   translation and the models, but it does not build: there are no proofs. It also needs:
   - drbg's `init.0` (the FIPS self-test `fips140.CAST`, which is fatal under GODEBUG `failfipscast`)
     needs a model;
   - `drbgPool` needs a `[[skip]]` entry;
   - the specs and proofs of math/big, `reader.Read` and crypto/rand (about 1–1.5k lines).
   See `gmr-rt/resume.md`.
2. **GODEBUG setenv hooks** (the lead's decision; not done, as the lead asked). In Perennial's syscall,
   add to `trusted` in `Perennial/Code/syscall.toml`, with `.impl`s in
   `Perennial/TrustedCode/syscall.lean`:
   - `runtimeSetenv(k, v)` and `runtimeUnsetenv(k)`: stuck when `k == "GODEBUG"`, no-op otherwise;
   - `runtimeClearenv(env)`: always stuck, or stuck when `env` has `"GODEBUG"`.

   All three are declared in `syscall.go`, with no Go body; the runtime provides them in
   `runtime.go` and `runtime_clearenv.go`. Today they are names only: their callers `Setenv`,
   `Unsetenv` and `Clearenv` are not translated, so nothing can reach them. A draft
   (`λ: "k" "v", if: "k" =⟨go.string⟩ #(go!"GODEBUG") then FuncResolve internal.gomodel.Stuck [] #() #()
   else #()`) was written and then reverted, unbuilt.
3. **review-trusted**: I did a self-review only, with no adversary subagent. It should get a review
   with one.

<details><summary>trusted-delta: models next to the real Go</summary>

```
## Go model overlays (TRUSTED: model Go is reviewed as Go, rule R12)

For each replaced declaration: every behaviour of the real one (gc, linux/amd64, the pinned Go), under every use by the program and the real package, must be a behaviour of the model's translation. Compare the two sources line by line; every `gomodel.Choose`/`ChooseUint64`/`Stuck` needs a reason in the doc comment.

### Perennial/Code/internal/gomodel.toml  (package `internal/gomodel`)

- `[model]` (unchanged): dir = 'goose/model/overlay/internal/gomodel', replaces = ['*'], added_methods = []
- model files: goose/model/overlay/internal/gomodel/choose.go, goose/model/overlay/internal/gomodel/gomodel.go; changed: goose/model/overlay/internal/gomodel/choose.go
- whole-package model (`replaces = ["*"]`): every real file is dropped; every model declaration that is not a primitive stub carries the R12 claim against the real declaration of the same name, if any

#### `internal/gomodel.ChooseString` (new)

Model (goose/model/overlay/internal/gomodel/choose.go:3):

```go
// ChooseString is an arbitrary string: every string is a result (and the loop
// may also not terminate). It is translated Go over Choose and ChooseUint64,
// not a primitive: a model uses it where Go's value is outside what the model
// tracks (a linker-set string, a symbol name, a command-line argument). In Go
// it is "".
func ChooseString() string {
	var b []byte
	for Choose() {
		b = append(b, byte(ChooseUint64()))
	}
	return string(b)
}
```

NOTE: the doc comment does not start with `MODEL:` (R12).

(no real declaration found by `go doc`: a model-only helper, or an added package)

#### `internal/gomodel.ChooseStrings` (new)

Model (goose/model/overlay/internal/gomodel/choose.go:16):

```go
// ChooseStrings is an arbitrary []string (nil or not, of any length, every
// element any string). It is translated Go over Choose and ChooseString. In Go
// it is nil.
func ChooseStrings() []string {
	var a []string
	for Choose() {
		a = append(a, ChooseString())
	}
	return a
}
```

NOTE: the doc comment does not start with `MODEL:` (R12).

(no real declaration found by `go doc`: a model-only helper, or an added package)

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `Choose` (func, goose/model/overlay/internal/gomodel/gomodel.go:12, unchanged); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `ChooseUint64` (func, goose/model/overlay/internal/gomodel/gomodel.go:17, unchanged); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `Stuck` (func, goose/model/overlay/internal/gomodel/gomodel.go:22, unchanged); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `StartRead` (func, goose/model/overlay/internal/gomodel/gomodel.go:33, unchanged); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)

### Perennial/Code/log.toml  (package `log`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/log', replaces = ['Printf', 'Println', 'init.0'], added_methods = []
- model files: goose/model/overlay/log/log.go; changed: goose/model/overlay/log/log.go

#### `log.Printf` (new)

Model (goose/model/overlay/log/log.go:12):

```go
// MODEL: Printf is std.output(0, 2, func(b []byte) []byte { return
// fmt.Appendf(b, format, v...) }). The standard logger std is not translated
// (its initializer is New(os.Stderr, "", LstdFlags), and os.Stderr is not a
// File in the model: perennial#663), nor is any function that changes it
// (SetOutput, SetFlags, SetPrefix, Default, Logger's setters), so in every
// execution of the model std is as New made it: flags LstdFlags, no prefix,
// output os.Stderr. Its output method then:
//   - returns at once if the output is io.Discard (l.isDiscard), which needs
//     a SetOutput no execution reaches; the model has both outcomes anyway
//     (gomodel.Choose: it formats or does nothing);
//   - reads the clock (time.Now), the prefix and the flags (atomic loads), and
//     with LstdFlags not the caller's file and line: no effect;
//   - takes a buffer from bufferPool, formats the date and time into it, and
//     calls the closure, which formats the arguments as fmt.Appendf does:
//     fmt's printer and doPrintf, which call the arguments' Error, String and
//     Format methods, the only effects on the program. The model formats them
//     with fmt.Fprintf, which runs the same newPrinter, doPrintf and free;
//   - appends a newline, takes std.outMu (held only by output, never while
//     the arguments' methods run) and writes the bytes to standard error,
//     ignoring the result: an effect outside the program, which the model
//     drops, as it drops Fprintf's bytes (modelDiscard).
//
// Neither can panic other than through the arguments' methods.
func Printf(format string, v ...any) {
	if gomodel.Choose() {
		fmt.Fprintf(modelDiscard{}, format, v...)
	}
}
```

Real (`go doc -u -src log.Printf`):

```go
package log // import "log"

// Printf calls Output to print to the standard logger.
// Arguments are handled in the manner of [fmt.Printf].
func Printf(format string, v ...any) {
	std.output(0, 2, func(b []byte) []byte {
		return fmt.Appendf(b, format, v...)
	})
}
```

#### `log.Println` (new)

Model (goose/model/overlay/log/log.go:41):

```go
// MODEL: Println is Printf's model (see there) with fmt.Appendln(b, v...) in
// place of Appendf: the model formats the arguments with fmt.Fprintln, which
// runs the same newPrinter, doPrintln and free.
func Println(v ...any) {
	if gomodel.Choose() {
		fmt.Fprintln(modelDiscard{}, v...)
	}
}
```

Real (`go doc -u -src log.Println`):

```go
package log // import "log"

// Println calls Output to print to the standard logger.
// Arguments are handled in the manner of [fmt.Println].
func Println(v ...any) {
	std.output(0, 2, func(b []byte) []byte {
		return fmt.Appendln(b, v...)
	})
}
```

#### `log.init.0` (new)

Model (goose/model/overlay/log/log.go:58):

```go
// MODEL: log's init function stores a closure into
// log/internal.DefaultOutput, the output of log/slog's default handler; it
// cannot panic. log/slog and log/internal are not translated, so no execution
// of the model reads that variable, and the model does nothing.
//
//gomodel:replace init.0 "internal.DefaultOutput = func(pc uintptr, data []byte) error {"
func init() {
}
```

(`go doc` cannot show `init.0`, the real package's init of that number in goose's numbering: read it in the real source. The marker quotes its first body line: "internal.DefaultOutput = func(pc uintptr, data []byte) error {")

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `modelDiscard` (type, goose/model/overlay/log/log.go:50, new)
- `modelDiscard.Write` (method, goose/model/overlay/log/log.go:54, new); a method: of a model-only type, or a config error

### Perennial/Code/runtime.toml  (package `runtime`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/runtime', replaces = ['Gosched', 'buildVersion', 'Frames.Next'], added_methods = []
- model files: goose/model/overlay/runtime/extern.go, goose/model/overlay/runtime/proc.go, goose/model/overlay/runtime/symtab.go, goose/model/overlay/runtime/traceback.go; changed: goose/model/overlay/runtime/extern.go, goose/model/overlay/runtime/proc.go, goose/model/overlay/runtime/symtab.go, goose/model/overlay/runtime/traceback.go

#### `runtime.Frames.Next` (new)

Model (goose/model/overlay/runtime/symtab.go:8):

```go
// MODEL: ci.Next() is the next frame of the program counters ci.callers,
// symbolized through the binary's tables (findfunc, the inlining tree, the
// cgo symbolizer; goose: "inc or dec statement with unsupported type
// uintptr", symtab.go:131), and whether another one follows. Go reads and
// writes *ci, so a nil ci panics (nil dereference) and a concurrent call on
// the same Frames races; the model's load and store of ci.callers do both.
// The model leaves *ci unchanged, where Go advances it, which no caller
// observes (the fields are unexported). It does not read the words
// ci.callers points to, which Go does (ci.callers[0]): a concurrent write to
// them races in Go and not in the model, but Go reads them only to look them
// up (any value gives some frames, a garbage one is skipped), and the model's
// frames are arbitrary anyway, so no outcome of that race is missing.
// Every exported field of the frame and more is arbitrary, a superset of
// what Go returns (goose/model/runtime/callers_test.go: a nil Func for a frame
// of a function inlined into its caller, Function/File/Line of the call
// sites, the zero frame with more false once the frames are exhausted). A
// non-nil Func is new(Func): Func is zero-size, and the semantics allocates a
// zero-size value at an arbitrary non-null address that owns no memory, so
// two results can be equal or not and a proof can read nothing through it, as
// with Go's pointers into the binary's tables. startLine and Entry are
// arbitrary too; funcInfo stays zero (unexported, read only by the runtime).
func (ci *Frames) Next() (frame Frame, more bool) {
	ci.callers = ci.callers
	frame.PC = uintptr(gomodel.ChooseUint64())
	if gomodel.Choose() {
		frame.Func = new(Func)
	}
	frame.Function = gomodel.ChooseString()
	frame.File = gomodel.ChooseString()
	frame.Line = int(gomodel.ChooseUint64())
	frame.startLine = int(gomodel.ChooseUint64())
	frame.Entry = uintptr(gomodel.ChooseUint64())
	more = gomodel.Choose()
	return
}
```

Real (`go doc -u -src runtime.Frames.Next`):

```go
package runtime // import "runtime"

// Next returns a [Frame] representing the next call frame in the slice
// of PC values. If it has already returned all call frames, Next
// returns a zero [Frame].
//
// The more result indicates whether the next call to Next will return
// a valid [Frame]. It does not necessarily indicate whether this call
// returned one.
//
// See the [Frames] example for idiomatic usage.
func (ci *Frames) Next() (frame Frame, more bool) {
	for len(ci.frames) < 2 {
		// Find the next frame.
		// We need to look for 2 frames so we know what
		// to return for the "more" result.
		if len(ci.callers) == 0 {
			break
		}
		var pc uintptr
		if ci.nextPC != 0 {
			pc, ci.nextPC = ci.nextPC, 0
		} else {
			pc, ci.callers = ci.callers[0], ci.callers[1:]
		}
		funcInfo := findfunc(pc)
		if !funcInfo.valid() {
			if cgoSymbolizerAvailable() {
				// Pre-expand cgo frames. We could do this
				// incrementally, too, but there's no way to
				// avoid allocation in this case anyway.
				ci.frames = append(ci.frames, expandCgoFrames(pc)...)
			}
			continue
		}
		f := funcInfo._Func()
		entry := f.Entry()
		// We store the pc of the start of the instruction following
		// the instruction in question (the call or the inline mark).
		// This is done for historical reasons, and to make FuncForPC
		// work correctly for entries in the result of runtime.Callers.
		// Decrement to get back to the instruction we care about.
		//
		// It is not possible to get pc == entry from runtime.Callers,
		// but if the caller does provide one, provide best-effort
		// results by avoiding backing out of the function entirely.
		if pc > entry {
			pc--
		}
		// It's important that interpret pc non-strictly as cgoTraceback may
		// have added bogus PCs with a valid funcInfo but invalid PCDATA.
		u, uf := newInlineUnwinder(funcInfo, pc)
		sf := u.srcFunc(uf)
		if u.isInlined(uf) {
			// Note: entry is not modified. It always refers to a real frame, not an inlined one.
			// File/line from funcline1 below are already correct.
			f = nil

			// When CallersFrame is invoked using the PC list returned by Callers,
			// the PC list includes virtual PCs corresponding to each outer frame
			// around an innermost real inlined PC.
			// We also want to support code passing in a PC list extracted from a
			// stack trace, and there only the real PCs are printed, not the virtual ones.
			// So check to see if the implied virtual PC for this PC (obtained from the
			// unwinder itself) is the next PC in ci.callers. If not, insert it.
			// The +1 here correspond to the pc-- above: the output of Callers
			// and therefore the input to CallersFrames is return PCs from the stack;
			// The pc-- backs up into the CALL instruction (not the first byte of the CALL
			// instruction, but good enough to find it nonetheless).
			// There are no cycles in implied virtual PCs (some number of frames were
			// inlined, but that number is finite), so this unpacking cannot cause an infinite loop.
			for unext := u.next(uf); unext.valid() && len(ci.callers) > 0 && ci.callers[0] != unext.pc+1; unext = u.next(unext) {
				snext := u.srcFunc(unext)
				if snext.funcID == abi.FuncIDWrapper && elideWrapperCalling(sf.funcID) {
					// Skip, because tracebackPCs (inside runtime.Callers) would too.
					continue
				}
				ci.nextPC = unext.pc + 1
				break
			}
... (38 more lines)
```

#### `runtime.Gosched` (new)

Model (goose/model/overlay/runtime/proc.go:6):

```go
// MODEL: Gosched yields the processor. Go's body is checkTimeouts(), empty on
// linux (lock_futex.go), and mcall(gosched_m), which switches to the g0 stack
// (assembly, asm_amd64.s) and puts the goroutine back on the global run queue
// (the scheduler, which the semantics does not model). The model returns: a
// yield after which the same goroutine runs on is a schedule Go also has, and
// the semantics' interleaving gives every other one. Neither can panic.
func Gosched() {
}
```

Real (`go doc -u -src runtime.Gosched`):

```go
package runtime // import "runtime"

// Gosched yields the processor, allowing other goroutines to run. It does not
// suspend the current goroutine, so execution resumes automatically.
//
//go:nosplit
func Gosched() {
	checkTimeouts()
	mcall(gosched_m)
}
```

#### `runtime.buildVersion` (new)

Model (goose/model/overlay/runtime/extern.go:8):

```go
// MODEL: buildVersion is the Go tree's version string at build time, the
// string Version returns. Go's declaration has no initializer: the linker
// writes the value into the binary (cmd/link/internal/ld/main.go:
// addstrdata1(ctxt, "runtime.buildVersion="+buildVersion), the toolchain's
// version, plus "-X:<experiments>" for a non-default GOEXPERIMENT), schedinit
// replaces an empty value by "unknown", and `-ldflags=-X
// runtime.buildVersion=<s>` sets any string s, invalid UTF-8 included
// (goose/model/runtime/version_test.go). Nothing writes it after that (a
// go:linkname pull of it is refused by the linker since Go 1.23). The model
// initializes it to an arbitrary string (gomodel.ChooseString, which can be
// every string): every value Go can have is one of its values. The
// translation of the real declaration would be "", more defined than Go.
var buildVersion = gomodel.ChooseString()
```

Real (`go doc -u -src runtime.buildVersion`):

```go
package runtime // import "runtime"

// buildVersion is the Go tree's version string at build time.
//
// If any GOEXPERIMENTs are set to non-default values, it will include
// "X:<GOEXPERIMENT>".
//
// This is set by the linker.
//
// This is accessed by "go version <binary>".
var buildVersion string
```

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `callersModel` (func, goose/model/overlay/runtime/traceback.go:10, new)

### Perennial/Code/syscall.toml  (package `syscall`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/syscall', replaces = ['prlimit1'], added_methods = []
- model files: goose/model/overlay/syscall/prlimit.go; changed: goose/model/overlay/syscall/prlimit.go

#### `syscall.prlimit1` (new)

Model (goose/model/overlay/syscall/prlimit.go:9):

```go
// MODEL: prlimit1 is the prlimit64 system call: Go's body is
// RawSyscall6(SYS_PRLIMIT64, uintptr(pid), uintptr(resource),
// uintptr(unsafe.Pointer(newlimit)), uintptr(unsafe.Pointer(old)), 0, 0) and,
// for a non-zero errno, errnoErr(e1). The conversions of pointers to uintptr
// and the system call (assembly) have no semantics. The kernel reads
// *newlimit if newlimit is non-nil, writes *old if old is non-nil and the call
// succeeds, and returns 0 or an errno; it cannot fault on Go's pointers and
// cannot panic. The model reads *newlimit (so a concurrent write races, as
// with the kernel's read), may write arbitrary limits to *old (a superset of
// the kernel's writes: always on success, never on failure), and returns
// errnoErr of an arbitrary errno, nil for 0, as Go's stub does with the
// kernel's. The limits themselves, the process's state, are not modelled.
func prlimit1(pid int, resource int, newlimit *Rlimit, old *Rlimit) (err error) {
	if newlimit != nil {
		_ = *newlimit
	}
	if old != nil && gomodel.Choose() {
		old.Cur = gomodel.ChooseUint64()
		old.Max = gomodel.ChooseUint64()
	}
	e1 := Errno(gomodel.ChooseUint64())
	if e1 != 0 {
		err = errnoErr(e1)
	}
	return
}
```

Real (`go doc -u -src syscall.prlimit1`):

```go
package syscall // import "syscall"

func prlimit1(pid int, resource int, newlimit *Rlimit, old *Rlimit) (err error) {
	_, _, e1 := RawSyscall6(SYS_PRLIMIT64, uintptr(pid), uintptr(resource), uintptr(unsafe.Pointer(newlimit)), uintptr(unsafe.Pointer(old)), 0, 0)
	if e1 != 0 {
		err = errnoErr(e1)
	}
	return
}
```

## Trusted models vs the Go source
```
</details>

### Lead decisions (2026-11-24 night)
- `runtime.callers`: a trusted one-line `.impl` calling the translated Go `callersModel` (not a pure Go model as first planned): as a Go model its gc body found no frames, `testing.callerName` panicked, and every model-test run failed. Accepted.
- crypto/rand.Int (D3): deferred out of this packet. crypto/rand and math/big stay as on lean; the parked work is on `goose-model-overlay-rest-rt-rand` (c6d26e15a, does not build); open questions in gmr-rt/resume.md (drbg `init.0`'s FIPS self-test under `failfipscast`, math/big proofs ~1-1.5k lines).
- GODEBUG: no new trusted `.impl`s for the setenv hooks. `Setenv`/`Unsetenv`/`Clearenv` and the runtime hooks stay untranslated, so a call is stuck; syscall.toml records the rule (time's KNOWN_LIMITATIONS entry relies on it).
- To check at integration: rerun the full library (the last run's one failure is fixed at d5b625198 but not rebuilt; ~1,870 modules were listed as skipped in that run, to explain).
- Adversarial review: pending (the lead runs it).
