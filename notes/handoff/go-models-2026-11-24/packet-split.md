# Unit split: `internal/bytealg` (MakeNoZero, init.0, Count/CountString) and the real-`strings.Split` follow-up (D-S1b)

Branch `goose-model-overlay-rest-split` (Perennial), head `8a6feff49`, on `lean` 54a29571e (S1). Note: commit
8a86dc88f's subject says "strings.Split real"; Split was then put back to its model (cedcc0138, 8a6feff49): see D-split-b.

## What changed

**Today (lean):** `Perennial/TrustedCode/internal/bytealg.lean` (81 lines) holds hand-written GooseLang for
`bytealg.MakeNoZero` (a capacity from `ArbitraryInt`, a recursive `fillArbitrary`) and `init.0` (`ArbitraryInt` picks
`MaxLen` 63 or 31); `bytealg.toml` has `trusted = ["MakeNoZero", "init.0"]`. `strings.Split` is a Go model (S1).

**With this branch:** that file and its empty `ManualProof` stub are deleted; `trusted = []` in bytealg.toml.

### Became real translations (no trust)
- `strings.Count`, `strings.Index` (strings' wrapper of `stringslite.Index`): translated, with new proved specs
  (`Count`: for `substr ≠ []`, RET `(split s substr).length - 1`; `Index`: = `stringslite.Index`'s). No caller needs them
  yet (Split stays a model); kept so option (a) below is cheap.

### Go models (trusted Go; side by side with the real Go in the details below)
| model | where | why not the real Go | choice points |
|---|---|---|---|
| `bytealg.Count`, `CountString` | `goose/model/overlay/internal/bytealg/count.go` | bodyless in count_native.go (goose: `[unsupported]: external function`), assembly in count_amd64.s | none: Go's own `count_generic.go` bodies, verbatim (diffed); `blank_asm += count_amd64.s` (defines only `·Count`, `·CountString`, `countbody<>`; includes only go_asm.h/asm_amd64.h/textflag.h) |
| `bytealg.MakeNoZero` | `.../bytealg/bytealg.go` | no Go body (goose: `external function`); defined by the runtime (`runtime/slice.go`, a push `go:linkname`, which the overlay builder now blanks: fb61fea3d) | capacity `int(ChooseUint64()>>1)` raised to `n` (covers `roundupsize`); each byte up to cap (`mallocgc(needzero=false)`) |
| `bytealg.init.0` | `.../bytealg/init.go` (`//gomodel:replace init.0`) | translates, but reads `internal/cpu.X86`, filled only by the runtime from `cpuid`; translated, `MaxLen` would always be 31 (more defined than gc) | `gomodel.Choose()`: the AVX2 bit |

Known divergence (no new premise; existing limitation): `MakeNoZero(n)` with `n > maxAlloc` (2^48) panics in gc
(`panicmakeslicelen`); the model's `make` allocates, as the semantics' `make`/`append` do
(docs/KNOWN_LIMITATIONS.md "No limit on allocation size", which already names MakeNoZero). Negative `n` panics in
`make` as in Go.

### Translator (goose/util/model.go; reported to the lead earlier)
- 867d5adb3: a blanked assembly file may include the toolchain's `asm_amd64.h` (count_amd64.s does).
- fb61fea3d: for a replaced function defined by a runtime push `//go:linkname <local> P.<Name>`, the `go build
  -overlay` map also drops that directive from the runtime file (test `model_linkname_test.go`). Only affects the
  Go build of the model tests; goose's translation is unchanged.

### New primitives
None. Uses S1's `gomodel.Choose`/`ChooseUint64` (specs cherry-picked from 634fd62a0 as 7c23b3c07).

### Deleted trusted Lean
`Perennial/TrustedCode/internal/bytealg.lean` (81 lines: `MakeNoZero.impl`, `fillArbitrary`, `init.«0».impl`),
`Perennial/ManualProof/internal/bytealg.lean` (5).

## Premise and statement changes
None. `bytealg.MakeNoZero.spec`, `bytealg.initialize'.spec` (isInit: `MaxLen ∈ {31, 63}`), `strings.Split.spec`
(keeps `sep ≠ []`, D-split-a) unchanged. New specs: `bytealg.CountString`, `strings.Count`, `strings.Index`.

## Decisions
- **D-split-a** (lead: keep). `strings.Split.spec` keeps `sep ≠ []`: dropping it needs `split` extended to Go's UTF-8
  `explode` and full `utf8.RuneCountInString`/`DecodeRuneInString` specs.
- **D-split-b** (lead chose (b); offered to Upamanyu). The real `Split` (goose translates `genSplit`, `Count`, `Index`,
  `explode`) cannot meet today's `Split.spec`: for `len(s) = 2^63-1`, `genSplit(s, sep, 0, -1)` computes
  `n = Count(s,sep)+1`, then `if n > len(s)+1` with `len(s)+1` overflowing to `-2^63`, so `n = -2^63` and
  `make([]string, n)` panics ("len out of range"). Strings are unbounded byte lists in the semantics (`len` only gives
  `< 2^63`), so the real Split would need a new premise `s.length < 2^63-1` (gc cannot hold such a string: maxAlloc).
  (b), done: keep Split as S1's Go model, the reason in strings.toml's and the model's comments.
  (a), option: translate the real Split and add that premise to `Split.spec` (and a `genSplit.spec`). Parked work:
  `gmr-split/real-split/` (configs, generated code, draft genSplit/Split proofs; Base lemmas `split_found`,
  `split_index`, `split_length_single` are on the branch).

## `#print axioms`
`internal.bytealg.wp_MakeNoZero`, `wp_initialize'`, `wp_CountString`, `strings.wp_Count`, `wp_Index`, `wp_Split`,
`strings.Builder.wp_grow`: `[propext, Classical.choice, Quot.sound]` each.

## Evidence
- `etc/model-tests.sh` (go1.26.11, linux/amd64, under the overlay): `strings`, `errors`, `bytes` ok (bytes' Count
  tests run against the Count model; MakeNoZero's model under Builder). Skipped as before: `TestSplit|ExampleSplit`
  (empty sep: Split's model is stuck), Builder allocation-count tests (now also because MakeNoZero's model allocates
  exactly n under gc, not the size class), `TestBuilderCopyPanic`, `errors.TestIs`.
- `go test ./goose/...` ok. `etc/update-goose-new.py --std-lib` regenerates the committed `Code/` (strconv.lean
  restored from lean, as in S1). `etc/gen-link.py --check` ok.
- Build (VM): every module importing `Code.strings`, `Code.internal.bytealg` or the changed proof/spec modules (436
  modules, 14 leaves) builds.
- review-trusted (fix mode, by hand; no adversary subagent per the takeover rules): Count/CountString diffed against
  count_generic.go (identical); MakeNoZero against `runtime.bytealg_MakeNoZero`; init.0 against index_amd64.go's;
  count_amd64.s's definitions checked. Findings: none beyond the documented maxAlloc divergence.

<details><summary>etc/trusted-delta.py: the models next to the real Go</summary>

```
## Go model overlays (TRUSTED: model Go is reviewed as Go, rule R12)

For each replaced declaration: every behaviour of the real one (gc, linux/amd64, the pinned Go), under every use by the program and the real package, must be a behaviour of the model's translation. Compare the two sources line by line; every `gomodel.Choose`/`ChooseUint64`/`Stuck` needs a reason in the doc comment.

### Perennial/Code/internal/bytealg.toml  (package `internal/bytealg`)

- `[model]` before: dir = 'goose/model/overlay/internal/bytealg', replaces = ['IndexByte', 'IndexByteString', 'Index', 'IndexString', 'CompareString'], added_methods = []
- `[model]` after:  dir = 'goose/model/overlay/internal/bytealg', replaces = ['IndexByte', 'IndexByteString', 'Index', 'IndexString', 'CompareString', 'Count', 'CountString', 'MakeNoZero', 'init.0'], added_methods = []
- model files: goose/model/overlay/internal/bytealg/bytealg.go, goose/model/overlay/internal/bytealg/compare_native.go, goose/model/overlay/internal/bytealg/count.go, goose/model/overlay/internal/bytealg/index.go, goose/model/overlay/internal/bytealg/indexbyte.go, goose/model/overlay/internal/bytealg/init.go; changed: goose/model/overlay/internal/bytealg/bytealg.go, goose/model/overlay/internal/bytealg/count.go, goose/model/overlay/internal/bytealg/init.go

#### `internal/bytealg.Count` (new)

Model (goose/model/overlay/internal/bytealg/count.go:16):

```go
// MODEL: Count returns the number of instances of c in b. Go's generic body
// (count_generic.go); the assembly computes the same function,
// deterministically.
func Count(b []byte, c byte) int {
	n := 0
	for _, x := range b {
		if x == c {
			n++
		}
	}
	return n
}
```

Real (`go doc -u -src internal/bytealg.Count`):

```go
package bytealg // import "internal/bytealg"

//go:noescape
func Count(b []byte, c byte) int
```

#### `internal/bytealg.CountString` (new)

Model (goose/model/overlay/internal/bytealg/count.go:29):

```go
// MODEL: CountString returns the number of instances of c in s. Go's generic
// body (count_generic.go); the assembly computes the same function,
// deterministically.
func CountString(s string, c byte) int {
	n := 0
	for i := 0; i < len(s); i++ {
		if s[i] == c {
			n++
		}
	}
	return n
}
```

Real (`go doc -u -src internal/bytealg.CountString`):

```go
package bytealg // import "internal/bytealg"

//go:noescape
func CountString(s string, c byte) int
```

#### `internal/bytealg.MakeNoZero` (new)

Model (goose/model/overlay/internal/bytealg/bytealg.go:8):

```go
// MODEL: MakeNoZero(n) is a slice of length n and capacity at least n whose
// bytes, up to the capacity, are not zeroed. Go's has no Go body (goose:
// "external function"): the runtime defines it (runtime/slice.go,
// `//go:linkname bytealg_MakeNoZero internal/bytealg.MakeNoZero`, which the
// overlay blanks so that gc links this body instead) as
//
//	if uintptr(len) > maxAlloc {
//		panicmakeslicelen()
//	}
//	cap := roundupsize(uintptr(len), true)
//	return unsafe.Slice((*byte)(mallocgc(cap, nil, false)), cap)[:len]
//
// The model chooses the capacity (gomodel.ChooseUint64: any c >= n, which
// includes the size class roundupsize rounds n up to) and each byte up to the
// capacity (gomodel.ChooseUint64: mallocgc with needzero false returns memory
// with whatever it held, which a Go program cannot predict). A negative n
// panics in make with Go's message ("makeslice: len out of range"). An n
// above maxAlloc (2^48), where gc panics, is not checked: the model
// allocates, as the semantics' make and append do (docs/KNOWN_LIMITATIONS.md,
// "No limit on allocation size", which names MakeNoZero).
func MakeNoZero(n int) []byte {
	c := int(gomodel.ChooseUint64() >> 1)
	if c < n {
		c = n
	}
	b := make([]byte, n, c)
	full := b[:cap(b)]
	for i := range full {
		full[i] = byte(gomodel.ChooseUint64())
	}
	return b
}
```

Real (`go doc -u -src internal/bytealg.MakeNoZero`):

```go
package bytealg // import "internal/bytealg"

// MakeNoZero makes a slice of length n and capacity of at least n Bytes
// without zeroing the bytes (including the bytes between len and cap).
// It is the caller's responsibility to ensure uninitialized bytes
// do not leak to the end user.
func MakeNoZero(n int) []byte
```

#### `internal/bytealg.init.0` (new)

Model (goose/model/overlay/internal/bytealg/init.go:9):

```go
// MODEL: the package's init sets MaxLen to 63 or to 31. Go's
//
//	if cpu.X86.HasAVX2 {
//		MaxLen = 63
//	} else {
//		MaxLen = 31
//	}
//
// reads internal/cpu.X86, which no Go package initializer sets: the runtime
// fills it (cpu.Initialize, from schedinit) from the processor's cpuid
// (assembly) before any package is initialized. Goose translates the real
// init, but X86 would then stay zero and MaxLen always 31, more defined than
// gc. The model chooses (gomodel.Choose: the processor's AVX2 bit, which the
// semantics does not model) either value.
//
//gomodel:replace init.0 "if cpu.X86.HasAVX2 {"
func init() {
	if gomodel.Choose() {
		MaxLen = 63
	} else {
		MaxLen = 31
	}
}
```

(`go doc` cannot show `init.0`, the real package's init of that number in goose's numbering: read it in the real source. The marker quotes its first body line: "if cpu.X86.HasAVX2 {")

Replaced, unchanged: `CompareString`, `Index`, `IndexByte`, `IndexByteString`, `IndexString`

### Perennial/Code/strings.toml  (package `strings`)

- `[model]` (unchanged): dir = 'goose/model/overlay/strings', replaces = ['Split', 'Builder.copyCheck', 'Builder.String', 'Builder.Reset'], added_methods = []
- model files: goose/model/overlay/strings/builder.go, goose/model/overlay/strings/strings.go; changed: goose/model/overlay/strings/strings.go

#### `strings.Split` (changed)

Model (goose/model/overlay/strings/strings.go:8):

```go
// MODEL: Split(s, sep) is the substrings of s between the occurrences of sep
// (found left to right, not overlapping), as Go's genSplit(s, sep, 0, -1)
// computes them. The model finds the occurrences by testing HasPrefix at each
// position, where Go's genSplit counts them with Count and finds them with
// Index. Goose translates the real Split, but at len(s) = 2^63-1 (a string gc
// cannot hold) genSplit's len(s)+1 overflows and it panics, so its spec would
// need a bound on len(s) that Split's spec does not have
// (Perennial/Code/strings.toml). The model returns the same fields as
// genSplit wherever genSplit does not panic, and there only: building such a
// string needs an allocation gc refuses, which the semantics allows
// (docs/KNOWN_LIMITATIONS.md, "No limit on allocation size"). For an empty
// sep, Go splits s into its UTF-8 sequences (explode); the model is stuck
// there, so every spec of Split requires sep to be non-empty.
func Split(s, sep string) []string {
	if len(sep) == 0 {
		gomodel.Stuck()
	}
	var a []string
	var field string
	rest := s
	for len(rest) > 0 {
		if HasPrefix(rest, sep) {
			a = append(a, field)
			field = ""
			rest = rest[len(sep):]
			continue
		}
		field += rest[:1]
		rest = rest[1:]
	}
	return append(a, field)
}
```

Real (`go doc -u -src strings.Split`):

```go
package strings // import "strings"

// Split slices s into all substrings separated by sep and returns a slice of
// the substrings between those separators.
//
// If s does not contain sep and sep is not empty, Split returns a
// slice of length 1 whose only element is s.
//
// If sep is empty, Split splits after each UTF-8 sequence. If both s
// and sep are empty, Split returns an empty slice.
//
// It is equivalent to [SplitN] with a count of -1.
//
// To split around the first instance of a separator, see [Cut].
func Split(s, sep string) []string { return genSplit(s, sep, 0, -1) }
```

Replaced, unchanged: `Builder.Reset`, `Builder.String`, `Builder.copyCheck`

```

</details>
