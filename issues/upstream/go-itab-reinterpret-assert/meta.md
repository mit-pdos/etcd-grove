# go-itab-reinterpret-assert

## Security

Not reported as a security issue: the wrong results are a `false` and a panic, with no memory
unsafety (method calls through the reinterpreted value dispatch correctly: the itabs of `(T, I1)`
and `(T, I2)` list the same methods in the same order). A program needs the pointer conversion on
purpose, so an attacker-controlled input cannot reach it.

## Candidate

- **Finding**: `issues/go-itab-reinterpret-assert.md`
- **Target**: golang/go, an issue only (no fix branch: Go takes changes through Gerrit, and it is
  not settled whether the compiler, the runtime or the spec should change)
- **Reproduction**: `issues/go-itab-reinterpret-assert/main.go` (the issue's program);
  `probe/main.go` (type switch, map lookup, `any` equality, `%T`, assertion to another interface)
  and `variants/main.go` (`type J I`, the unnamed interface, the value conversion) for the issue's
  "also"
- **State**: ready to file (2026-10-23), not filed; checked 2026-10-23 with go1.27.3 (the newest release on
  go.dev/dl), linux/amd64: `main.go`, `probe/main.go`, `variants/main.go` outputs unchanged from go1.27.2; `go vet`,
  `gofmt -l` clean. `go env` in `issue.md` from go1.27.3. Not run at tip
- **Upstream issue**: —

The issue follows golang/go's bug-report template (Go version, `go env`, what did you do / see /
expect). The `go env` output is trimmed of the lines with local paths (`GOBIN`, `GOCACHE`, `GOENV`,
`GOMOD`, `GOMODCACHE`, `GOPATH`, `GOROOT`, `GOTELEMETRYDIR`, `GOTOOLDIR`, `GOGCCFLAGS`) and empty
ones. A playground link (go.dev/play) could replace the program; none was made, since sharing
publishes it.

`.claude/skills/upstream-report/check.py go-itab-reinterpret-assert`: three FAILs that are the
skill's etcd conventions, not this target's: "spec" (here the Go spec, the word Go's maintainers
use), no "Anything else we need to know?" section (Go's template has none), no `pr.md` (an issue
only). No prose-length warning.

## Duplicates checked (2026-10-19)

GitHub search on `repo:golang/go`: `itab conversion pointer interface`, `"different scopes"
interface conversion`, `itab identical underlying interface`, `interface pointer conversion type
assertion panic itab`, `ifaceeq itab pointer conversion`, `"interface conversion" "not main.T"`
(five more queries hit the API's rate limit), and one web search. No duplicate. Related:

- golang/go#18595 (closed, 2017): `i1 == i2` false after a *value* conversion from an unnamed to
  a named interface with the same methods, because the compiler emitted a no-op conversion that
  kept the old itab; fixed (CL 35119) by recomputing the itab on such conversions. The same class
  as this bug; a pointer conversion cannot recompute the itab in memory. The issue cites it.
- golang/go#26094 (closed): the "different packages" wording of the panic message (now "different
  scopes") was wrong for genuinely different types of the same name.
- golang/go#48532 (open), #46895 (open), and several generics issues (#51250, #52027, #53376):
  other ways to get "types from different scopes" (plugins, WASM, generic instantiation), all for
  types that really differ or a mismatch the runtime should not see; none through a conversion.
- golang/go#80332 (closed, 2026): `reflect` trusting `reflect.Type` methods an embedding type
  shadows; a different mechanism. randall77 there: converting `*T` to `*U` through a data race is
  possible without `unsafe` and "not something we need to fix". Here no race or `unsafe` is
  needed.

## Duplicates re-checked (2026-10-23)

`repo:golang/go "types from different scopes" created:>2026-10-01` (0), `repo:golang/go itab pointer conversion
interface identical underlying` (#25860, #71183, #49085, #29192: spec proposals, none this bug; #71183, closed, asks
for `[]A` to `[]B` conversions), `repo:golang/go type assertion panic "not main.T"` (#82054, an unrelated compiler
crash; #26094). No duplicate.

## Verification

go1.26.0, go1.27.1 and go1.27.2 (the latest release, 2026-10-19), linux/amd64, all identical:
`go run main.go` prints `false`, `false`, `true`, `main.T` and panics with `interface conversion:
main.I2 is main.T, not main.T (types from different scopes)`; the same with `-gcflags='-N -l'`
(go1.26.0). `go vet main.go` and `gofmt -l` are clean. `probe/main.go`: `_, ok := b.(T)` false,
the type switch takes `default`, `b == c` false, `any(b) == any(c)` true, the map lookup misses,
`any(b).(T)` succeeds, `%T` is `main.T`, `b.M()` runs. `variants/main.go`: `J(a).(T)` holds;
`*(*J)(&a)` and `*(*interface{ M() })(&a)` both fail the assertion and `==`. Not run at tip (no
`gotip` installed).

## If a reviewer asks

- Is the conversion legal? Yes, without `unsafe`: the spec allows converting between pointer
  types that are not named types when their base types have identical underlying types (ignoring
  struct tags), and `I1`'s and `I2`'s underlying type is `interface{ M() }`.
- Where does the itab compare happen? The compiler emits an inline compare of the value's itab
  pointer with the static itab symbol for `(T, I2)` for `x.(T)` and type switch cases on a
  non-empty interface; `==` on two non-empty interfaces (and the map's key equality) compares the
  itab pointers before the data. Converting to `any` keeps only `itab._type`, so `any(b) ==
  any(c)` holds.
- What could change? Not proposed in the issue; directions: give interfaces with identical
  underlying types one itab per concrete type (key itabs by the underlying interface type); or
  compare `itab._type` instead of the itab pointer (an extra load on every such assertion); or
  reject the pointer conversion between distinct non-empty interface types in the spec (breaks
  compatibility).
- Why does it matter to formal verification? A semantics in which memory holds bytes has to
  decide what a reinterpreted interface value is; Perennial's byte-memory semantics follow the
  runtime (an assertion from a non-empty interface checks the itab's interface type), so a program
  like this cannot be proved not to panic. See the finding's "How the proof handles it".
