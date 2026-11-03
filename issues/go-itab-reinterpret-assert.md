---
upstream: reported
checked: 2026-11-01
links:
  - golang/go#82470 issue open: this bug, filed by us 2026-10-23 (label compiler/runtime); thepudds bisected the behavior change to Go 1.9, randall77 proposed naming itabs by the underlying interface type and noted that reflect refuses the same *I1-to-*I2 conversion
  - golang/go#18595 issue closed: the same class through a value conversion (named and unnamed interface, `==` false), fixed by recomputing the itab; a pointer conversion cannot
  - golang/go#26094 issue closed: related, not this bug (the misleading "different packages" wording, now "different scopes", for genuinely different types)
blocks-proof: no
---

# Go: `x.(T)` and `==` fail on an interface value read through a `*I1` to `*I2` conversion

Two interface types with the same methods have identical underlying types, so `*I1` converts to
`*I2` without `unsafe`. An `I1` value read through the converted pointer keeps the itab of
`(T, I1)`: `b.(T)` panics (`interface conversion: main.I2 is main.T, not main.T (types from
different scopes)`), a type switch misses `case T`, `b == c` is false for `var c I2 = T{1}` and a
`map[I2]` lookup misses, while `any(b) == any(c)` holds and `%T` prints `main.T`.

**Reproduction:** `TestItabReinterpret` in
[`issues/go-itab-reinterpret-assert/itab_test.go`](go-itab-reinterpret-assert/itab_test.go), in a
scratch module (no dependencies), go1.27.3 linux/amd64 (the latest release, 2026-11-01; the same
on go1.26.0, go1.27.1, go1.27.2):

```
$ go test ./itab -count=1 -v
=== RUN   TestItabReinterpret
    itab_test.go:25: b.(T) fails although b's dynamic type is itab.T
    itab_test.go:30: a type switch on b misses case T
    itab_test.go:33: b == c is false although any(b) == any(c)
    itab_test.go:36: a map[I2] lookup of b misses the key c
    itab_test.go:41: b.(T) panics: interface conversion: itab.I2 is itab.T, not itab.T (types from different scopes)
--- FAIL: TestItabReinterpret (0.00s)
=== RUN   TestItabValueConversion
--- PASS: TestItabValueConversion (0.00s)
FAIL
```

## Proof

no: Perennial's byte-memory semantics (Perennial branch `worktree-byte-heap`, not yet on its
`lean`) follow the runtime (an assertion from a non-empty interface checks the itab's interface
type), so such a program cannot be proved not to panic; the verified etcd code does not
reinterpret interface values this way, as far as is known.

## Notes

The issue's program (`main.go`) is the test's body as a `main` printing `false`, `false`, `true`,
`main.T` and then panicking. Found 2026-10-13 in round 3 of Perennial's byte-memory review
(`docs/BYTE_MEMORY_REVIEW.md` on Perennial's `worktree-byte-heap`, 7b5230c36). Not reported as a
security issue: no memory unsafety (method calls through the value dispatch correctly).
