---
upstream: fixed
checked: 2026-10-26
links:
  - golang/go#78371 issue closed: this bug ("no-op interface conversion bypasses overlap checking", CVE-2026-27144), reported by Jakub Ciolek, fixed by golang/go@3985ca0b6264 (2026-04-08, Go 1.27); backported as golang/go#78424 (Go 1.26.2) and golang/go#78423 (Go 1.25.9)
  - golang/go#54467 issue closed: the same miscompile for `*p = *q` with identical array types, fixed by CL 425076 (memmove when the two sides may partially overlap); this case, with a conversion on the right, was not covered
  - golang/go#55920 issue closed: the arm64 slowdown from that fix; CL 433056 then narrowed the overlap test to "both sides are dereferences", which a conversion defeats
blocks-proof: no
---

# Go: gc miscompiles a copy between overlapping array views of a named and an unnamed array type

In safe Go, `*(*A)(s[1:5]) = *(*[4]int)(s[0:4])` with `type A [4]int` copies `s[0:4]` forward over
itself instead of loading it first: `s = []int{0,1,2,3,4}` becomes `[0 0 1 1 3]` instead of
`[0 0 1 2 3]` (gc's overlap test missed the implicit conversion on the right side). Fixed in
go1.25.9, go1.26.2 and go1.27.

**Reproduction:** `TestOverlappingNamedArrayCopy` in
[`issues/go-overlapping-named-array-copy/overlap_test.go`](go-overlapping-named-array-copy/overlap_test.go),
in a scratch module, linux/amd64, with go1.26.1 (the last 1.26 release before the fix; it passes on
go1.26.2 and go1.27.3):

```
$ GOTOOLCHAIN=go1.26.1 go test ./overlap -count=1 -v
=== RUN   TestOverlappingNamedArrayCopy
    overlap_test.go:18: s = [0 0 1 1 3], want [0 0 1 2 3]
--- FAIL: TestOverlappingNamedArrayCopy (0.00s)
=== RUN   TestOverlappingUnnamedArrayCopy
--- PASS: TestOverlappingUnnamedArrayCopy (0.00s)
FAIL
```

## Proof

no: Perennial's semantics copies an array as a whole load then a whole store (the spec's answer),
and its guard `goose/modelcheck` (Perennial branch `unsafe-guard`, 5d1198961, not yet on its
`lean`) refuses to translate an array copy between two memory places that may overlap; the
verified etcd and raft code has none, as far as is known. The toolchains this repository pins
(go1.27.x) have the fix.

## Notes

Found 2026-10-25 by an adversarial review of Perennial's unsafe-memory guard
(`docs/design/unsafe-memory.md`, draft 9), already fixed upstream; the one-loop fix tried on a copy
of go1.26.0 (strip `OCONVNOP`s from the right side before the `ODEREF` test) is upstream's.
