---
upstream: fixed
checked: 2026-10-25
links:
  - golang/go#78371 issue closed: this bug ("no-op interface conversion bypasses overlap checking", CVE-2026-27144), reported by Jakub Ciolek, fixed by golang/go@3985ca0b6264 (2026-04-08, Go 1.27) with the fix proposed below; backported as golang/go#78424 (Go 1.26.2) and golang/go#78423 (Go 1.25.9)
  - golang/go#54467 issue closed: the same miscompile for `*p = *q` with identical array types, fixed by CL 425076 (memmove when the two sides may partially overlap); this case, with a conversion on the right, is not covered
  - golang/go#55920 issue closed: the arm64 slowdown from that fix; CL 433056 then narrowed the overlap test to "both sides are dereferences", which a conversion defeats
---

# Go: gc miscompiles a copy between overlapping array views of a named and an unnamed array type

- **Status**: a bug in the Go toolchain (gc), not in the Go code this repository verifies, in
  safe Go (no `unsafe`), already fixed upstream (CVE-2026-27144): go1.26.0, the toolchain this
  was found on, has it; go1.25.9, go1.26.2 and go1.27 do not. Recorded here because Perennial's guarantee for goose-translated code
  depends on what gc compiles; Perennial's model of the copy is right by the spec, gc is not.
- **Where**: gc go1.26.0 linux/amd64, `cmd/compile/internal/ssagen/ssa.go:1831`, in the `OAS`
  case of `stmt`:

  ```go
  mayOverlap := n.X.Op() == ir.ODEREF && (n.Y != nil && n.Y.Op() == ir.ODEREF)
  ```

  Only when `mayOverlap` is set does `moveWhichMayOverlap` use `memmove`. Assigning an unnamed
  array type to a named one wraps the right side in an implicit `OCONVNOP`, so `n.Y.Op()` is
  not `ODEREF`, `mayOverlap` is false, and gc emits a `Move`, which assumes the two sides do
  not partially overlap.
- **What happens**:

  ```go
  package main

  import "fmt"

  type A [4]int

  func main() {
  	s := []int{0, 1, 2, 3, 4}
  	*(*A)(s[1:5]) = *(*[4]int)(s[0:4])
  	fmt.Println(s)
  }
  ```

  prints `[0 0 1 1 3]` on go1.26.0 linux/amd64 (2026-10-25; `[0 0 1 2 3]` on go1.26.2 and
  go1.27.1): the old `s[0:4]` is copied
  forward in 16-byte chunks over itself. Replacing `*A` by `*[4]int`, so that the two sides
  have identical types, prints `[0 0 1 2 3]`.
- **Expected**: `[0 0 1 2 3]`. An assignment evaluates its right side and then stores it (as
  golang/go#54467 settled for identical types), and converting between array types with the
  same underlying type does not change the value.
- **How the proof handles it**: Perennial's semantics copies an array as a whole load then a
  whole store, the spec's answer, which gc does not implement here. Perennial's guard,
  `goose/modelcheck` (Perennial branch `unsafe-guard`, commit 5d1198961, not yet on its `lean`;
  `docs/design/unsafe-memory.md` R4 and the review of draft 9 in section 11, which found this),
  refuses to translate a statement that copies a value of any array type between two memory
  places that are not exempt (whole variables and the like), so the verified results do not
  cover such a copy. Today's verified etcd and raft code has none, as far as is known.
- **Possible fixes**: upgrade the toolchain (go1.25.9, go1.26.2 or later). Upstream's fix,
  golang/go@3985ca0b6264, is the one below: strip `OCONVNOP`s from the right side before the test:

  ```go
  y := n.Y
  for y != nil && y.Op() == ir.OCONVNOP {
  	y = y.(*ir.ConvExpr).X
  }
  mayOverlap := n.X.Op() == ir.ODEREF && (y != nil && y.Op() == ir.ODEREF)
  ```

  Tried on a copy of the go1.26.0 tree (2026-10-25; nothing sent upstream): gc then emits
  `runtime.typedmemmove`, the same copy on `[8]string` and `[8]uint64` arrays comes out
  right, and `go test -short cmd/compile/internal/ssagen cmd/compile/internal/test` passes
  (use a fresh `GOCACHE` with a copied GOROOT, or the go command reuses the unpatched objects).
  The left side cannot carry a conversion, so it needs nothing. Upstream's regression test is
  `cmd/compile/internal/test/memoverlap_test.go`.
- **Found**: 2026-10-25, an adversarial review of Perennial's unsafe-memory guard (the review
  of draft 9 of `docs/design/unsafe-memory.md`, Perennial branch `unsafe-guard`), with Go
  probes on gc 1.26. Found already fixed upstream the same day, when drafting a report.
