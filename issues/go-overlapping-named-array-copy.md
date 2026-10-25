---
upstream: none
checked: 2026-10-25
links:
  - golang/go#54467 issue closed: the same miscompile for `*p = *q` with identical array types, fixed by CL 425076 (memmove when the two sides may partially overlap); this case, with a conversion on the right, is not covered
  - golang/go#55920 issue closed: the arm64 slowdown from that fix; CL 433056 then narrowed the overlap test to "both sides are dereferences", which a conversion defeats
---

# Go: gc miscompiles a copy between overlapping array views of a named and an unnamed array type

- **Status**: a bug in the Go toolchain (gc), not in the Go code this repository verifies, in
  safe Go (no `unsafe`): an array assignment between partially overlapping views made by
  slice-to-array-pointer conversions gives a result no order of evaluation explains, when one
  side's array type is named and the other's is not. Recorded here because Perennial's
  guarantee for goose-translated code depends on what gc compiles; Perennial's model of the
  copy is right by the spec, gc is not.
- **Where**: gc go1.26.0 linux/amd64 (`/usr/local/go`), `cmd/compile/internal/ssagen/ssa.go`.
  Line 1831, in the `OAS` case of `stmt`:

  ```go
  mayOverlap := n.X.Op() == ir.ODEREF && (n.Y != nil && n.Y.Op() == ir.ODEREF)
  ```

  `mayOverlap` is passed to `moveWhichMayOverlap` (line 1605), which uses `memmove` for an
  array of more than one element only when it is set; its comment names this exact case
  ("Since Go 1.17, you can use a cast from a slice to a ptr-to-array ... For 2, we need to
  ensure that if there might be partial overlap, then we can't use OpMove"). An assignment
  between a named and an unnamed array type leaves an `OCONVNOP` (implicit or explicit) around
  the right side, so `n.Y.Op()` is `OCONVNOP`, not `ODEREF`: `mayOverlap` is false and gc emits
  an SSA `Move` (here `runtime.wbMove`), which assumes the two sides do not partially overlap.
  The spec: "Conversions from slice to array or array pointer" (Go 1.17) and assignment's
  two-phase evaluation (operands evaluated, then assigned).
- **What happens**: with `s` the strings `"0"` to `"9"`,

  ```go
  type A [8]string
  p := (*A)(s[1:9])
  q := (*[8]string)(s[0:8])
  *p = *q
  ```

  leaves `s` as `[0 0 0 0 0 0 0 0 0 9]`, a forward element-by-element copy. So do `*p = A(*q)`,
  `*p = A([8]string(s[0:8]))`, the tuple form `*p, x = *q, 1`, and the other direction
  (`p` a `*[8]string`, `q` a `*A`). With identical types on both sides
  (`*(*[8]string)(s[1:9]) = *(*[8]string)(s[0:8])`, or a generic `func cp[T any](p, q *T)
  { *p = *q }` at `T = [8]string`) the result is right. Element types without pointers are hit
  too: with `type B [8]uint64` the result is `[0 0 1 1 3 3 5 5 7 9]`, the forward copy in
  16-byte chunks. A reproduction (`go test` in a directory with `go.mod` saying `go 1.26`):

  ```go
  package overlap

  import (
  	"slices"
  	"testing"
  )

  type A [8]string
  type B [8]uint64

  //go:noinline
  func copyNamed(s []string) {
  	p := (*A)(s[1:9])
  	q := (*[8]string)(s[0:8])
  	*p = *q // [8]string is assignable to A: an implicit conversion
  }

  //go:noinline
  func copyConv(s []string) {
  	p := (*A)(s[1:9])
  	q := (*[8]string)(s[0:8])
  	*p = A(*q)
  }

  //go:noinline
  func copySliceConv(s []string) {
  	p := (*A)(s[1:9])
  	*p = A([8]string(s[0:8]))
  }

  //go:noinline
  func copyUnnamed(s []string) {
  	p := (*[8]string)(s[1:9])
  	q := (*[8]string)(s[0:8])
  	*p = *q
  }

  //go:noinline
  func copyNamedU64(s []uint64) {
  	p := (*B)(s[1:9])
  	q := (*[8]uint64)(s[0:8])
  	*p = *q
  }

  func TestNamedArrayOverlapCopy(t *testing.T) {
  	// An array assignment copies the right side's value: like memmove.
  	want := []string{"0", "0", "1", "2", "3", "4", "5", "6", "7", "9"}
  	for _, c := range []struct {
  		name string
  		f    func([]string)
  	}{
  		{"unnamed", copyUnnamed},
  		{"named", copyNamed},
  		{"conv", copyConv},
  		{"sliceconv", copySliceConv},
  	} {
  		s := []string{"0", "1", "2", "3", "4", "5", "6", "7", "8", "9"}
  		c.f(s)
  		if !slices.Equal(s, want) {
  			t.Errorf("%s: got %v, want %v", c.name, s, want)
  		}
  	}
  	u := []uint64{0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
  	copyNamedU64(u)
  	if wantU := []uint64{0, 0, 1, 2, 3, 4, 5, 6, 7, 9}; !slices.Equal(u, wantU) {
  		t.Errorf("named uint64: got %v, want %v", u, wantU)
  	}
  }
  ```

  On go1.26.0 linux/amd64 (2026-10-25):

  ```
  --- FAIL: TestNamedArrayOverlapCopy (0.00s)
      overlap_test.go:60: named: got [0 0 0 0 0 0 0 0 0 9], want [0 0 1 2 3 4 5 6 7 9]
      overlap_test.go:60: conv: got [0 0 0 0 0 0 0 0 0 9], want [0 0 1 2 3 4 5 6 7 9]
      overlap_test.go:60: sliceconv: got [0 0 0 0 0 0 0 0 0 9], want [0 0 1 2 3 4 5 6 7 9]
      overlap_test.go:66: named uint64: got [0 0 1 1 3 3 5 5 7 9], want [0 0 1 2 3 4 5 6 7 9]
  FAIL
  ```

  (`unnamed` passes.) The `-W` dump shows the statement as `AS (DEREF p) (CONVNOP Implicit
  (DEREF q))`.
- **Expected**: an assignment evaluates its right side, then stores it, so `*p = *q` copies the
  old `s[0:8]` into `s[1:9]`, `[0 0 1 2 3 4 5 6 7 9]`, as it does with identical types and as
  golang/go#54467 settled. A conversion between array types with the same underlying type does
  not change the value.
- **How the proof handles it**: Perennial's semantics copies an array with value semantics (a
  whole load, then a whole store), which is the spec's answer and is wrong for gc here; a
  program verified against it could misbehave when compiled. Perennial's guard,
  `goose/modelcheck` (Perennial branch `unsafe-guard`, commit 5d1198961, not yet on Perennial's
  `lean`; `docs/design/unsafe-memory.md` R4, and the review of draft 9 in section 11, which
  found this), runs on every package goose translates and refuses to emit the translation when
  a statement copies a value of **any array type** (with pointers or not) between two memory
  places that are not exempt (whole variables, and the like). So goose refuses such a copy
  rather than translate it, and the verified results do not cover a program that does it.
  Before that review the guard skipped arrays with pointers, assuming gc's `memmove`, which
  this bug shows it does not always use. Today's verified etcd and raft code has no such copy,
  as far as is known.
- **Possible fixes**: strip `OCONVNOP` from the right side before the test, as the code just
  below already does for the pointer under the `ODEREF` in the `OSPTR` string case:

  ```go
  y := n.Y
  for y != nil && y.Op() == ir.OCONVNOP {
  	y = y.(*ir.ConvExpr).X
  }
  mayOverlap := n.X.Op() == ir.ODEREF && (y != nil && y.Op() == ir.ODEREF)
  if y != nil && y.Op() == ir.ODEREF {
  	p := y.(*ir.StarExpr).X
  	...
  ```

  Tried on a copy of the go1.26.0 tree (2026-10-25; Go itself not changed, nothing sent
  upstream): the compiler emits `runtime.typedmemmove` for the statement,
  `TestNamedArrayOverlapCopy` passes, so do the tuple and reversed-direction forms, and
  `go test -short cmd/compile/internal/ssagen cmd/compile/internal/test` passes. (With a copy
  of GOROOT, use a fresh `GOCACHE`: the go command keys a release compiler's cache by its
  version, so it otherwise reuses the unpatched objects.) The cost is a `memmove` for array
  copies through a conversion between two dereferences, the same as without the conversion.
  The left side cannot carry a conversion (it is not addressable), so it needs nothing. A
  regression test would go in `test/fixedbugs`, next to golang/go#54467's.
- **Found**: 2026-10-25, an adversarial review of Perennial's unsafe-memory guard (the review
  of draft 9 of `docs/design/unsafe-memory.md`, Perennial branch `unsafe-guard`), with Go
  probes on gc 1.26; the test above, the patch and the upstream search the same day.
