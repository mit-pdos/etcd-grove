---
upstream: none
checked: 2026-10-26
links:
  - golang/go#18595 issue closed: the same class through a value conversion (named and unnamed interface, `==` false), fixed by recomputing the itab; a pointer conversion cannot
  - golang/go#26094 issue closed: related, not this bug (the misleading "different packages" wording, now "different scopes", for genuinely different types)
candidate: issues/upstream/go-itab-reinterpret-assert/
---

# Go: a type assertion on an interface value read as another interface type panics

- **Status**: a bug in Go against its spec (the conversion needs no `unsafe`), though which of
  the compiler, the runtime or the spec should change is not settled. The compiler compares
  itab pointers where the spec compares dynamic types: in `x.(T)` and type switches on a
  non-empty interface, and in `==` on two of them (and so map keys). An issue for golang/go is
  drafted in `issues/upstream/go-itab-reinterpret-assert/` (`issue.md`, `meta.md`).
- **Where**: the Go runtime's type assertion from a non-empty interface (the panic message
  below), observed with go1.26.0, go1.27.1, go1.27.2 and go1.27.3 (2026-10-23). The spec's type assertion (`x.(T)` holds if the dynamic
  type of `x` is `T`) says nothing about the itab. Found in Perennial's byte-memory review,
  round 3 (`docs/BYTE_MEMORY_REVIEW.md` on Perennial's branch `worktree-byte-heap`,
  7b5230c36).
- **What happens**: two distinct named interface types with identical method sets have the
  same underlying type, so `*I1` converts to `*I2` (directly or through `unsafe.Pointer`).
  An `I1` value read through the converted pointer keeps the itab for `(T, I1)`. Asserting
  `.(T)` on it panics, although its dynamic type is `T`:

  ```go
  type I1 interface{ M() }
  type I2 interface{ M() }
  type T struct{ x int }
  func (T) M() {}

  func main() {
  	var a I1 = T{1}
  	b := *(*I2)(&a)   // or *(*I2)(unsafe.Pointer(&a))
  	_ = b.(T)
  }
  ```

  Output (both conversions, go1.26.0): `panic: interface conversion: main.I2 is main.T, not
  main.T (types from different scopes)`. The assertion compares the value's itab with the
  itab for `(T, I2)`, not only the dynamic type. `b == c` for `var c I2 = T{1}` is false too
  (while `any(b) == any(c)` holds), a type switch misses `case T`, and a `map[I2]` lookup
  misses: `go-itab-reinterpret-assert/main.go`, `probe/main.go`; `variants/main.go` shows the
  value conversion `I2(a)` is fine (golang/go#18595) and `*(*interface{ M() })(&a)` is not.
- **Expected**: by the spec, `b`'s dynamic type is `T`, so the assertion holds and `b == c`;
  if the conversion is to be rejected instead, the spec's conversion rules would have to say
  so. The panic message is misleading either way (`T` and `T` are the same type).
- **How the proof handles it**: Perennial's byte-memory semantics (branch
  `worktree-byte-heap`, not yet on Perennial's `lean`) follow the runtime. `TypeAssert`
  carries the static source type, and an assertion from a non-empty interface `I` checks
  both `itab.Type = typeAddr T` and `itab.Inter = typeAddr I` (review round 4). So the
  program above cannot be verified as non-panicking. The verified etcd code does not
  reinterpret interface values this way, as far as is known.
- **Possible fixes**: none proposed in the issue. Options: one itab per concrete type for all
  interfaces with the same underlying type (itabs keyed by the underlying interface type);
  comparing `itab._type` instead of the itab pointer; or forbidding the conversion between
  pointers to distinct non-empty interface types (a compatibility break).
- **Found**: 2026-10-13 (round 3 of the byte-memory `/review-trusted` review, recorded here
  for tracking); the panic confirmed with the program above; the `==`, type switch and map
  consequences and the upstream search 2026-10-19.
