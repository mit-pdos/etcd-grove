# Go: a type assertion on an interface value read as another interface type panics

- **Status**: open (recorded for tracking; not filed). It is unclear which aspect of Go, if
  any, should change: the spec, the runtime, or the rules for pointer conversions and
  `unsafe.Pointer`. No root cause analysis has been done.
- **Where**: the Go runtime's type assertion from a non-empty interface (the panic message
  below), observed with go1.26.0. The spec's type assertion (`x.(T)` holds if the dynamic
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
  itab for `(T, I2)`, not only the dynamic type.
- **Expected**: unclear. By the spec, `b`'s dynamic type is `T` and the assertion should hold,
  but no Go rule makes the conversion produce an itab for `I2`, and the panic message is
  misleading (`T` and `T` are the same type).
- **How the proof handles it**: Perennial's byte-memory semantics (branch
  `worktree-byte-heap`, not yet on Perennial's `lean`) follow the runtime. `TypeAssert`
  carries the static source type, and an assertion from a non-empty interface `I` checks
  both `itab.Type = typeAddr T` and `itab.Inter = typeAddr I` (review round 4). So the
  program above cannot be verified as non-panicking. The verified etcd code does not
  reinterpret interface values this way, as far as is known.
- **Possible fixes**: none proposed. Options include documenting the behavior, having the
  runtime compare only the dynamic type, or forbidding the conversion between pointers to
  distinct interface types.
- **Found**: 2026-10-13 (round 3 of the byte-memory `/review-trusted` review, recorded here
  for tracking); the panic confirmed with the program above.
