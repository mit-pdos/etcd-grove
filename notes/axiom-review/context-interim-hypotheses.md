# Adversarial review: `context.WithValue.specPtr`, `context.WithCancel.specValBg`

Reviewed: worktree `/shared/etcd-grove-wt/ps2-s5srv-b9`, branch `prove-ps2-s5srv-b11/2026-11-24`, commit
`f6b2e39cbc`: `Net/Spec/context/WithValuePtr.lean`, `Net/Spec/context/WithCancelValBg.lean`,
`Net/Proof/context/CtxBg.lean`; Perennial's `Proof/context/{Base,CtxValue,WithCancelGen}.lean`,
`Code/context.{toml,lean}`; the repo's other `context` specs (`Spec/context/WithValue.lean`,
`WithCancelBackground`, `WithCancelTodo`, `WithCancelValCtx`) and `Spec/reflect/Value__Set.lean`;
go1.27.3's `src/context/context.go` (`WithValue` l.728, `withCancel` l.274, `propagateCancel` l.476,
`parentCancelCtx` l.383, `removeChild` l.400, `cancelCtx.cancel` l.550).

Go evidence: the author's (now `examples/stdlib/ctxhyp/{ctxhyp,source}_test.go`) passes (go1.27.3). Mine:
`examples/stdlib/ctxhyp/review_test.go`, first at `/shared/tmp/ps2/revctx/gotest` (`GOTOOLCHAIN=go1.27.3 go test -race -count=1 -v ./...`, passes).

## Verdicts

- `context.WithValue.specPtr`: **sound** (no counterexample). One docstring claim is false (F1).
- `context.WithCancel.specValBg`: **sound** (no counterexample). Post is weaker than Go (F2, optional).

## Findings, ranked

**F1 (docstring wrong; soundness unaffected).** `WithValuePtr.lean` says the three fields are read-only
because "they are unexported". `Context` is not: an embedded field takes its type's name, and
`Context` is exported. `reflect.ValueOf(ctx).Elem().Field(0).CanSet()` is `true` outside the
`context` package (`key`, `val`: `false`). My test `TestReflectWritesEmbeddedContext` writes a nil
`Context` into a `*valueCtx` this way, and `WithCancel` of it then panics (nil-interface call in
`propagateCancel`'s `parent.Done()`). The author's `TestValueCtxFieldsNeverWritten` scans only
`context`'s own sources, so it cannot see this.

This is no counterexample to the triple. A verified program can write the field only through a
spec that hands out ownership of it: `reflect` is names-only, has no `Value.Field`/`FieldByName`
spec, and the repo's `reflect.Value.Set.spec` needs `p ↦ x` (full ownership), which `↦□` never
gives back. So `↦□` stays sound under the usual ownership discipline.

Fix: (a) reword the header to: "`key` and `val` are unexported; `Context` is an exported embedded
field that only reflection can reach from outside `context` (`Field(0).Set`), and every write
needs full ownership of the field, which `↦□` excludes"; (b) add to `notes/perennial-changes.md`
(the `reflectlite`/`reflect-s05` entry, this hypothesis's retirement path) that a future
`reflect.Value.Field`/`Set` spec must require ownership of the struct (not just `reflElem`) and
must never apply to memory a `↦□` covers; (c) add the reflective-write case to the evidence.

**F2 (completeness, optional).** `specValBg` gives no `ctxValueFrom parent ctx'` and no
`ctxField c ↦□ parent`. So nothing can derive `ctx'.Value(ServerContextKey)` or
`ctx'.Value(LocalAddrContextKey)`, which net/http's handlers read through `conn.serve`'s context.
Adding `context.ctxValueFrom parent ctx'` would be true: `cancelCtx.Value` delegates every key
except `&cancelCtxKey` to `c.Context`, which `propagateCancel` writes once. Perennial's
`wp_WithCancel_Background_of` already gives it for depth 0. The keys here are `*contextKey`, so
`notIntPtrKey` holds. Add it only when a proof needs it; leaving it out is sound.

**F3 (remark).** `Values := ∅` claims nothing. `isContext`'s `"#HValue"` specifies only
`&cancelCtxKey` (Perennial's `Base.lean`: "the `Values` field of `ContextDesc` is unused"). Nothing
in Perennial or this repo reads a descriptor's `Values` (only `{cd with Values := vs}` updates
exist). So no proof can get `ctx'.Value(k) = nil` for a key the chain holds. `ctx'.Value(&cancelCtxKey)`
is `ctx'` itself in Go (`cancelCtx.Value` checks that key first), which matches `isCancelCtxAny`.
Suggested sentence for the header: "`Values := ∅` is sound only while no context predicate reads
`Values` (true today)."

**F4 (remark, outside these hypotheses).** gc aliases pointers to zero-size values:
`new(struct{}) == new(struct{})` can be true, and then `WithValue(bg, k1, "x").Value(k2)` is `"x"`
(`TestZeroSizeKeyAlias`). `specPtr` says nothing about key equality, so it is not affected. The
place this could matter is Perennial's `keyEqOk`/`ctxValue_valueCtx` together with the model's
zero-size allocation (`GoPrealloc` returns some address in `(0, maxAddr)`, not necessarily a
distinct one). I did not examine it further; net/http's keys are not zero-size.

## Checklist results

1. **Each post vs Go (never more).**
   - `specPtr`: Go returns `&valueCtx{parent, key, val}`. This is the only `valueCtx` literal, and
     `context` writes none of its fields.
   - `specValBg`:
     - `Deadline` is promoted through the chain to `Background()`: `(zero, false)`, matching
       `Deadline := none`.
     - `Done` and `Err` are `cancelCtx`'s own. They can be done only by `cancel`, because the
       chain's `Done()` is `nil`: `propagateCancel` returns at l.480 and registers nowhere. So
       `PDone := True` and `cancelSpec … True` are exact.
     - After cancel, `Err()` is `Canceled` (`isCtxErr` allows it) and `Cause` is `Canceled`.
     - `"#HParentCC"`: `parentCancelCtx(ctx')` returns `ctx'` itself (`Pp = True`).
     - `cancel`'s `removeChild(chain, c)`: `chain.(stopCtx)` fails, and `parentCancelCtx` returns
       on `Done() == nil`.
     - No goroutine is started.
     - All of this is checked under `-race` with concurrent `cancel`, `Done`, `Err`, `Deadline`
       and `Cause`, and with children `WithCancel`, `WithTimeout` and `AfterFunc` (canceled with
       `ctx'`, timer child `Err() == Canceled`), at chain depths 0-5 (200 iterations each) and at
       depth 100000.
2. **`↦□` of the `valueCtx` fields.** No write in `context` (and `WithoutCancel`/`AfterFunc` build
   other types). Reflection can write `Context` from outside (F1), but only with ownership;
   `unsafe` is outside what goose translates.
3. **Premises.**
   - A nil `parent` is excluded by `GoInterfaceOk`. A typed-nil parent is fine in Go.
   - A nil key is excluded by `interface.mkOk`. A typed-nil pointer key is fine.
   - Non-comparable keys are excluded: every `go.GoType.PointerType kt` is comparable. Tested
     with pointers to func, map, slice, `any`, `error`, `[0]int` and `struct{}`.
   - Named pointer types (`type P *int`) have a `Named` dynamic type and are not covered. That is
     fine.
   - `ctxBg` requires `Background()` at the bottom and the `↦□` fields at every link. Only
     `specPtr` produces those for a value of dynamic type `*valueCtx`, which a Go program cannot
     forge.
4. **Interaction with other specs.**
   - The repo's `Spec/context/WithValue.lean` covers only struct-typed keys, so its premise does
     not overlap with `specPtr`.
   - Depth 0 of `specValBg` is the proved `WithCancelBackground.spec` with a weaker post.
   - Perennial's `WithCancel` specs need `isParentCtx`/`isContext`, which a chain of depth ≥1 never
     satisfies (`isContextDone` needs `isChan`, which is non-nil). So the two families never
     apply to the same call.
   - `isCancelCtxCtx ctx'` lets `ctx'` be a parent for `wp_WithCancel`/`WithDeadline`, which is
     what Go does (the child registers in `ctx'.children`).
   - The `ctxValue` laws over the `↦□` fields are consistent: they use the same field locations
     and the same Lean type (`Context := GoInterface`).
5. **Go evidence.** The author's tests pass. Mine (above) pass, including the F1 demonstration.

No `issues/` entry: nothing here is a bug in Go.
