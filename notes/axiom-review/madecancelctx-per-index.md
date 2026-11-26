# Review: `context.madeCancelCtx_of_isCancelCtx`, stated per error index (2026-11-25)

**Target.** The law in `Proof/context/MadeCancelCtx.lean` of the worktree `time-compare` (uncommitted,
over `b07b794461`, Perennial pin `a76168a96`), restated since perennial#705 (`0fd2c2394`:
`isCancelCtxOf c γ P` is `∃ A, …`) for every index:

```lean
axiom context.madeCancelCtx_of_isCancelCtx (c : Loc) (γ : ContextNames) (P : IProp GF)
    (A : GoInterface → Prop) :
    isCancelCtxOfA c γ P A ⊢ context.madeCancelCtx c
```

`madeCancelCtx c` is `□ madeCancelCtxRaw c`, an opaque. Its documented meaning: `c` was allocated by one
of `context`'s constructors, and only `context`'s code touches its fields. It explicitly excludes "a fresh
zero value (`reflect.New`) … although harmless in Go". Its consumers are `v3rpc.ctxDoneErr`'s `"#HValue"`
(`madeCancelCtxAny`) and `"#HParentCC"` (`SrvCtxWeak.lean`). They are taken by `leasehttp.RenewHTTP.spec`,
`waitLeader` and the local axiom `v3rpc.wp_WithTimeout_weak`, which also *gives* `madeCancelCtx` of its new
`*timerCtx`. No law eliminates `madeCancelCtx`: it yields no points-to and no pure fact.

Reviewed by reading only: no Lean build (on tundra), and no counterexample branch. One Go test was run
in a scratchpad at go1.27.3, below.

## Verdict

**Sound under stated conditions. The docstring's argument is wrong in one step, and the law contradicts
`madeCancelCtx`'s documented meaning.**

- **A proof can obtain `isCancelCtxOfA c γ P A` for a `c` that `context`'s constructors did not make.**
  The route is reflection: this repository's trust-boundary axioms for `reflect` give a program the field
  points-tos of a fresh zero `cancelCtx` (below). The law's docstring says "no spec of this repository
  or of Perennial gives a program a `cancelCtx`'s field points-tos". That is false. The law then gives
  `madeCancelCtx` of a `reflect.New`'d zero `*cancelCtx`, which `madeCancelCtx`'s own docstring says it
  does not hold of.
- **Not unsound today: no counterexample exists with the current consumers.** A zero `*cancelCtx` differs
  from one `context` made only in its embedded `Context` field, which is `nil`. Every consumer reaches the
  found `*cancelCtx` only through `context`'s `parentCancelCtx`, `propagateCancel`, `removeChild` and
  `Cause`. None of these reads that field (go1.27.3 `src/context/context.go:289-307, 383-414`, and
  `propagateCancel`, which writes the *child's* `Context`, never the parent's). The Go test confirms it:
  a zero `*cancelCtx` behind a wrapper context is a working parent for `WithTimeout`, `WithCancel` and
  `Cause`, with no panic and no race under `-race` over 1000 rounds.
- **The conditions:** (1) `madeCancelCtx`'s meaning is widened to every `*cancelCtx` whose state is
  `context`'s protocol (made by `context`, *or a zero value from `reflect.New`*). (2) No consumer of
  `madeCancelCtx` (an axiom that takes `ctxDoneErr`, or a future one) reads, or lets Go read, the found
  `*cancelCtx`'s `Context` field: its promoted `Deadline`, its `Value` at another key, `String`. On such
  a zero value, those panic (nil interface).

## The route to `isCancelCtxOfA` of a foreign location (strongest attack)

Go (`reflect` on an unexported type is legal; `TestZeroCancelCtxAsParent`):

```go
real, cancel := context.WithCancel(context.Background()); defer cancel()
t := reflect.ValueOf(real).Elem().Type()            // reflect.Type of context.cancelCtx
p := reflect.New(t).Interface().(context.Context)   // a fresh zero *cancelCtx, not made by context
```

Its proof, from trust-base axioms only (argued, not checked in Lean):

1. `wp_WithCancel_Background`: `real` is `interface.mk (*cancelCtx) #c0` (`isCancelCtxCtx`).
2. `reflect.ValueOf.spec` (`Spec/reflect/ValueOf.lean`) at `T := cancelCtx.ty`: `Elem()` gives
   `reflElem e cancelCtx.ty c0`. `conversion.EnforcePtr.spec` gives the same.
3. `reflect.Value.Type.spec`: `reflType rt cancelCtx.ty`.
4. `reflect.New.spec`: `reflPtr w cancelCtx.ty p ∗ reflNew cancelCtx.ty p`, `p ≠ null`. Then
   `reflNew_pointsto` (`Proof/reflect/Values.lean:67`, any `V` with `IntoValTyped V T`) at
   `V := context.cancelCtx` gives `p ↦ zero_val context.cancelCtx`. `Value.Interface.spec` gives the Go
   value `interface.mkOk (*cancelCtx) #p`.
5. Split the struct (`cancelCtx_typed_pointsto`): `mu`, `done`, `children`, `err`, `cause` (and
   `Context`). Then:
   - `init_Mutex` on `mu`, with lock invariant `cancelCtxLockInv p γ P True` at `closed = false`,
     `od = none`, `children = map.nil` (`childrenInv`'s left disjunct) and `cause = nil`;
   - `inv cancelCtxN (cancelCtxInv p γ P A)` at `od = none`, `e = nil`, with the zero `atomic.Value`
     cells as `ownValue … nil`;
   - fresh `dghostVar`s for `γ.doneGn` (`none`) and `γ.closedGn` (`false`), split in halves;
   - `isClosedchanInit` from `isPkgInit context`.

   This is `isCancelCtxOfA p γ P A` for **any** `A`: `A` appears only as `⌜A e⌝` with `e ≠ nil`.
6. The law: `madeCancelCtx p`.

`v3rpc.ctxDoneErr m s` is then buildable for a wrapper `m` (the test's `myCtx`) with these methods:
`Deadline` its own; `Done`/`Err` delegated to `p` (`wp_cancelCtx_Done`/`_Err` from step 5); `Value(k)`
returning `p.Value(k)` when `k` is a `*int` (`&cancelCtxKey` is one) and `nil` otherwise. `"#HParentCC"`
holds because `p.done` holds the channel `p.Done()` made.

The attack then needs a consumer that misbehaves on this `p`. None does:

- `WithTimeout(m)`, `WithCancel(m)`, `Cause` and cancelling the children (`removeChild`) use only `p.mu`,
  `p.done`, `p.err`, `p.children` and `p.cause`;
- nobody can cancel `p` itself in Go (`cancel` is unexported), so it stays a valid, never-cancelled
  parent.

`p` used *directly* as a context does panic, at `Deadline()` (`TestZeroCancelCtxDeadlinePanics`: nil
pointer dereference). But no spec lets a proof use it so: `isContext p` and `ctxDoneErr p` both need a
`"#HDeadline"` WP that is not provable for it. `context.WithCancel.spec` needs `isContext` of its parent
as well as `isCancelCtxCtx`.

Side observation (not this law's problem): step 5 also gives Perennial's own `isCancelCtx p`, so the
same reflection route reaches Perennial's `context` specs. They likewise need `isContext` for a parent,
and the same argument applies.

## Other attacks tried, and why each fails

| Attack | Why it fails |
|---|---|
| The `A` index: `fun _ => False`, or an `A` depending on ghost state | `A` is a Lean predicate, so it cannot mention ghost state. It is used only as `⌜A e⌝` once `err` is set: it restricts what the invariant holds and never helps build it. Any `A` with `err = nil` was already enough above. Stating the law per `A` adds nothing over the `isCancelCtx` form (`isCancelCtx c ⊢ ∃ A, isCancelCtxOfA …`, `isCancelCtxOf_A`). |
| A nil `*cancelCtx` (the T-h5 panic, `TestRenewHTTPNilCancelCtxPanics`) | `isCancelCtxOfA null …` needs heap points-tos at `structFieldRef context.cancelCtx f null`. `structFieldRef` of a non-plain struct is an uninterpreted function (`GoSemanticsFunctions`; `structFieldRef_plain` covers plain structs only, and `cancelCtx` has interface and map fields). No spec gives a cell there. A typed nil `*cancelCtx` via `reflect.Zero` would need `reflType` of `*cancelCtx`, and no `reflect` spec produces a pointer type's `reflType`. Even with one, the points-tos are still missing. |
| A `reflect` copy of a real one (the docstring's data race) | Making it needs `Value.Set` of a non-zero struct. `reflect.Value.Set.spec` sets only a zero value or a slice. The real one's lock invariant owns the `children` map (`ownMap`) and its `inv` owns `done`/`err`, so a proof cannot duplicate them. |
| Allocating a `cancelCtx` in translated client code | Go cannot name the unexported type. The only `GoAlloc` of `cancelCtx.ty`, `timerCtx.ty` and `afterFuncCtx.ty` is in Perennial's `Code/context.lean`: `withCancel` (:437), `AfterFunc` (:562), `WithDeadlineCause` (:1369). `context.toml` keeps `WithValue`, `stringify` and `contextName` out, none of which allocate one. `AfterFunc`'s `afterFuncCtx` embeds a `cancelCtx` the docstring's list of constructors omits. It is made by `context` all the same, so it is no counterexample, only a gap in the list. |
| Another Go type sharing `cancelCtx`'s Lean representation (`TypeRepr t context.cancelCtx`) | `TypeRepr` for it comes only from `TypeReprUnderlying` of `cancelCtx`'s underlying struct, whose `children` key is the unexported named type `context.canceler`. No client type has that underlying type. |
| `unsafe` | `convert_unsafe_to_pointer` needs `IsPlain`. A conversion to `*cancelCtx` is stuck (`Golang/Defn/Plain.lean`). |
| Cross-world (`notes/axiom-review/ctx-descs.md`): build `isCancelCtxOfA` in a fresh heap world (`withHeapName hG γ`) and carry `madeCancelCtx` back | The conclusion is an opaque `IProp`, not a pure fact, so it transfers only if `madeCancelCtxRaw` does not take `hG`: check with `#check @context.madeCancelCtxRaw`, not done here. Either way, a fresh-world heap cell needs `⌜0 < l.addr < maxAddr⌝` (`heapPointsto`) of the uninterpreted `structFieldRef` addresses. Those are known only for a location that already has a real `cancelCtx`-typed allocation in the run, made by `context` or by `reflect.New`, which the route above covers. No new location is reached. |
| Misusing `madeCancelCtx` once obtained | No elimination law exists. It yields no points-to, no pure fact and no right to cancel. It matters only as the premise of the consumers above. |

## Not tried

- The Lean proof of the route (steps 1-6). Its pieces are proved Perennial lemmas and the `reflect`
  axioms, but it was not written or checked. In particular, step 2 assumes Goose's `real` → `any`
  conversion keeps the interface value, and step 5 assumes `zero_val atomic.Value = {v' := nil}`.
- The Go behaviour of every consumer's whole code path (`net/http` under `RenewHTTP`). It was checked
  only that the context functions on the found `*cancelCtx` never read its `Context`. A consumer whose
  Go calls `Value` at another key on the *found* `*cancelCtx`, not on the context chain, would break
  condition (2). None was found.

## Proposed changes (not applied)

1. Change `madeCancelCtx`'s docstring to say "made by `context` (any of its allocations of a
   `cancelCtx`, including `AfterFunc`'s), or a zero `cancelCtx` from `reflect.New`". State condition (2)
   as the obligation of every spec that takes it.
2. Change the law's docstring to drop "no spec … gives a program a `cancelCtx`'s field points-tos", and
   name `reflect.New.spec` with `reflNew_pointsto` as the one route, with why it is harmless.
3. Alternatively, narrow the law at the source: have `reflNew_pointsto` exclude `context`'s unexported
   types. This is not recommended, because the `reflect` axiom is true of Go, so narrowing it would only
   hide the case.

The Go test (scratchpad, not committed):
`/tmp/claude-0/-shared-etcd-grove/b97c80e7-cd07-49fa-a39b-20ca76a68f5e/scratchpad/zerocc/zerocc_test.go`.
Its output at `GOTOOLCHAIN=go1.27.3 go test -race -v`:

```
--- PASS: TestZeroCancelCtxAsParent (0.04s)
    zerocc_test.go:62: panic: runtime error: invalid memory address or nil pointer dereference
--- PASS: TestZeroCancelCtxDeadlinePanics (0.00s)
```
