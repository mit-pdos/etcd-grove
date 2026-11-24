/-
**Interim pending hypothesis** (not an axiom: a hypothesis of the linked results that use it, until
its retirement below; approved as interim on #24, 2026-11-24, subject to an adversarial review).

`context.WithValue(parent, key, val)` (go1.27.3 `src/context/context.go`) for a non-nil `parent`, a
`key` whose dynamic type is a pointer type (`*T` for any `T`; the pointer itself may be `nil`) and
any `val` (`nil` included): Go's checks pass (`parent != nil`, `key != nil` as an interface, and
`reflectlite.TypeOf(key).Comparable()`, true of every pointer type), and it returns
`&valueCtx{parent, key, val}` as a `Context`: a fresh `*valueCtx` `q` whose three fields hold
`parent`, `key` and `val`. The fields are read-only from then on (`↦□`): the `context` package writes
a `valueCtx`'s fields nowhere and builds one only in `WithValue`, and they are unexported.

Not covered (each panics in Go, and no caller passes it): a nil `parent`, a nil `key`, a key of a
non-comparable dynamic type (and the spec says nothing of other comparable key types, which nothing
here needs).

Evidence (go1.27.3, `GOTOOLCHAIN=go1.27.3 go test -v ./...` in
`/shared/tmp/ps2/s5d/gotest/ctxhyp`): `TestWithValuePtrKey` (net/http's `ServerContextKey` and
`LocalAddrContextKey`, pointers to `int`, slices, maps, funcs, structs, nil pointers; parents
`Background()`, `TODO()`, a `*cancelCtx`, a `*valueCtx`; values `nil`, ints, strings, pointers,
slices: the result's dynamic type is `*context.valueCtx`, its fields `Context`, `key`, `val` are the
arguments, and two calls give distinct pointers), `TestWithValueExcluded` (the three panics),
`TestValueCtxFieldsNeverWritten` (a type-checked scan of the package's sources: no assignment to, or
address taken of, a `valueCtx` field; one `valueCtx` literal, `WithValue`'s), `TestNetHTTPChain`.

**Why a hypothesis.** Perennial translates `WithValue` names-only (`context.toml`:
`"!WithValue"`, for its `reflectlite.TypeOf(key).Comparable()`), so its body is not in the model.
**Retired by** Perennial's `internal/reflectlite` model (reflection stage S0.5, Perennial branch
`reflect-s05`): `WithValue` translated with its body and this triple proved over it
(`notes/perennial-changes.md`, "`sync.NewCond.spec` does not say its result is not `nil`;
`context.WithValue` names-only").
-/
module

public import Perennial.Proof.context.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : context.Assumptions]

/-- See the file header. -/
abbrev context.WithValue.specPtr : Prop :=
  ∀ (parent : GoInterfaceOk) (kt : go.GoType) (k : Loc) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (App (App (Val (@! context.WithValue)) (Val #(GoInterface.ok parent)))
      (Val #(interface.mkOk (go.GoType.PointerType kt) #k))) (Val #v))
  {{ (q : Loc), RET #(interface.mkOk (go.GoType.PointerType context.valueCtx.ty) #q);
      structFieldRef context.valueCtx go!"Context" q ↦□ (GoInterface.ok parent) ∗
      structFieldRef context.valueCtx go!"key" q ↦□
        (interface.mkOk (go.GoType.PointerType kt) #k) ∗
      structFieldRef context.valueCtx go!"val" q ↦□ v }}

end spec

end Perennial
