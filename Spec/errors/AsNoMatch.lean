/-
`errors.As(err, target)` of an error in whose tree nothing matches the target's element type `T`,
to depth one: `nil`; a leaf error (`isLeafError`: no `As(any) bool`, no `Unwrap() error`, no
`Unwrap() []error`) outside `T`'s type set; or a wrapper outside `T`'s type set with
`Unwrap() error` and no `As(any) bool`, whose `Unwrap()` returns `nil` or such a leaf (for a
non-interface `T`, every error asked has another underlying type than `T`). Result `false`, the
target unchanged. (prove-k8s2, 2026-11-20: it replaces `errors.AsLeafTy`, its leaf case, now a
theorem, and lets `apierrors`' `APIStatus` checks (`IsTimeout`, `IsTooManyRequests`,
`HasStatusCause`, `SuggestsClientDelay`), until then axioms, be proved over their real bodies, whose
`.plain` errors include such wrappers, `*storage.StorageError`s; `notes/axiom-review/asnomatch.md`.)

Proved since Perennial 52d62e83c (`Proof/errors/AsNoMatch.lean`, over `errors.wp_As`'s no-match
case); until then an axiom, of which the following was the evidence. Go (go1.27.3, `src/errors/wrap.go:102-160`): `As` returns `false` at once on a `nil`
`err` (`:103-105`); otherwise it panics unless the target is a non-nil pointer (`l ↦ v` makes `l`
non-null) to a type that is an interface or implements `error` (`AsTarget T`, `:106-116`), then
runs `as` (`:121-160`), a loop over the error: (1) if `reflectlite.TypeOf(err).AssignableTo(T)` the
error is stored into the target and `true` returned: excluded here, since the error's dynamic type
is outside `T`'s type set (for an interface `T`, assignability is implementing `T`) and, for a
non-interface `T`, has another underlying type (assignability is then identical types, or identical
underlying types with one unnamed, or a bidirectional channel whose element type matches, with one
unnamed: a dynamic type implementing `error` and a `T` implementing `error` are both named when they
are channel types, since an unnamed type has no methods); (2) if the error has a method
`As(any) bool` it is called, `true` returning `true`: excluded, no such method; (3) the type switch:
`Unwrap() error` sets `err = x.Unwrap()` and returns `false` if it is `nil`, else loops;
`Unwrap() []error` recurses into the elements; otherwise `false`. A leaf takes the last branch at
once; a wrapper (its method set has `Unwrap() error`, so not the other `Unwrap`: one signature per
name) calls its `Unwrap` once, through its method of `ii.ty` (the call this spec takes the WP of,
consumed once, with the target's points-to framed: `Unwrap` cannot reach it through the spec), and
the result, `nil` or a leaf of the same kind, gives `false` at the next iteration without any
method call. No other method of any error is called (`TypeOf`, `AssignableTo` and the type
assertions call none), and the target is written only in case (1). The leaf premise relies on Goose's
`MethodSetIs` listing every method of a type, promoted ones included (a promoted `As` or `Unwrap` is
in Go's method set and is called).

Go evidence: `examples/premisefix/watcherctx/asnomatch_test.go` (wrappers over `nil` and over a leaf,
an interface and a pointer target: `false`, the target unwritten, `Unwrap` called once; `nil`; and the
negative, a wrapper of a match), `asleafty_test.go` (leaves, the former `AsLeafTy`) and
`examples/k8s/etcd3/trustspecs_test.go` `TestStatusChecksPlain`/`TestPlainWrapperTypedNil` (wrappers:
`*storage.StorageError` over `nil` and over an `errors.New`, every `APIStatus` check false; a typed
nil wrapper panics in `Unwrap`, which no WP of that call allows). Lean-first.
-/
module

public import Perennial.Proof.errors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- **An error `errors.As` ends at without a match against `T`**: `nil`, or a leaf error (no
`As(any) bool`, no `Unwrap`) whose dynamic type is outside `T`'s type set and, for a non-interface
`T`, of another underlying type and either of another kind or of a kind other than struct, channel
and function (Perennial's `AsDecided`: where the `reflectlite` model decides it); the model's
reflection on its dynamic type is defined (`asModelled`), and for an interface `T` its dynamic type
has a Lean representation (Perennial's `asTyRepr`: `reflectlite`'s `implements` allocates a zero
value of it). -/
def errors.asNoMatchLeaf (T : go.GoType) (e : GoInterface) : Prop :=
  e = interface.nil ∨ ∃ ii : GoInterfaceOk, e = GoInterface.ok ii ∧
    _root_.Perennial.errors.isLeafError ii ∧ go.typeSetContains ii.ty T = false ∧
    _root_.Perennial.errors.asModelled ii.ty ∧
    _root_.Perennial.errors.asTyRepr (GF := GF) T ii ∧
    (go.isInterfaceType (underlying T) = false → underlying ii.ty ≠ underlying T ∧
      (_root_.Perennial.errors.undecidedKind (underlying T) = false ∨
        go.kindOf (underlying ii.ty) ≠ go.kindOf (underlying T)))

/-- **A wrapper `errors.As` unwraps once, to no match against `T`**: a dynamic type outside `T`'s
type set (of another underlying type than a non-interface `T`) with `Unwrap() error` and no
`As(any) bool`, whose `Unwrap()` returns `nil` or a leaf of `asNoMatchLeaf T` (one call). -/
def errors.asNoMatchWrap (T : go.GoType) (err : GoInterface) : IProp GF :=
  iprop(∃ ii : GoInterfaceOk,
    ⌜err = GoInterface.ok ii ∧ go.typeSetContains ii.ty T = false ∧
      _root_.Perennial.errors.asModelled ii.ty ∧
      _root_.Perennial.errors.asTyRepr (GF := GF) T ii ∧
      (go.isInterfaceType (underlying T) = false → underlying ii.ty ≠ underlying T ∧
        (_root_.Perennial.errors.undecidedKind (underlying T) = false ∨
          go.kindOf (underlying ii.ty) ≠ go.kindOf (underlying T))) ∧
      GoSemanticsFunctions.methodSet ii.ty !! go!"As" ≠
        some (go.signature.Signature [go.any] false [go.bool]) ∧
      GoSemanticsFunctions.methodSet ii.ty !! go!"Unwrap" =
        some (go.signature.Signature [] false [go.error])⌝ ∗
    ∀ Φ : val → IProp GF, (∀ e : GoInterface, ⌜errors.asNoMatchLeaf (GF := GF) T e⌝ -∗ Φ #e) -∗
      WP (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #())) {{ Φ }})

/-- See the file header. -/
abbrev errors.AsNoMatch.spec : Prop :=
  ∀ (err : GoInterface) (l : Loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    _root_.Perennial.errors.AsTarget T →
    (∃ k, go.kindOf (underlying T) = some k) → go.isUntypedNil (underlying T) = false →
    go.layoutModelled T = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ l ↦ v ∗
        (⌜errors.asNoMatchLeaf (GF := GF) T err⌝ ∨ errors.asNoMatchWrap T err) }}
      (App (App (Val (@! _root_.Perennial.errors.As)) (Val #err))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #false; l ↦ v }}

end spec

end EtcdGrove
end Perennial
