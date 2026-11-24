/-
`errors.As(err, target)` of any leaf error whose type is outside the target's type set (k8s 7f-5a-P
step 5: `interpretWatchError`'s `errors.As(err, &corruptobjDeletedErr)` on the errors the watcher's
producers send: a `*status.Error` (grpc's; rpctypes' `ErrGRPC*` values are `*status.Error` at
runtime), an `rpctypes.EtcdError` (from `rpctypes.Error(..)`, or `ErrCompacted`/`ErrFutureRev`),
`context.DeadlineExceeded`, a `*StatusError`, an `*errors.errorString`). The generalization of
`errors.AsLeaf.spec` (an `*errors.errorString`) to any dynamic type.

Trusted text (approved by etcd-grove-81, 2026-11-15, after an independent axiom review: no
counterexample) until prove-k8s2 (2026-11-20), since then a theorem: the leaf case of
`errors.AsNoMatch` (`Spec/errors/AsNoMatch.lean`). Go (`errors/wrap.go`, `As`): for a non-nil `err`, `As` panics unless the target is a
non-nil pointer to an interface or to a type implementing `error` (`AsTarget`); then it walks `err`'s
tree: `err` is set into the target and `true` returned only if `reflectlite.TypeOf(err)` is assignable
to the target's element type `T` (for an interface `T`: `err`'s type implements it, the type set; for
a non-interface `T`: identical types, or identical underlying types with one of them unnamed); else an
`As(any) bool` method may answer, else `Unwrap` continues the walk, else `false`, the target unchanged.
A leaf error (`isLeafError`: no `As`, no `Unwrap`) outside `T`'s type set, and (non-interface `T`) of
another underlying type, gives `false`. The leaf premise relies on Goose's `MethodSetIs` listing every
method of a type, promoted ones included (a promoted `As` or `Unwrap` is in Go's method set and is
called). Go evidence: `examples/premisefix/watcherctx/asleafty_test.go` (each of the types above
against `*corruptObjectDeletedError`: a leaf, outside the type set, `As` false and the target
unwritten; and the negatives: a wrapper, an `As` method, the target's own type). Lean-first.
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

/-- See the file header. -/
abbrev errors.AsLeafTy.spec : Prop :=
  ∀ (ii : GoInterfaceOk) (l : Loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    _root_.Perennial.errors.AsTarget T →
    _root_.Perennial.errors.isLeafError ii →
    go.typeSetContains ii.ty T = false →
    (go.isInterfaceType (underlying T) = false → underlying ii.ty ≠ underlying T ∧
      (_root_.Perennial.errors.undecidedKind (underlying T) = false ∨
        go.kindOf (underlying ii.ty) ≠ go.kindOf (underlying T))) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ l ↦ v }}
      (App (App (Val (@! _root_.Perennial.errors.As)) (Val #(GoInterface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #false; l ↦ v }}

end spec

end EtcdGrove
end Perennial
