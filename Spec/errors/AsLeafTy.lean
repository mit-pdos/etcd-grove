/-
`errors.As(err, target)` of any leaf error whose type is outside the target's type set (k8s 7f-5a-P
step 5: `interpretWatchError`'s `errors.As(err, &corruptobjDeletedErr)` on the watcher's errors: a
`*status.Error`, an `rpctypes.EtcdError`, `context.DeadlineExceeded`, a `*StatusError`). The
generalization of `errors.AsLeaf.spec` (an `*errors.errorString`) to any dynamic type.

**DRAFT trusted text, for etcd-grove-81's review (not an axiom; no proof takes it yet but as a
hypothesis).** Go (`errors/wrap.go`, `As`): for a non-nil `err`, `As` panics unless the target is a
non-nil pointer to an interface or to a type implementing `error` (`AsTarget`); then it walks `err`'s
tree: `err` is set into the target and `true` returned only if `reflectlite.TypeOf(err)` is assignable
to the target's element type `T` (for an interface `T`: `err`'s type implements it, the type set; for
a non-interface `T`: identical types, or identical underlying types with one of them unnamed); else an
`As(any) bool` method may answer, else `Unwrap` continues the walk, else `false`, the target unchanged.
A leaf error (`isLeafError`: no `As`, no `Unwrap`) outside `T`'s type set, and (non-interface `T`) of
another underlying type, gives `false`. Lean-first.
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
    (go.isInterfaceType (underlying T) = false → underlying ii.ty ≠ underlying T) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ l ↦ v }}
      (App (App (Val (@! _root_.Perennial.errors.As)) (Val #(GoInterface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #false; l ↦ v }}

end spec

end EtcdGrove
end Perennial
