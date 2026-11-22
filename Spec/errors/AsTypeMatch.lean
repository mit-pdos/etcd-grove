/-
`errors.AsType[T](err)` for an `err` whose dynamic type is `T` itself, a non-interface type: it
returns `err`'s value and `true` (`renameWAL`'s test of `os.Rename`'s `*os.LinkError`, S/wal.go:351).
Proved from the translation of `AsType` and `asType` (`Proof/errors/AsTypeMatch.lean`), where until
etcd-grove#29 `renameWAL`'s `errors.As(err, &linkErr)` was the hypothesis `errors.AsLinkError.spec`.

Why not Perennial's `errors.AsType.spec`: it allows any result, and asks for the whole error tree of
`err` (`isErrorTree S`, closed under `Unwrap`), even when the first error matches; a `*LinkError`'s
`Unwrap` returns its `Err` field, so the tree needs the field's persistent points-to and the errno
below it, which `os.Rename`'s spec does not export. Go's `asType` checks `err.(T)` first and returns
on a match, without calling any of `err`'s methods: the first-match case below, which is a
candidate for Perennial (`notes/perennial-changes.md`). Lean-first.
-/
module

public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- See the file header. -/
abbrev errors.AsTypeMatch.spec : Prop :=
  ∀ (ii : GoInterfaceOk) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.GoType}
    [IntoValTyped (GF := GF) T' T] (x : T'),
    go.isInterfaceType (underlying T) = false → ii.ty = T → ii.v = #x →
    {{ (True : IProp GF) }}
      (App (Val #(functions _root_.Perennial.errors.AsType [T])) (Val #(GoInterface.ok ii)))
    {{ RET (PairV #x #true); True }}

end spec

end EtcdGrove
end Perennial
