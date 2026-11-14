/-
`errors.As(err, &linkErr)` for a `*os.LinkError` `err` and a `**os.LinkError` target (`renameWAL`'s test
of `os.Rename`'s error, S/wal.go:337-339): **a hypothesis** of `WAL.renameWAL`'s proof, not proved here
and not an axiom. It returns `true` and stores `err`'s pointer in the target.

Why it holds: Go's `as` checks first whether `err`'s dynamic type is assignable to the target's element
type (`*os.LinkError` to `*os.LinkError`: equal) and, if so, stores `err`'s value and returns `true`,
without calling any of `err`'s methods or reading through its pointer.

Why not Perennial's `errors.As.spec`: it asks for the whole error tree of `err` (`isErrorTree S`, closed
under `Unwrap`), even when the first error matches; a `*LinkError`'s `Unwrap` returns its `Err` field, so
the tree needs the field's persistent points-to and the errno below it, which `os.Rename`'s spec does
not export. The general fix is a Perennial change (`errors.As.spec` with a first-match case:
`notes/perennial-changes.md`); the statement below is what it would give.
Lean-first (W4 of `notes/wal-fsext-plan.md`).
-/
module

public import LinuxFs.GeneratedProof.os
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

/-- See the file header. -/
abbrev errors.AsLinkError.spec : Prop :=
  ∀ (le l v : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ l ↦ v }}
      (App (App (Val (@! _root_.Perennial.errors.As))
        (Val #(interface.mkOk (go.GoType.PointerType os.LinkError.ty) #le)))
        (Val #(interface.mkOk (go.GoType.PointerType (go.GoType.PointerType os.LinkError.ty)) #l)))
    {{ RET #true; l ↦ le }}

end spec

end EtcdGrove
end Perennial
