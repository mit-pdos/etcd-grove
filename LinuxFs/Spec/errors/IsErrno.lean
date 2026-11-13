/-
`errors.Is(err, target)` for an errno `err` (`errnoErr e`, `e ≠ 0`) and an errno `target`
(`syscall.EWOULDBLOCK` in `fileutil`'s `ofdTryLockFile`/`flockTryLockFile`): **a hypothesis** of
`fileutil.TryLockFile`'s proof, not proved here and not an axiom. It returns some boolean.

Why not Perennial's `errors.Is.spec`: it admits only `nil` and pointer targets (`IsPointerError`),
because Go's `is` compares `target` with the errors of the tree of its type with `==`, which panics
on non-comparable values. An errno is a `uintptr`, comparable, so Go's walk returns: `err ==
target` (two `Errno`s), then `Errno.Is(target)` (a `switch` comparing `target` with `oserror`'s
pointer errors and `errors.ErrUnsupported`, of other types: `false`), then no `Unwrap`. The general
fix is a Perennial change (`errors.is.spec` for any target whose errors of its type in the tree hold
comparable values; `syscall.Errno.Is`'s spec), `notes/perennial-changes.md`; the statement below is
what it would give (weakened to "some boolean", all `TryLockFile` needs).
Lean-first (W5 of `notes/wal-fsext-plan.md`).
-/
module

public import LinuxFs.Proof.syscall.Base
public import LinuxFs.Proof.syscall.PkgInit
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
abbrev errors.IsErrno.spec : Prop :=
  ∀ (e t : w64), e ≠ 0 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ isPkgInit (PROP := IProp GF) pkg_id.syscall }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #(errnoErr e)))
        (Val #(interface.mkOk syscall.Errno.ty #t)))
    {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
