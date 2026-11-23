/-
`errors.Is(err, u)` for a `*PathError` of a nonzero errno (`os.errnoPathErr err e`, what the part's `os` models
return on a failed system call) and any pointer target `u`: it returns. Stated as its error tree (`errTreeTerm`,
`Spec/errors/ErrTree.lean`; since 2026-11-22, so that a `fmt.Errorf` wrapping it has one: ledger 2026-11-22, "`fmt.ErrorfErrsNot.spec`/`fmt.ErrorfErrsTerm.spec` -- premises no proof can use"; `errIsTerm_of_tree` gives the triple `errIsTerm`). **A
hypothesis** (of `fileutil.ReadDir`'s proofs and the WAL's readers, `ReadBridge.lean`), not proved here and not
an axiom; true of Go: `errors.Is` compares `err` with `u` (two pointers, or values of different types), the
`*PathError` has no `Is` method, its `Unwrap` returns the `Errno`, which `errors.Is` compares with `u` (an
`Errno` is comparable), and `Errno.Is(u)` compares `u` with `oserror`'s `ErrPermission`, `ErrExist`,
`ErrNotExist` and `errors.ErrUnsupported` (pointers) and returns; an `Errno` has no `Unwrap`. Its proof needs
Perennial's `errors.Is.spec` over that two-error tree, hence translations of `(*PathError).Unwrap` and
`Errno.Is` (names-only in the part): as `errors.IsPathErrnoEof.spec` and `errors.IsErrno.spec`
(`notes/perennial-changes.md`). What `validSnapshotEntries`' errors need for `ValidSnapshotEntries`' retry test
`errors.Is(err, os.ErrNotExist)` (ledger 2026-11-14, "no `errors.Is` termination on their errors";
`wal-vsnap4`). Lean-first.
-/
module

public import Proof.os.ErrnoPathErr
public import Proof.os.PkgInit
public import Spec.fmt.ErrorfErrsNot
public import Spec.errors.ErrTree

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
abbrev errors.IsPathErrnoTerm.spec : Prop :=
  ∀ (err : GoInterface) (e : w64), e ≠ 0 →
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.os -∗ os.errnoPathErr (GF := GF) err e -∗ errTreeTerm (GF := GF) err

end spec

end EtcdGrove
end Perennial
