/-
`errors.Is(err, io.EOF)` and `errors.Is(err, io.ErrUnexpectedEOF)` for a `*PathError` of a nonzero errno
(`os.errnoPathErr err e`, what the part's `os` models return on a failed system call): they answer
`false`. (`io.ErrUnexpectedEOF` since 2026-11-14, `wal-vsnap2`: the decoder's readers' errors carry that
answer too, `notUeof`; ledger "`decoder.Decode.spec`: no `io.ErrUnexpectedEOF` answer". The argument is
the same: `io.ErrUnexpectedEOF` is a fifth `errors.New` allocation.) **A hypothesis** (of the WAL's
`openWALFiles`/`openAtIndex` proofs, through the `os.File` reader bridge, `ReadBridge.lean`), not proved
here and not an axiom; true of Go: `errors.Is` walks `&PathError{Op, Path, Errno(e)}`: the
`*PathError` is not `io.EOF` (another type) and has no `Is` method; its `Unwrap` returns the `Errno`,
which is not `io.EOF` either; `Errno.Is(io.EOF)` compares `io.EOF` with `oserror`'s `ErrPermission`,
`ErrExist`, `ErrNotExist` and `errors.ErrUnsupported`, four other `errors.New` allocations, and
answers `false`; an `Errno` has no `Unwrap`. Its proof needs Perennial's `errors.Is.spec` over that
two-error tree, hence translations of `(*PathError).Unwrap` and `Errno.Is` (both names-only in the
part, `Code/io/fs.toml`, `syscall.toml`) and `oserror`'s package facts: as
`errors.IsPathErrnoNotExist.spec` and `errors.IsErrno.spec` (`notes/perennial-changes.md`). What the
WAL's decoder needs of its readers' errors (`decRdE`, `DecDefs.lean`; ledger 2026-11-14, "the readers'
errors and `errors.Is`"). Lean-first.
-/
module

public import Proof.os.ErrnoPathErr
public import Proof.os.PkgInit

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
abbrev errors.IsPathErrnoEof.spec : Prop :=
  ∀ (err eof : GoInterface) (e : w64), e ≠ 0 →
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.os -∗
      (globalAddr _root_.Perennial.io.EOF ↦□ eof ∨ globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ eof) -∗
      os.errnoPathErr (GF := GF) err e -∗
      {{ (True : IProp GF) }}
        (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #eof))
      {{ (b : Bool), RET #b; ⌜b = false⌝ }}

end spec

end EtcdGrove
end Perennial
