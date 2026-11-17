/-
`io.ReadFull(r, buf)` of a reader read as a stream (`io.readerStream`, `Proof/io/ReaderStream.lean`):
the trust boundary (Perennial translates `io` names-only for it; `Proof/io/ReadFull.lean`). Go 1.27
`io.go`: `ReadFull(r, buf)` is `ReadAtLeast(r, buf, len(buf))`, which calls `r.Read(buf[n:])` until
`n = len(buf)` or an error, then returns `nil` if all came, else the last error, with `io.EOF`
replaced by `io.ErrUnexpectedEOF` if some bytes came (`n > 0 && err == EOF`: an interface
comparison with `EOF`'s `*errorString`, which cannot panic). WAL leaf specs, 2026-11-13 (decoder.go:117);
the reader's errors carry an Iris evidence (`io.readerStream`'s `E`) since 2026-11-14 (ledger, "the
readers' errors and `errors.Is`"; **adopted provisionally, pending the user's review**). Lean-first.
-/
module

public import Proof.io.ReaderStream

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

/-- `ReadFull(r, buf)` of a stream reader `r` (`io.readerStream ri S E`), from `S r0`: delivers
`ys` into the front of `buf` and leaves `S (r0 ++ ys)`, returning `len(ys)` and an error as
`io.readFullRes` says (`nil` when all came; else the reader's last error with its evidence, or
`io.ErrUnexpectedEOF` for an `io.EOF` after some bytes) (`eof`, `ueof`: the values of `io.EOF`, `io.ErrUnexpectedEOF`). The end of
the read stays below `2^62` (`len(r0) + len(buf) < 2^62`, as `io.readerStream` asks of each
`Read`). It may not
return (a reader that keeps returning `0, nil`: partial correctness). -/
abbrev io.ReadFull.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r0 : List w8) (p : GoSlice) (xs : List w8) (eof ueof : GoInterface),
  ⊢ io.readerStream ri S E -∗
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr _root_.Perennial.io.EOF ↦□ eof ∗
        globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ ueof ∗
        ⌜r0.length + xs.length < 2 ^ 62⌝ ∗ S r0 ∗ p ↦* xs }}
      (App (App (Val (@! _root_.Perennial.io.ReadFull)) (Val #(GoInterface.ok ri))) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
          io.readFullRes E eof ueof r0 ys xs.length err ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r0 ++ ys) }}

end spec

end EtcdGrove
end Perennial
