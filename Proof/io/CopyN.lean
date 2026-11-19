/-
Trust boundary: `io.CopyN` of a `*SectionReader` (an axiom; see `Spec/io/CopyN.lean`). S4,
2026-11-18; proposed in Perennial as a translation of `CopyN`, `Copy`, `copyBuffer`, `LimitReader`
and the `Read`s of `LimitedReader` and `SectionReader` with bodies, and this spec proved over the
`ReaderAt` and `Writer` contracts (`notes/perennial-changes.md`, "`io.NewSectionReader`, `io.CopyN`").
-/
module

public import Spec.io.CopyN

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (S4): Go's `io.CopyN(dst, src, n)` (go1.27 `io/io.go`, the file header of
`Spec/io/CopyN.lean`) of a fresh `*SectionReader` (`io.secReader`, from `NewSectionReader` at
`0 ≤ off`, `0 ≤ n`, `off + n < 2^63`) and a writer without `ReadFrom` loops `Read`/`Write` over a
buffer of at most 32 KiB: the `k`-th `Read` is one `ReadAt(p, off + written)` with `len(p) ≤ n -
written` (both the limited and the section reader truncate to it), and it is the end of the section
when nothing is left (`io.EOF`, without a `ReadAt`); the `Write` of the `nr` bytes read appends
`nw ≤ nr` of them (the writer's contract), `written += nw`, and the loop stops unless `nw = nr` with
a `nil` error. So the bytes appended are the first `written ≤ n` bytes of the section, in order, each
from a `ReadAt` (related by `Hd` to its offset); `CopyN` returns `(n, nil)` when `written = n`, and
otherwise a non-`nil` error (the copy's, or `io.EOF`, non-`nil` once `io` is initialized). The
comparisons `er != nil`, `er != EOF` cannot panic (`EOF`'s dynamic type, `*errorString`, is
comparable). What would discharge it: `io`'s copy translated with its bodies, and this spec proved
by Löb induction over the loop from `readerAtOk` and `writerOk`. -/
axiom io.CopyN.wp_proof : io.CopyN.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
