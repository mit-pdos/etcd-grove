/-
**A `*bufio.Reader` over a stream reader** (WAL leaf specs, 2026-11-13; the part's translation of
`bufio`): `bufio.ownReader b ri S E r`, the reader at `b` reading from `ri` (`io.readerStream ri S
E`, `Proof/io/ReaderStream.lean`) after delivering `r`. It owns the struct and its buffer `bs`, and
the underlying reader's state is `S` of `r` and the buffered bytes `bs[r:w]` (what `ri` delivered
so far); a pending error (`b.err`, set by a `Read` of `ri` that also delivered bytes) is one `E`
allows there. The buffer is at most `bufio`'s default size, 4 KiB (`NewReader`), which bounds
where a refill reads (`bufio.Reader.Read.spec`). So the `*bufio.Reader` is itself a stream reader of the same bytes and errors
(`bufio.Reader.Read.spec`). Lean-first.
-/
module

public import Proof.io.ReaderStream
public import LinuxFs.Proof.bufio.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
def bufio.ownReader (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → Prop) (r : List w8) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
    ∃ (v : _root_.Perennial.bufio.Reader) (bs : List w8),
    b ↦ v ∗ v.buf' ↦* bs ∗
    ⌜v.rd' = GoInterface.ok ri ∧ 0 ≤ sint.Z v.r' ∧ sint.Z v.r' ≤ sint.Z v.w' ∧
      sint.nat v.w' ≤ bs.length ∧ 0 < bs.length ∧ bs.length ≤ 2 ^ 12⌝ ∗
    S (r ++ subslice (sint.nat v.r') (sint.nat v.w') bs) ∗
    ⌜v.err' ≠ GoInterface.nil → E (r ++ subslice (sint.nat v.r') (sint.nat v.w') bs) v.err'⌝)

/-- The underlying stream's state, lent out of the reader (`r` and its buffered bytes `q`). -/
theorem bufio.ownReader_open (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → Prop) (r : List w8) :
    bufio.ownReader b ri S E r ⊢ ∃ q : List w8, S (r ++ q) ∗ (S (r ++ q) -∗ bufio.ownReader b ri S E r) := by
  unfold bufio.ownReader
  iintro ⟨#Hpkg, %v, %bs, Hv, Hbuf, %Hwf, HS, %Herr⟩
  iexists subslice (sint.nat v.r') (sint.nat v.w') bs
  iframe HS
  iintro HS
  iframe Hpkg
  iexists v, bs
  iframe
  ipureintro; exact ⟨Hwf, Herr⟩

end defs

end EtcdGrove
end Perennial
