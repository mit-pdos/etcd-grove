/-
**A `*bufio.Reader` with its buffered bytes and pending error shown** (net/http's `ReadResponse`,
2026-11-23): `bufio.ownReaderBuf b ri S E r q e` is `bufio.ownReader b ri S E r`
(`Proof/bufio/Defs.lean`) with the bytes it holds `q` (read from `ri`, not yet delivered: the
underlying stream is at `S (r ++ q)`) and its pending error `e` (`b.err`, with `E`'s evidence at
`r ++ q`, `io.errAt`) named, for the specs that say what they leave in the buffer (`fill`, `Peek`).
`bufio.ownReader_buf`: `ownReader r` is `ownReaderBuf r q e` for some `q`, `e`. Lean-first.
-/
module

public import Proof.bufio.Defs

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
def bufio.ownReaderBuf (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r q : List w8) (e : GoInterface) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
    ∃ (v : _root_.Perennial.bufio.Reader) (bs : List w8),
    b ↦ v ∗ v.buf' ↦* bs ∗
    ⌜v.rd' = GoInterface.ok ri ∧ 0 ≤ sint.Z v.r' ∧ sint.Z v.r' ≤ sint.Z v.w' ∧
      sint.nat v.w' ≤ bs.length ∧ 0 < bs.length ∧ bs.length ≤ 2 ^ 12 ∧
      subslice (sint.nat v.r') (sint.nat v.w') bs = q ∧ v.err' = e⌝ ∗
    S (r ++ q) ∗ io.errAt E (r ++ q) e)

/-- See the file header. -/
theorem bufio.ownReader_buf (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r : List w8) :
    bufio.ownReader b ri S E r ⊣⊢
      ∃ (q : List w8) (e : GoInterface), bufio.ownReaderBuf b ri S E r q e := by
  constructor
  · unfold bufio.ownReader bufio.ownReaderBuf
    iintro ⟨#Hpkg, %v, %bs, Hv, Hbuf, %Hwf, HS, #Herr⟩
    iexists subslice (sint.nat v.r') (sint.nat v.w') bs, v.err'
    iframe Hpkg
    iexists v, bs
    iframe Hv Hbuf HS Herr
    ipureintro
    exact ⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, Hwf.2.2.2.1, Hwf.2.2.2.2.1, Hwf.2.2.2.2.2, rfl, rfl⟩
  · unfold bufio.ownReader bufio.ownReaderBuf
    iintro ⟨%q, %e, #Hpkg, %v, %bs, Hv, Hbuf, %Hwf, HS, #Herr⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, hq, he⟩ := Hwf
    subst hq he
    iframe Hpkg
    iexists v, bs
    iframe Hv Hbuf HS Herr
    ipureintro
    exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The underlying stream's state, lent out of the reader. -/
theorem bufio.ownReaderBuf_open (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r q : List w8) (e : GoInterface) :
    bufio.ownReaderBuf b ri S E r q e ⊢
      S (r ++ q) ∗ (S (r ++ q) -∗ bufio.ownReaderBuf b ri S E r q e) := by
  unfold bufio.ownReaderBuf
  iintro ⟨#Hpkg, %v, %bs, Hv, Hbuf, %Hwf, HS, #Herr⟩
  iframe HS
  iintro HS
  iframe Hpkg
  iexists v, bs
  iframe Hv Hbuf HS Herr
  ipureintro; exact Hwf

end defs

end EtcdGrove
end Perennial
