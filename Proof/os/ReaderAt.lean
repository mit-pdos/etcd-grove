/-
**An open `*os.File` as an `io.ReaderAt`** (S4, 2026-11-18): the reader's contract
(`io.readerAtOk`, `Proof/io/SectionReader.lean`) of a readable `*os.File`, from its racing read
(`os.File.ReadAt.specRacyLt`, the hypothesis: this module imports no proof), over the file, its
descriptor and the client's `Q` behind the accessor of the bytes `rs` (`os.heldAcc`): each byte the
read returns is the byte `rs` says, where they say one (`io.CopyN` of a section of the file:
bbolt's `Tx.WriteTo`). Lean-first.
-/
module

public import Spec.os.File__ReadAt
public import Proof.io.SectionReader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open Fs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A readable `*os.File` is an `io.ReaderAt`** of the bytes the ranges `rs` say (see the file
header): with the file (`os.ownFile`), its descriptor (`osFd`) and `Q` as the reader's resource,
`Q` behind the accessor `os.heldAcc d.ino rs Q E`. -/
theorem os.File.readerAtOk (hRead : os.File.ReadAt.specRacyLt (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (dq : DFrac) (d : OsFd)
    (rs : List (Nat × DFrac × List ByteG)) (Q : IProp GF) (E : CoPset) (eof : GoInterface)
    (hrd : d.readable = true) (hE : ↑osN ⊆ E) :
    ⊢ osInv (GF := GF) -∗ globalAddr io.EOF ↦□ eof -∗ os.heldAcc d.ino rs Q E -∗
      io.readerAtOk ⟨go.GoType.PointerType os.File.ty, #f⟩
        iprop(os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗ Q)
        (fun i x => ∀ b, os.heldByte rs i b → x = b) := by
  iintro #Hinv #Heof #Hacc
  unfold io.readerAtOk
  imodintro
  iintro %b %vs %o %Φ
  imodintro
  iintro ⟨%ho, ⟨Hfo, Hfd, HQ⟩, Hb⟩ HΦ
  obtain ⟨ho0, hlen, hend⟩ := ho
  iapply hRead f fd name dqf b vs o dq d rs Q E eof hrd ho0 (by omega) hend hE
    $$ [Hfo Hb Hfd HQ]
  · iframe; iframe #
  inext
  iintro %n %err ⟨Hfo, Hfd, HQ, %vs', Hb, %h, -⟩
  obtain ⟨h1, h2, h3⟩ := h
  iapply HΦ
  iframe
  ipureintro
  refine ⟨h1, h2, fun i x hx hi bt hh => ?_⟩
  have := h3 (o.toNat + i) bt hh (by omega) (by omega)
  rw [show o.toNat + i - o.toNat = i by omega, hx] at this
  exact Option.some.inj this

end lemmas

end EtcdGrove
end Perennial
