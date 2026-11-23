/-
**A `*bufio.Reader` is itself an `io.Reader` by Perennial's contract** (dsv-bufio, 2026-11-23,
mit-pdos/etcd-grove#24): `bufio.ownBufReader_readerOk` gives `io.readerOk` of the interface value
`⟨*bufio.Reader, br⟩`, with the stream state `bufio.ownBufReader br ri Pre S E` and the errors
`bufio.errE E`, from the generic `Read` spec (`bufio.Reader.Read.specOk`, a hypothesis). So
Perennial's `io.ReadFull`/`io.ReadAtLeast` (`io.wp_ReadFull`, `io.wp_ReadAtLeast`) read through a
buffered reader. Lean-first.
-/
module

public import Spec.bufio.Reader__ReadOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- The interface value of a `*bufio.Reader`. -/
def bufio.readerIface (br : Loc) : GoInterfaceOk :=
  ⟨go.GoType.PointerType _root_.Perennial.bufio.Reader.ty, #br⟩

/-- See the file header. Each read must meet `Pre` at any point of the underlying stream. -/
theorem bufio.ownBufReader_readerOk
    (wp_Read : bufio.Reader.Read.specOk (GF := GF) (hG := hG))
    (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) :
    ⊢ _root_.Perennial.io.readerOk (bufio.readerIface br) (fun _ m => ∀ r, 0 < m → Pre r m)
        (bufio.ownBufReader br ri Pre S E) (bufio.errE E) := by
  unfold _root_.Perennial.io.readerOk bufio.readerIface
  imodintro
  iintro %R %p %xs
  imodintro
  iintro %Φ ⟨%hpre, HS, Hp⟩ HΦ
  dsimp only
  iapply wp_Read br ri Pre S E R p xs hpre $$ [HS Hp] HΦ
  iframe HS Hp

end laws

end EtcdGrove
end Perennial
