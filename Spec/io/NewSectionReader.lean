/-
`io.NewSectionReader(r, off, n)` (names only in Perennial; S4, 2026-11-18): the trust boundary (an
axiom in `Proof/io/NewSectionReader.lean`), stated over `io.secReader` (`Proof/io/SectionReader.lean`),
which only `io.CopyN`'s spec takes (`Spec/io/CopyN.lean`). bbolt's `Tx.WriteTo` (tx.go) makes one of
the database's `*os.File` (converted to an `io.ReaderAt`) to copy its data pages. Lean-first.
-/
module

public import Proof.io.SectionReader

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

/-- `NewSectionReader(r, off, n)`, at `0 ≤ off`, `0 ≤ n` and `off + n < 2^63`: a fresh
`*SectionReader` `sr` of `r` from `off`, `n` bytes long (`io.secReader sr r off n`). -/
abbrev io.NewSectionReader.spec : Prop :=
  ∀ (r : GoInterfaceOk) (off n : w64),
  0 ≤ sint.Z off → 0 ≤ sint.Z n → off.toNat + n.toNat < 2 ^ 63 →
  {{ (True : IProp GF) }}
    (App (App (App (Val (@! _root_.Perennial.io.NewSectionReader)) (Val #(GoInterface.ok r)))
      (Val #off)) (Val #n))
  {{ (sr : Loc), RET #sr; io.secReader sr r off n }}

end spec

end EtcdGrove
end Perennial
