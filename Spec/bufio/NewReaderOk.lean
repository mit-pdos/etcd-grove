/-
`bufio.NewReader(rd)` (Go 1.27.3 `bufio.go`: `NewReaderSize(rd, 4096)`) over a reader `rd` by
Perennial's `io.Reader` contract (`io.readerOk ri Pre S E`): a fresh reader with a 4096-byte buffer,
nothing returned or buffered (`bufio.ownBufReader`); every read of at most 4096 bytes, from any
state of the stream, must meet `Pre` (`bufio.preUpTo`). Scope: `rd` is not a `*bufio.Reader`
(`NewReaderSize`'s spec says why). The WAL's `bufio.NewReader.spec` (`Spec/bufio/NewReader.lean`,
over `bufio.ownReader`) is proved from the same `NewReaderSize` proof. Proved in
`Proof/bufio/NewReaderOk.lean`. dsv-bufio, 2026-11-23 (#24); revised after the review (R1, R3).
-/
module

public import Proof.bufio.Own

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
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
abbrev bufio.NewReader.specOk : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8),
  {{ ⌜ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ _root_.Perennial.io.readerOk ri Pre S E ∗
      bufio.preUpTo S Pre 4096 ∗ S R }}
    (App (Val (@! _root_.Perennial.bufio.NewReader)) (Val #(GoInterface.ok ri)))
  {{ (br : Loc), RET #br; bufio.ownBufReader br ri Pre S E R }}

end spec

end EtcdGrove
end Perennial
