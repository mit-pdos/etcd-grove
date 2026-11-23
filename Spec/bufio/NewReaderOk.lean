/-
`bufio.NewReader(rd)` (Go 1.27.3 `bufio.go`: `NewReaderSize(rd, 4096)`) over a reader `rd` by
Perennial's `io.Reader` contract (`io.readerOk ri Pre S E`): a fresh reader with a 4096-byte buffer,
nothing returned or buffered (`bufio.ownBufReader`); every read of at most 4096 bytes, from any
state of the stream, must meet `Pre` (`bufio.preUpTo`). Scope: `rd` is not a `*bufio.Reader`
(`NewReaderSize`'s spec says why).

`bufio.NewReader.specE` is the same for `bufio.ownBufReaderE` with any evidence `Eb` of the pending
errors and any condition `szOk` the buffer's size (4096) meets, as `bufio.NewReaderSize.specE`: the
one proof of `NewReader`'s body (`bufio.NewReader.wp_proofE`, `Proof/bufio/NewReaderOk.lean`), of
which `specOk` is the instance at `bufio.errE E` and the WAL's `bufio.NewReader.spec`
(`Spec/bufio/NewReader.lean`, over `bufio.ownReader`) another. dsv-bufio, 2026-11-23 (#24); revised
after the review (R1, R3; round 2, N4).
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
abbrev bufio.NewReader.specE : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E Eb : List w8 → GoInterface → IProp GF) (szOk : Nat → Prop) (R : List w8),
  {{ ⌜ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty⌝ ∗ ⌜szOk 4096⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ _root_.Perennial.io.readerOk ri Pre S E ∗
      bufio.preUpTo S Pre 4096 ∗ S R }}
    (App (Val (@! _root_.Perennial.bufio.NewReader)) (Val #(GoInterface.ok ri)))
  {{ (br : Loc), RET #br; bufio.ownBufReaderE br ri Pre S E Eb szOk R }}

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
