/-
`bufio.NewReaderSize(rd, size)` (Go 1.27.3 `bufio.go`) over a reader `rd` by Perennial's
`io.Reader` contract (`io.readerOk ri Pre S E`): a fresh reader with a buffer of `max(size, 16)`
bytes, nothing returned or buffered (`bufio.ownBufReader`, `Proof/bufio/Own.lean`); every read of
at most that many bytes, from any state of the stream, must meet `Pre` (`bufio.preUpTo`).

Scope: `rd` is not a `*bufio.Reader` (`⌜ri.ty ≠ *bufio.Reader⌝`). Go returns such an `rd` itself
when its buffer has at least `size` bytes, and wraps it otherwise (`bufio.go:52-54`); neither case
is specified.

`bufio.NewReaderSize.specE` is the same for `bufio.ownBufReaderE` with any evidence `Eb` of the
pending errors and any condition `szOk` the buffer's size meets: the one proof
(`Proof/bufio/NewReaderSize.lean`), of which `spec` is the instance at `bufio.errE E`, and the WAL's
`bufio.NewReader.spec` another. dsv-bufio, 2026-11-23 (#24); revised after the review (R1, R3, R4).
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
abbrev bufio.NewReaderSize.specE : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E Eb : List w8 → GoInterface → IProp GF) (szOk : Nat → Prop) (R : List w8) (size : w64),
  {{ ⌜ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty⌝ ∗
      ⌜szOk (max (sint.Z size) 16).toNat⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ _root_.Perennial.io.readerOk ri Pre S E ∗
      bufio.preUpTo S Pre (max (sint.Z size) 16).toNat ∗ S R }}
    (App (App (Val (@! _root_.Perennial.bufio.NewReaderSize)) (Val #(GoInterface.ok ri)))
      (Val #size))
  {{ (br : Loc), RET #br; bufio.ownBufReaderE br ri Pre S E Eb szOk R }}

/-- See the file header. -/
abbrev bufio.NewReaderSize.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) (size : w64),
  {{ ⌜ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ _root_.Perennial.io.readerOk ri Pre S E ∗
      bufio.preUpTo S Pre (max (sint.Z size) 16).toNat ∗ S R }}
    (App (App (Val (@! _root_.Perennial.bufio.NewReaderSize)) (Val #(GoInterface.ok ri)))
      (Val #size))
  {{ (br : Loc), RET #br; bufio.ownBufReader br ri Pre S E R }}

end spec

end EtcdGrove
end Perennial
