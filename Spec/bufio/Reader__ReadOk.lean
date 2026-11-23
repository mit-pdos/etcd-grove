/-
`(*bufio.Reader).Read(p)` (Go 1.27.3 `bufio.go`) over a reader by Perennial's `io.Reader`
contract (`bufio.ownBufReader`): the next bytes `ys` of the stream (at most `len(p)`) in the front
of `p`, the rest of `p` unchanged, and `nil` or an error with its evidence at `R ++ ys`
(`bufio.errE E`); bytes and an error may come together (as the underlying reader's). A read of
`p` directly from the underlying reader (`len(p)` at least the buffer's size, nothing buffered:
the stream is at `R`) must meet `Pre` (`⌜0 < len(p) → Pre R len(p)⌝`); the reads into the buffer
meet it by `bufio.preUpTo`, held by the reader. The post is `io.readerOk`'s, for the reader `br`
with state `bufio.ownBufReader br ri Pre S E` (`Proof/bufio/ReaderLaws.lean`).

`bufio.Reader.Read.specE` is the same for `bufio.ownBufReaderE`, with any evidence `Eb` of the
reader's errors that the underlying reader's give (`□ (E -∗ Eb)`): the one proof
(`Proof/bufio/Reader__ReadOk.lean`), of which `specOk` is the instance at `bufio.errE E`, and the
WAL's `bufio.Reader.Read.spec` (`Spec/bufio/Reader__Read.lean`) another. dsv-bufio, 2026-11-23
(#24); revised after the review (R1, R3).
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
abbrev bufio.Reader.Read.specE : Prop :=
  ∀ (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E Eb : List w8 → GoInterface → IProp GF) (szOk : Nat → Prop) (R : List w8) (p : GoSlice)
    (xs : List w8),
  {{ ⌜0 < xs.length → Pre R xs.length⌝ ∗ (□ ∀ r e, E r e -∗ Eb r e) ∗
      bufio.ownBufReaderE br ri Pre S E Eb szOk R ∗ p ↦* xs }}
    (App (Val (br @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"Read")) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ bufio.ownBufReaderE br ri Pre S E Eb szOk (R ++ ys) ∗
        _root_.Perennial.io.errAt Eb (R ++ ys) err ∗
        ⌜_root_.Perennial.io.ptrTyped err⌝ }}

/-- See the file header. -/
abbrev bufio.Reader.Read.specOk : Prop :=
  ∀ (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) (p : GoSlice) (xs : List w8),
  {{ ⌜0 < xs.length → Pre R xs.length⌝ ∗ bufio.ownBufReader br ri Pre S E R ∗ p ↦* xs }}
    (App (Val (br @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"Read")) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ bufio.ownBufReader br ri Pre S E (R ++ ys) ∗
        _root_.Perennial.io.errAt (bufio.errE E) (R ++ ys) err ∗
        ⌜_root_.Perennial.io.ptrTyped err⌝ }}

end spec

end EtcdGrove
end Perennial
