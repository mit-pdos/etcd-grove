/-
`(*bufio.Reader).ReadByte()` (Go 1.27.3 `bufio.go`) over a reader by Perennial's `io.Reader`
contract (`bufio.ownBufReader`): the next byte `c` of the stream (`R ++ [c]` returned) and `nil`,
or a non-`nil` error with its evidence at `R` (`bufio.errE E`: the underlying reader's, or
`io.ErrNoProgress` after 100 empty reads) and nothing returned. Proved in
`Proof/bufio/Reader__ReadByte.lean`. dsv-bufio, 2026-11-23 (#24).
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
abbrev bufio.Reader.ReadByte.spec : Prop :=
  ∀ (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8),
  {{ bufio.ownBufReader br ri Pre S E R }}
    (App (Val (br @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"ReadByte")) (Val #()))
  {{ (c : w8) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ bufio.ownBufReader br ri Pre S E (R ++ [c])) ∨
      (⌜err ≠ interface.nil⌝ ∗ □ bufio.errE E R err ∗ ⌜_root_.Perennial.io.ptrTyped err⌝ ∗
        bufio.ownBufReader br ri Pre S E R) }}

end spec

end EtcdGrove
end Perennial
