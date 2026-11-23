/-
`(*bufio.Reader).ReadByte()` (Go 1.27 `bufio.go`) over a stream reader that makes progress
(`io.readerStreamNE`, `Proof/io/ReaderStreamNE.lean`): the stream's next byte `c` (from the buffer,
or after a `fill`), the reader then at `r ++ [c]`; or, with nothing buffered, an error of the stream
at `r` (`io.errAt E r err`: its evidence, and a pointer type's value a location, what comparing
it with `io.EOF` needs; the pending one or a new read's), cleared, the reader still at `r`. Proved in
`Proof/bufio/Reader__ReadByte.lean`. net/http's `ReadResponse`, 2026-11-23 (the model's
`modelReadLine`); Lean-first.
-/
module

public import Proof.bufio.Buf
public import Proof.io.ReaderStreamNE

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
  ∀ (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r : List w8),
  ⊢ io.readerStreamNE ri S E -∗ (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) -∗
    {{ bufio.ownReader b ri S E r }}
      (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"ReadByte"))
        (Val #()))
    {{ (c : w8) (err : GoInterface), RET (PairV #c #err);
        (⌜err = GoInterface.nil⌝ ∗ bufio.ownReader b ri S E (r ++ [c])) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ io.errAt E r err ∗ bufio.ownReader b ri S E r) }}

end spec

end EtcdGrove
end Perennial
