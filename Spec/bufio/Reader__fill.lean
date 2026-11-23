/-
`(*bufio.Reader).fill()` (Go 1.27 `bufio.go`) on an empty buffer with no pending error, over a
stream reader that makes progress (`io.readerStreamNE`, `Proof/io/ReaderStreamNE.lean`): one `Read`
of `ri` into the whole buffer, which then holds the bytes `ys` it delivered and its error `e`; one of
them is there (`ys ≠ []` or `e ≠ nil`), so the loop's `io.ErrNoProgress` is never reached. As
`ReadByte` and `Peek(1)` call it (both only on an empty buffer). Proved in
`Proof/bufio/Reader__fill.lean`. net/http's `ReadResponse`, 2026-11-23; Lean-first.
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
abbrev bufio.Reader.fill.spec : Prop :=
  ∀ (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r : List w8),
  ⊢ io.readerStreamNE ri S E -∗ (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) -∗
    {{ bufio.ownReaderBuf b ri S E r [] GoInterface.nil }}
      (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"fill"))
        (Val #()))
    {{ RET #(); ∃ (ys : List w8) (e : GoInterface), ⌜ys ≠ [] ∨ e ≠ GoInterface.nil⌝ ∗
        bufio.ownReaderBuf b ri S E r ys e }}

end spec

end EtcdGrove
end Perennial
