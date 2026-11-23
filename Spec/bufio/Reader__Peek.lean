/-
`(*bufio.Reader).Peek(1)` (Go 1.27 `bufio.go`) over a stream reader that makes progress
(`io.readerStreamNE`, `Proof/io/ReaderStreamNE.lean`): the slice `s` of the buffer holding the
stream's next byte `c`, lent (`s ↦* [c]`, given back for the reader, which then holds `c` and
maybe more, `c :: q`, nothing delivered); or, with nothing buffered, an error of the stream at `r`
(`E r err`), cleared, the reader still at `r`. Only `n = 1`, what net/http's model peeks
(`modelReadMIMEHeader`): a larger `n` may exceed the buffer, whose size `ownReader` does not fix,
and then `Peek` returns `bufio.ErrBufferFull`, a package variable whose value bufio's package fact
does not hold. Proved in `Proof/bufio/Reader__Peek.lean`. net/http's `ReadResponse`, 2026-11-23;
Lean-first.
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
abbrev bufio.Reader.Peek.spec : Prop :=
  ∀ (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r : List w8),
  ⊢ io.readerStreamNE ri S E -∗ (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) -∗
    {{ bufio.ownReader b ri S E r }}
      (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"Peek"))
        (Val #(W64 1)))
    {{ (s : GoSlice) (err : GoInterface), RET (PairV #s #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (c : w8) (q : List w8) (e : GoInterface), s ↦* [c] ∗
          (s ↦* [c] -∗ bufio.ownReaderBuf b ri S E r (c :: q) e)) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ □ E r err ∗ bufio.ownReader b ri S E r) }}

end spec

end EtcdGrove
end Perennial
