/-
`bufio.NewWriterSize(wr, size)` (Go 1.27.3 `bufio.go`) over a writer `wr` by the `io.Writer`
contract `io.streamWriterOk wi J Q Ew` (`Proof/io/StreamWriterOk.lean`): a fresh writer with a buffer of
`bufio.writerSize size` bytes (`size`, 4096 if `size ≤ 0`; the size index of `bufio.ownBufWriter`,
`Proof/bufio/Own.lean`) that has sent `W` (`J W`, `□ Q W`) and buffers nothing.

Scope: `wr` is not a `*bufio.Writer` (`⌜wi.ty ≠ *bufio.Writer⌝`). Go returns such a `wr` itself
when its buffer has at least `size` bytes, and wraps it otherwise (`bufio.go:591-593`); neither
case is specified. Proved in `Proof/bufio/NewWriterSize.lean`. dsv-bufio, 2026-11-23 (#24);
revised after the review (W2, W5).
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
abbrev bufio.NewWriterSize.spec : Prop :=
  ∀ (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF) (W : List w8)
    (size : w64),
  {{ ⌜wi.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Writer.ty⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ io.streamWriterOk wi J Q Ew ∗ J W ∗ □ Q W }}
    (App (App (Val (@! _root_.Perennial.bufio.NewWriterSize)) (Val #(GoInterface.ok wi)))
      (Val #size))
  {{ (bw : Loc), RET #bw; bufio.ownBufWriter bw wi J Q Ew (bufio.writerSize size) W [] interface.nil }}

end spec

end EtcdGrove
end Perennial
