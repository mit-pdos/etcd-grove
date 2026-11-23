/-
`bufio.NewWriterSize(wr, size)` (Go 1.27.3 `bufio.go`) over a writer `wr` by the `io.Writer`
contract `io.writerOk wi J Q Ew` (`Proof/io/WriterOk.lean`) that is not already a
`*bufio.Writer` (which it would return as is): a fresh writer (a buffer of `size` bytes, 4096 if
`size ≤ 0`) that has sent `W` (`J W`, `□ Q W`) and buffers nothing (`bufio.ownBufWriter`,
`Proof/bufio/Own.lean`). Proved in `Proof/bufio/NewWriterSize.lean`. dsv-bufio, 2026-11-23 (#24).
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
  wi.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Writer.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ io.writerOk wi J Q Ew ∗ J W ∗ □ Q W }}
    (App (App (Val (@! _root_.Perennial.bufio.NewWriterSize)) (Val #(GoInterface.ok wi)))
      (Val #size))
  {{ (bw : Loc), RET #bw; bufio.ownBufWriter bw wi J Q Ew W [] interface.nil }}

end spec

end EtcdGrove
end Perennial
