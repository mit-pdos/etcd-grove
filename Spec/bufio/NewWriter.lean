/-
`bufio.NewWriter(wr)` (Go 1.27.3 `bufio.go`: `NewWriterSize(wr, 4096)`) over a writer `wr` by the
`io.Writer` contract `io.writerOk wi J Q Ew` that is not already a `*bufio.Writer`: a fresh writer
that has sent `W` and buffers nothing (`bufio.ownBufWriter`). Proved in
`Proof/bufio/NewWriter.lean`. dsv-bufio, 2026-11-23 (#24).
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
abbrev bufio.NewWriter.spec : Prop :=
  ∀ (wi : GoInterfaceOk) (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF) (W : List w8),
  wi.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Writer.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ io.writerOk wi J Q Ew ∗ J W ∗ □ Q W }}
    (App (Val (@! _root_.Perennial.bufio.NewWriter)) (Val #(GoInterface.ok wi)))
  {{ (bw : Loc), RET #bw; bufio.ownBufWriter bw wi J Q Ew W [] interface.nil }}

end spec

end EtcdGrove
end Perennial
