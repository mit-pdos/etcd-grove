/-
`bufio.NewWriterSize(wr, size)` (Go 1.27.3 `bufio.go`), generic: for any `wr` not a `*bufio.Writer`,
a fresh writer's fields over `wr` (`bufio.writerRep`, `Proof/bufio/Own.lean`) with a buffer of
`bufio.writerSize size` bytes, nothing buffered, no error, for any error evidence `Ew`. Nothing is
asked of `wr`: `NewWriterSize` only stores it. `bufio.NewWriterSize.spec` (over the `io.Writer`
contract) is its instance (`Proof/bufio/NewWriterSize.lean`); net/http's `newBufioWriterSize` uses
it with `bufio.writerRep_raw` (a writer holding nothing, `bufio.rawWriter`), as the server writes
nothing before a hijack. Proved in `Proof/bufio/NewWriterSizeRep.lean`. 2026-11-23; Lean-first.
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
abbrev bufio.NewWriterSize.specRep : Prop :=
  ∀ (wi : GoInterfaceOk) (Ew : GoInterface → IProp GF) (size : w64),
  {{ ⌜wi.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Writer.ty⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio }}
    (App (App (Val (@! _root_.Perennial.bufio.NewWriterSize)) (Val #(GoInterface.ok wi)))
      (Val #size))
  {{ (bw : Loc), RET #bw; bufio.writerRep bw wi Ew (bufio.writerSize size) [] interface.nil }}

end spec

end EtcdGrove
end Perennial
