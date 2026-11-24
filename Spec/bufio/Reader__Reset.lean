/-
`(*bufio.Reader).Reset(r)` (Go 1.27.3 `bufio.go`) of a reader with a buffer (`bufio.rawReader`), to
a source `r` that is `nil` or not a `*bufio.Reader` (so not the reader itself): its buffer kept,
reading from `r` with nothing buffered and no pending error (`bufio.freshReader`). Proved in
`Proof/bufio/Reader__Reset.lean`. net/http's server (`newBufioReader`'s pooled reader), 2026-11-23;
Lean-first.
-/
module

public import Proof.bufio.RawReader

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
abbrev bufio.Reader.Reset.spec : Prop :=
  ∀ (b : Loc) (rd : GoInterface),
  {{ ⌜rd = interface.nil ∨ ∃ ri : GoInterfaceOk, rd = interface.ok ri ∧
        ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty⌝ ∗
      bufio.rawReader (GF := GF) b }}
    (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"Reset"))
      (Val #rd))
  {{ RET #(); bufio.freshReader b rd }}

end spec

end EtcdGrove
end Perennial
