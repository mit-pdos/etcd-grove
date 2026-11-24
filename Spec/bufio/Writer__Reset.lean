/-
`(*bufio.Writer).Reset(w)` (Go 1.27.3 `bufio.go`) of a writer holding nothing (`bufio.rawWriter`), to a
destination `w` that is `nil` or not a `*bufio.Writer` (so not the writer itself): its buffer kept, its
error cleared, its destination `w`. Proved in `Proof/bufio/Writer__Reset.lean`. net/http's server,
2026-11-23; Lean-first.
-/
module

public import Proof.bufio.RawWriter

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
abbrev bufio.Writer.Reset.spec : Prop :=
  ∀ (bw : Loc) (sz : Nat) (w : GoInterface),
  {{ ⌜w = interface.nil ∨ ∃ wi : GoInterfaceOk, w = interface.ok wi ∧
        wi.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Writer.ty⌝ ∗ bufio.rawWriter (GF := GF) bw sz }}
    (App (Val (bw @!! go.GoType.PointerType _root_.Perennial.bufio.Writer.ty @!! go!"Reset"))
      (Val #w))
  {{ RET #(); bufio.rawWriter bw sz }}

end spec

end EtcdGrove
end Perennial
