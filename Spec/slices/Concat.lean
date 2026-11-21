/-
`slices.Concat(ss...)` of string slices (Go's `slices`, names only in Perennial): **the trust
boundary**. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.GeneratedProof.slices

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace slices

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev Concat.spec : Prop :=
  ∀ (ss : GoSlice) (dq : DFrac) (sls : List GoSlice) (xss : List (List GoString)) (dq' : DFrac),
  sls.length = xss.length →
  {{ ss ↦*{dq} sls ∗ [∗list] p ∈ sls.zip xss, (p.1 ↦*{dq'} p.2 : IProp GF) }}
    (App (Val #(functions _root_.Perennial.slices.Concat
      [go.GoType.SliceType go.string, go.string])) (Val #ss))
  {{ (s' : GoSlice), RET #s'; ss ↦*{dq} sls ∗ ([∗list] p ∈ sls.zip xss, p.1 ↦*{dq'} p.2) ∗
      s' ↦* xss.flatten ∗ ownSliceCap GoString s' (DFrac.own 1) }}

end spec

end slices
end EtcdGrove
end Perennial
