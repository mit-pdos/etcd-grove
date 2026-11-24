/-
`skipSpace(b)` (the encoding/json model's, `model.go`): the number of JSON whitespace bytes at
the start of `b` (`leadSpace`) (mit-pdos/etcd-grove#24, J2).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.encoding.json.Registry

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- See the file header. -/
abbrev skipSpace.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ (b ↦*{dq} bs : IProp GF) }}
    (App (Val (@! encoding.json.skipSpace)) (Val #b))
  {{ RET #(W64 (leadSpace bs)); b ↦*{dq} bs }}

end spec

end encoding.json
end Perennial
