/-
`isSpace(c)` (the encoding/json model's, `model.go`): JSON whitespace (`isSpaceB`)
(mit-pdos/etcd-grove#24, J2).
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
abbrev isSpace.spec : Prop :=
  ∀ c : w8,
  {{ (True : IProp GF) }}
    (App (Val (@! encoding.json.isSpace)) (Val #c))
  {{ RET #(isSpaceB c); True }}

end spec

end encoding.json
end Perennial
