/-
`getCodec()` (the encoding/json model's, `model.go`) after a codec of `fm`, `fu` is registered
(`codecSetWith`): the registered codec (mit-pdos/etcd-grove#24, J2).
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
abbrev getCodec.spec : Prop :=
  ∀ (fm fu : GoFunc),
  {{ codecSetWith (GF := GF) fm fu }}
    (App (Val (@! encoding.json.getCodec)) (Val #()))
  {{ (c : Loc), RET #c; codecFnsWith (GF := GF) fm fu c }}

end spec

end encoding.json
end Perennial
