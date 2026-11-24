/-
`valid(c, data)` (the encoding/json model's, `model.go`) on a `*Codec` `c` whose `Scan` is
`jsoncodec.Scan`, computing `F`: whether `data` is one JSON value with whitespace around it
(`jsonValid F bs`) (mit-pdos/etcd-grove#24, J2).
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
abbrev valid.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (c : Loc)
    (data : GoSlice) (dq : DFrac) (bs : List w8),
  {{ structFieldRef encoding.json.Codec go!"Scan" c ↦□ models_lab.jsoncodec.scanFn ∗
      models_lab.jsoncodec.scanOk (GF := GF) F models_lab.jsoncodec.scanFn ∗ data ↦*{dq} bs }}
    (App (App (Val (@! encoding.json.valid)) (Val #c)) (Val #data))
  {{ RET #(decide (models_lab.jsoncodec.jsonValid F bs)); data ↦*{dq} bs }}

end spec

end encoding.json
end Perennial
