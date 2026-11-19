/-
`jsoncodec.IsSpace(c)`: whether `c` is JSON whitespace (`spaceB c`). A functional spec, so it
implies safety (no panic). Proved in `Net/Proof/netmodels_lab/jsoncodec/IsSpace.lean`; ported from
dsverify-lab's `wp_IsSpace` (`Harness/Proof/jsoncodec/Helpers.lean`, `348a866`).
-/
module

public import Net.Proof.netmodels_lab.jsoncodec.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace netmodels_lab.jsoncodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : netmodels_lab.jsoncodec.Assumptions]

/-- See the file header. -/
abbrev IsSpace.spec : Prop :=
  ∀ c : w8,
  {{ (True : IProp GF) }}
    (App (Val (@! netmodels_lab.jsoncodec.IsSpace)) (Val #c))
  {{ RET #(spaceB c); True }}

end spec

end netmodels_lab.jsoncodec
end Perennial
