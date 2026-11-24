/-
`shouldClose(major, minor, header, removeCloseHeader)`, `header` a header map `ms` whose `"Connection"`
slice's values are owned (`hdrVals`, `Net/Proof/net/http/Defs.lean`): some answer; the header unchanged,
or (`removeCloseHeader`) without its `"Connection"` entry. Proved in `Net/Proof/net/http/shouldClose.lean`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev shouldClose.spec : Prop :=
  ∀ (major minor : w64) (h : Loc) (ms : GMap GoString GoSlice) (rm : Bool),
  {{ (h ↦$ ms ∗ hdrVals ms go!"Connection" : IProp GF) }}
    (App (App (App (App (Val (@! net.http.shouldClose)) (Val #major)) (Val #minor)) (Val #h)) (Val #rm))
  {{ (b : Bool), RET #b; ∃ ms' : GMap GoString GoSlice, h ↦$ ms' ∗ hdrVals ms go!"Connection" ∗
      ⌜ms' = ms ∨ (rm = true ∧ ms' = GMap.delete go!"Connection" ms)⌝ }}

end spec

end net.http
end Perennial
