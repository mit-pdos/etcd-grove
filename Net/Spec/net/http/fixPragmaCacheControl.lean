/-
`fixPragmaCacheControl(header)` on an empty header (no `Pragma`): nothing changed. Proved in
`Net/Proof/net/http/fixPragmaCacheControl.lean`.
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
abbrev fixPragmaCacheControl.spec : Prop :=
  ∀ (h : Loc),
  {{ (h ↦$ (∅ : GMap GoString GoSlice) : IProp GF) }}
    (App (Val (@! net.http.fixPragmaCacheControl)) (Val #h))
  {{ RET #(); h ↦$ (∅ : GMap GoString GoSlice) }}

end spec

end net.http
end Perennial
