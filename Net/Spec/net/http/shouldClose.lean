/-
`shouldClose(major, minor, header, removeCloseHeader)` on an empty header: some answer, the header
still empty. Proved in `Net/Proof/net/http/shouldClose.lean`.
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
  ∀ (major minor : w64) (h : Loc) (rm : Bool),
  {{ (h ↦$ (∅ : GMap GoString GoSlice) : IProp GF) }}
    (App (App (App (App (Val (@! net.http.shouldClose)) (Val #major)) (Val #minor)) (Val #h)) (Val #rm))
  {{ (b : Bool), RET #b; h ↦$ (∅ : GMap GoString GoSlice) }}

end spec

end net.http
end Perennial
