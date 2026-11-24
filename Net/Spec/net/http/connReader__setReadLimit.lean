/-
`cr.setReadLimit(remain)` (the model's `server.go`): the reader's `remain` set. Proved in
`Net/Proof/net/http/connReader__setReadLimit.lean`.
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
abbrev connReader.setReadLimit.spec : Prop :=
  ∀ (cr : Loc) (v remain : w64),
  {{ (structFieldRef net.http.connReader go!"remain" cr ↦ v : IProp GF) }}
    (App (Val (cr @!! go.GoType.PointerType net.http.connReader.ty @!! go!"setReadLimit"))
      (Val #remain))
  {{ RET #(); structFieldRef net.http.connReader go!"remain" cr ↦ remain }}

end spec

end net.http
end Perennial
