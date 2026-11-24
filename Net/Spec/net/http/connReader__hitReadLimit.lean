/-
`cr.hitReadLimit()` (the model's `server.go`): whether the reader's `remain` is at most 0; the
field is only read (any fraction). Proved in `Net/Proof/net/http/connReader__hitReadLimit.lean`.
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
abbrev connReader.hitReadLimit.spec : Prop :=
  ∀ (cr : Loc) (dq : DFrac) (v : w64),
  {{ (structFieldRef net.http.connReader go!"remain" cr ↦{dq} v : IProp GF) }}
    (App (Val (cr @!! go.GoType.PointerType net.http.connReader.ty @!! go!"hitReadLimit"))
      (Val #()))
  {{ RET #(decide (sint.Z v ≤ 0)); structFieldRef net.http.connReader go!"remain" cr ↦{dq} v }}

end spec

end net.http
end Perennial
