/-
`cr.setInfiniteReadLimit()` (the model's `server.go`): the reader's `remain` set to `maxInt64`.
Proved in `Net/Proof/net/http/connReader__setInfiniteReadLimit.lean`.
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
abbrev connReader.setInfiniteReadLimit.spec : Prop :=
  ∀ (cr : Loc) (v : w64),
  {{ (structFieldRef net.http.connReader go!"remain" cr ↦ v : IProp GF) }}
    (App (Val (cr @!! go.GoType.PointerType net.http.connReader.ty @!! go!"setInfiniteReadLimit"))
      (Val #()))
  {{ RET #(); structFieldRef net.http.connReader go!"remain" cr ↦ W64 (2 ^ 63 - 1) }}

end spec

end net.http
end Perennial
