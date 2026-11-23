/-
`s.freeResponse(resp)` (`server.go`): `resp` (owned) goes to the free list. Proved in
`Net/Proof/net/rpc/Server__freeResponse.lean`.
-/
module

public import Net.Proof.net.rpc.ServerDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Server.freeResponse.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (resp : Loc) (v : net.rpc.Response),
  {{ isServer (GF := GF) s γ ∗ resp ↦ v }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"freeResponse")) (Val #resp))
  {{ RET #(); True }}

end spec

end net.rpc
end Perennial
