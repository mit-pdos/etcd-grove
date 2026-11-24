/-
`s.freeRequest(req)` (`server.go`): `req` (owned) goes to the free list. Proved in
`Net/Proof/net/rpc/Server__freeRequest.lean`.
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
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Server.freeRequest.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (req : Loc) (v : net.rpc.Request),
  {{ isServer (GF := GF) s γ ∗ req ↦ v }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"freeRequest")) (Val #req))
  {{ RET #(); True }}

end spec

end net.rpc
end Perennial
