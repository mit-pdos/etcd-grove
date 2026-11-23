/-
`s.getRequest()` (`server.go`): a request from the free list (zeroed) or a new one, owned.
Proved in `Net/Proof/net/rpc/Server__getRequest.lean`.
-/
module

public import Net.Proof.net.rpc.ServerDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Server.getRequest.spec : Prop :=
  ∀ (s : Loc) (γ : GName),
  {{ isServer (GF := GF) s γ }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"getRequest")) (Val #()))
  {{ (req : Loc), RET #req; req ↦ (_root_.Perennial.zero_val net.rpc.Request) }}

end spec

end net.rpc
end Perennial
