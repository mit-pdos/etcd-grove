/-
`s.getResponse()` (`server.go`): a response from the free list (zeroed) or a new one, owned.
Proved in `Net/Proof/net/rpc/Server__getResponse.lean`.
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
abbrev Server.getResponse.spec : Prop :=
  ∀ (s : Loc) (γ : GName),
  {{ isServerAny (GF := GF) s γ }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"getResponse")) (Val #()))
  {{ (resp : Loc), RET #resp; resp ↦ (_root_.Perennial.zero_val net.rpc.Response) }}

end spec

end net.rpc
end Perennial
