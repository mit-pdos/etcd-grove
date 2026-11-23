/-
`newClientCodec(conn)` (`codec.go`): a new client codec over `conn`, no write error yet. Proved
in `Net/Proof/net/rpc/newClientCodec.lean`.
-/
module

public import Net.GeneratedProof.net.rpc

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

/-- See the file header. -/
abbrev newClientCodec.spec : Prop :=
  ∀ (conn : GoInterface),
  {{ (True : IProp GF) }}
    (App (Val (@! net.rpc.newClientCodec)) (Val #conn))
  {{ (cc : Loc), RET #cc; structFieldRef net.rpc.clientCodec go!"rwc" cc ↦ conn ∗
      structFieldRef net.rpc.clientCodec go!"werr" cc ↦ interface.nil }}

end spec

end net.rpc
end Perennial
