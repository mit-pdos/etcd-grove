/-
`newServerCodec(conn)` (`codec.go`): a new server codec over `conn`, no write or read error yet, not closed. Proved
in `Net/Proof/net/rpc/newServerCodec.lean`.
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
abbrev newServerCodec.spec : Prop :=
  ∀ (conn : GoInterface),
  {{ (True : IProp GF) }}
    (App (Val (@! net.rpc.newServerCodec)) (Val #conn))
  {{ (cc : Loc), RET #cc; structFieldRef net.rpc.serverCodec go!"rwc" cc ↦ conn ∗
      structFieldRef net.rpc.serverCodec go!"werr" cc ↦ interface.nil ∗
      structFieldRef net.rpc.serverCodec go!"rerr" cc ↦ interface.nil ∗
      structFieldRef net.rpc.serverCodec go!"closed" cc ↦ false }}

end spec

end net.rpc
end Perennial
