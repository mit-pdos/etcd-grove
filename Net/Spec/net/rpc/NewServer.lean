/-
`NewServer()` (`server.go`): a new server (`isServer`, `ServerDefs.lean`), no service
registered (its registry `γ`'s authority is the invariant's: `register` is what adds to it).
Proved in `Net/Proof/net/rpc/NewServer.lean`.
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
abbrev NewServer.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
    (App (Val (@! net.rpc.NewServer)) (Val #()))
  {{ (s : Loc), RET #s; ∃ γ : GName, isServer s γ }}

end spec

end net.rpc
end Perennial
