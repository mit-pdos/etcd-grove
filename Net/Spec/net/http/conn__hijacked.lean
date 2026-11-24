/-
`c.hijacked()` (the model's `server.go`): under `c.mu` (`connMuInv c γh`), the connection's
`hijackedv`, which the caller's half of `γh` fixes at `b`. Proved in
`Net/Proof/net/http/conn__hijacked.lean`.
-/
module

public import Net.Proof.net.http.ServerConn

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev conn.hijacked.spec : Prop :=
  ∀ (c : Loc) (γh : GName) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      sync.isMutex (structFieldRef net.http.conn go!"mu" c) (connMuInv c γh) ∗
      ghostVar γh (1 : Qp).half b }}
    (App (Val (c @!! go.GoType.PointerType net.http.conn.ty @!! go!"hijacked")) (Val #()))
  {{ RET #b; ghostVar γh (1 : Qp).half b }}

end spec

end net.http
end Perennial
