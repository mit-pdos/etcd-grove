/-
`concurrency.Session.Ctx()` (`client/v3/concurrency/session.go`). Lean-first (no Rocq counterpart); see
`InvSession.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSession

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `s.Ctx()`: the session's context (canceled once the session ends). -/
abbrev Session.Ctx.spec : Prop :=
  ∀ (s : Loc) (γ : SessionNames) (client : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isSession s γ client id }}
    (App (Val (s @!! go.GoType.PointerType Session.ty @!! go!"Ctx")) (Val #()))
  {{ (c : GoInterfaceOk), RET #(GoInterface.ok c); ∃ cs, context.isContext c cs }}

end spec

end concurrency
end EtcdGrove
end Perennial
