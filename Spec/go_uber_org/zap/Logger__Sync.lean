/-
`(*zap.Logger).Sync`: the trust boundary.
Users: the server's shutdown, `etcdmain`.
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: new (verify round, A1-completeness S1: a specced caller uses it and no spec existed).
Margin: the sinks' flush is not modelled.
-/
module

public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Zap

open Iris Iris.BI go_uber_org

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `l.Sync()`: `nil` or an error (the sinks' `Sync`). -/
def Logger.Sync.spec : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ isLogger l }}
    (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

end spec

end Zap
end EtcdGrove
end Perennial
