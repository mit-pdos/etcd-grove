/-
`(*zap.Logger).Core`: the trust boundary.
Users: the gRPC log interceptor (`api/v3rpc/interceptor.go:94`, `lg.Core().Enabled(zap.DebugLevel)`).
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: new (re-review of A1, second tier: `logUnaryRequestStats` is specced and calls it).
Margin: the core's configuration is not modelled.
-/
module

public import SpecPlan.Spec.go_uber_org.zap.Api

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

/-- `l.Core()`: the logger's core (`coreOk`). -/
def Logger.Core.spec : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ isLogger l }}
    (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Core")) (Val #()))
  {{ (c : GoInterface), RET #c; coreOk c }}

end spec

end Zap
end EtcdGrove
end Perennial
