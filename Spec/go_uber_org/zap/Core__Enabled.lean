/-
`(zapcore.Core).Enabled`: the trust boundary.
Users: the gRPC log interceptor (`api/v3rpc/interceptor.go:94`).
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: new (re-review of A1, second tier: `logUnaryRequestStats` is specced and calls it).
Margin: which levels are enabled is not modelled.
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

/-- `core.Enabled(lvl)` of a logger's core: some boolean. -/
def Core.Enabled.spec : Prop :=
  ∀ (c : GoInterface) (lvl : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ coreOk c }}
    (App (Val (c @!! zap.zapcore.Core.ty @!! go!"Enabled")) (Val #lvl))
  {{ (b : Bool), RET #b; True }}

end spec

end Zap
end EtcdGrove
end Perennial
