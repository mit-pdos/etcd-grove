/-
`zap.Float64`: the trust boundary.
Users: `Client.roundRobinQuorumBackoff` (`client/v3/client.go:497`), the server (`server.go:1623`).
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: new (verify round, A1-completeness S1: a specced caller uses it and no spec existed).
Margin: logging's output is not modelled.
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

/-- `zap.Float64(key, v)` returns a field (a plain value; `v` a `float64`'s bits). -/
def Float64.spec : Prop :=
  ∀ (k : GoString) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (App (Val (@! zap.Float64)) (Val #k)) (Val #v))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end Zap
end EtcdGrove
end Perennial
