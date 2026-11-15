/-
`zap.Time`: the trust boundary.
Users: the gRPC interceptors' request stats (`api/v3rpc/interceptor.go:188,204`, `logUnaryRequestStats`), the server (`server.go:917`).
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: new (verify round, A1-completeness S1: a specced caller uses it and no spec existed).
Margin: logging's output is not modelled.
-/
module

public import SpecPlan.Spec.go_uber_org.zap.Api
public import Perennial.Proof.time

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

/-- `zap.Time(key, t)` returns a field (a plain value). -/
def Time.spec : Prop :=
  ∀ (k : GoString) (t : time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (App (Val (@! zap.Time)) (Val #k)) (Val #t))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end Zap
end EtcdGrove
end Perennial
