/-
`zap.Stringer`: the trust boundary.
Users: the server's and the client's code throughout (every logging call); `NewNop`: the examples
(`examples/etcd/*`, `zap.NewNop()` as the member's and the client's logger).
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: from `specs-ref/Spec/go_uber_org/zap/Stringer.lean`: the namespace `Zap`.
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

/-- `zap.Stringer(key, v)` returns a field (a plain value). -/
def Stringer.spec : Prop :=
  ∀ (k : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (App (Val (@! zap.Stringer)) (Val #k)) (Val #v))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end Zap
end EtcdGrove
end Perennial
