/-
`(*zap.Logger).Fatal`: the trust boundary.
Users: the server's and the client's code throughout (every logging call); `NewNop`: the examples
(`examples/etcd/*`, `zap.NewNop()` as the member's and the client's logger).
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: from `specs-ref/Spec/go_uber_org/zap/Logger__Fatal.lean`: the logger's premise is `isLogger l` (was
`l ≠ null`; the old `zapLoggerOk` only in `NewNop`), the namespace `Zap`.
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

/-- `l.Fatal(msg, fields...)` logs, then exits the process (`os.Exit(1)`): it never returns (as
Perennial models an exit, the call diverges: any postcondition). -/
def Logger.Fatal.spec : Prop :=
  ∀ (l : Loc) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ isLogger l }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Fatal")) (Val #msg)) (Val #fields))
  {{ (r : val), RET r; False }}

end spec

end Zap
end EtcdGrove
end Perennial
