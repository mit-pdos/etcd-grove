/-
`(*zap.Logger).Panic`: the trust boundary.
Users: the server's and the client's code throughout (every logging call); `NewNop`: the examples
(`examples/etcd/*`, `zap.NewNop()` as the member's and the client's logger).
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: from `specs-ref/Spec/go_uber_org/zap/Logger__Panic.lean`: the logger's premise is `isLogger l` (was
`l ≠ null`; the old `zapLoggerOk` only in `NewNop`), the namespace `Zap`.
Margin: logging's output is not modelled.
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

/-- `l.Panic(msg, fields...)` logs, then panics with the message (zapcore's `CheckedEntry.Write`:
`panic(ce.Message)`), whatever the logger's core: `Panic` entries are always written. -/
def Logger.Panic.spec : Prop :=
  ∀ (l : Loc) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ isLogger l }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Panic")) (Val #msg)) (Val #fields))
  {{ (r : val), RET r; ⌜r = PanicV #msg⌝ }}

end spec

end Zap
end EtcdGrove
end Perennial
