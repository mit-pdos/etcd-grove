/-
`(*zap.Logger).Check`: the trust boundary.
Users: the server's and the client's code throughout (every logging call); `NewNop`: the examples
(`examples/etcd/*`, `zap.NewNop()` as the member's and the client's logger).
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: from `specs-ref/Spec/go_uber_org/zap/Logger__Check.lean`: the logger's premise is `isLogger l` (was
`l ≠ null`; the old `zapLoggerOk` only in `NewNop`), the namespace `Zap`.
Margin: logging's output is not modelled.
The level is a `zapcore.Level` (`int8`) below `DPanicLevel` (`DebugLevel` `-1` through `ErrorLevel`
`2`): an entry at `DPanicLevel` (under `Development()`) or `PanicLevel` panics in its `Write`. Its
one caller (`auth/store.go`) checks `DebugLevel`.
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

/-- `l.Check(lvl, msg)` at a level below `DPanicLevel` returns `nil` (level not enabled) or an
entry to write once (`entryOk`). -/
def Logger.Check.spec : Prop :=
  ∀ (l : Loc) (lvl : w8) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ isLogger l ∗ ⌜sint.Z lvl < 3⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Check")) (Val #lvl)) (Val #msg))
  {{ (ce : Loc), RET #ce; ⌜ce = null⌝ ∨ entryOk ce }}

end spec

end Zap
end EtcdGrove
end Perennial
