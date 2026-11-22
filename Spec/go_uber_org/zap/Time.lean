/-
`zap.Time` (srvloops2, 2026-11-21: `ensureLeadership`'s debug log). Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.go_uber_org.zap
public import Perennial.Proof.time
public import Proof.go_uber_org.zap.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `zap.Time(...)` returns some field (`Field{Key: key, Type: zapcore.TimeType, Integer: val.UnixNano(),
Interface: val.Location()}`, or with `TimeFullType` and `val` itself outside `int64` nanoseconds). -/
abbrev zap.Time.spec : Prop :=
  ∀ (k : GoString) (v : _root_.Perennial.time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (App (Val (@! zap.Time)) (Val #k)) (Val #v))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end EtcdGrove
end Perennial
