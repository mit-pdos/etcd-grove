/-
`zap.Logger.Info`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import GeneratedProof.go_uber_org.zap
public import Spec.go_uber_org.zap.Defs

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

/-- `l.Info(msg, fields...)` (a zap logger, `zapLoggerOk l`; premise fixes 6: a zero `&zap.Logger{}` panics) returns: logging has no effect here. -/
abbrev zap.Logger.Info.spec : Prop :=
  ∀ (l : Loc) (msg : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ zapLoggerOk l }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Info")) (Val #msg)) (Val #fields))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
