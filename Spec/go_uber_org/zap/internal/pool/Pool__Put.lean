/-
`pool.Pool[T].Put` of zap's internal `pool` (`internal/pool/pool.go`: `p.pool.Put(x)`; zap-z2, 2026-11-23:
zapcore's `putCheckedEntry`). Lean-first.
-/
module

public import GeneratedProof.go_uber_org.zap.internal.pool
public import Proof.go_uber_org.zap.PkgInit
public import Spec.go_uber_org.zap.internal.pool.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_uber_org.zap.internal.pool.Assumptions]

/-- `p.Put(x)` (a pool whose elements satisfy `Q`, `x` with `Q`) (a pool of pointers, `T = *E`, as each of zap's) gives `x` to the pool (which may drop
it). -/
abbrev zap.internal.pool.Pool.Put.spec : Prop :=
  ∀ (E : go.GoType) (p : Loc) (Q : Loc → IProp GF) (x : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.internal.pool ∗ zap.internal.pool.isPool (go.GoType.PointerType E) p Q ∗
      Q x }}
    (App (Val (p @!! go.GoType.PointerType (go_uber_org.zap.internal.pool.Pool.ty (go.GoType.PointerType E)) @!! go!"Put"))
      (Val #x))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
