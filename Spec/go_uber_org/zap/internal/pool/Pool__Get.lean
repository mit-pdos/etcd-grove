/-
`pool.Pool[T].Get` of zap's internal `pool` (`internal/pool/pool.go`: `return p.pool.Get().(T)`; zap-z2,
2026-11-23: zapcore's `getCheckedEntry`). Lean-first.
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

/-- `p.Get()` (a pool whose elements satisfy `Q`) (a pool of pointers, `T = *E`, as each of zap's) returns an element: one `Put` earlier or one its
`New` made, with `Q` (the type assertion `.(T)` succeeds: the pool holds only `T`-boxed values). -/
abbrev zap.internal.pool.Pool.Get.spec : Prop :=
  ∀ (E : go.GoType) (p : Loc) (Q : Loc → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.internal.pool ∗ zap.internal.pool.isPool (go.GoType.PointerType E) p Q }}
    (App (Val (p @!! go.GoType.PointerType (go_uber_org.zap.internal.pool.Pool.ty (go.GoType.PointerType E)) @!! go!"Get"))
      (Val #()))
  {{ (v : Loc), RET #v; Q v }}

end spec

end EtcdGrove
end Perennial
