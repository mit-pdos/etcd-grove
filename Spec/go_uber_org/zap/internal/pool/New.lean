/-
`pool.New[T](fn)` of zap's internal `pool` (`internal/pool/pool.go`): its package variables'
constructor (zapcore's `_cePool`, `_jsonPool`, ...; prove-misc, 2026-11-20). Lean-first.
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

/-- `pool.New[T](fn)` returns a pointer to a fresh `Pool[T]` (its `sync.Pool`'s `New` wrapping
`fn`, which it does not call): `ownPool` (zap-z2, 2026-11-23: until then `True`), which becomes an
`isPool` of the elements of any `Q` that `fn`'s results satisfy (`ownPool_init`). Stated for a
pointer type `T = *E` (each of zap's pools holds pointers; `New`'s closure boxes `fn()` as
`interface.mkOk T`, which needs `T`'s underlying type to be known). -/
abbrev zap.internal.pool.New.spec : Prop :=
  ∀ (E : go.GoType) (fn : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.internal.pool }}
    (App (Val #(functions go_uber_org.zap.internal.pool.New [go.GoType.PointerType E])) (Val #fn))
  {{ (p : Loc), RET #p; zap.internal.pool.ownPool (V := Loc) (go.GoType.PointerType E) p fn }}

end spec

end EtcdGrove
end Perennial
