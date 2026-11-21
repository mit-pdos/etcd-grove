/-
`pool.New[T](fn)` of zap's internal `pool` (`internal/pool/pool.go`): its package variables'
constructor (zapcore's `_cePool`, `_jsonPool`, ...; prove-misc, 2026-11-20). Lean-first.
-/
module

public import GeneratedProof.go_uber_org.zap.internal.pool
public import Proof.go_uber_org.zap.PkgInit

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
`fn`, which it does not call). -/
abbrev zap.internal.pool.New.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (fn : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.internal.pool }}
    (App (Val #(functions go_uber_org.zap.internal.pool.New [T])) (Val #fn))
  {{ (p : Loc), RET #p; True }}

end spec

end EtcdGrove
end Perennial
