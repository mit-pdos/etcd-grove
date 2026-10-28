/-
`(*threadSafeMap).GetIndexers()` (`thread_safe_store.go:501`): the store's own indexers' map, read
without the lock. Lean-first.

The result is the map the store's lock guards (`tsP` holds `γ.im ↦$ ph.fv`): `AddIndexers` writes
it under the write lock, so a caller reading it (`GetIndexers()[name]`, as `pkg/controller`'s
`AddPodNodeNameIndexer` does) races with a concurrent `AddIndexers` (Go: a concurrent map read and
write; `issues/k8s-clientgo-getindexers-unlocked-map.md`). The spec gives only the location: a
read of it needs the map's points-to, which no client holds while the store exists.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `c.GetIndexers()`: the store's indexers' map `γ.im` (shared with the store, not a copy). -/
abbrev threadSafeMap.GetIndexers.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam }}
    (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"GetIndexers")) (Val #()))
  {{ RET #γ.im; True }}

end spec

end cache
end EtcdGrove
end Perennial
