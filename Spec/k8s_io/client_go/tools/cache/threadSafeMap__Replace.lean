/-
`(*threadSafeMap).Replace(items, resourceVersion)` (`thread_safe_store.go:393`): replaces the items
(the store keeps the caller's map) and the resource version, and rebuilds the indices, under the
write lock. Lean-first.
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

/-- **`c.Replace(nl, rv)`**, logically atomic, for a map `nl` of objects each `nil` or meeting `OK`
(the store takes the map): the items are `its` and the resource version `rv` (even `""`). -/
abbrev threadSafeMap.Replace.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (nl : Loc)
    (its : Items) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      nl ↦$ its ∗ □ ([∗map] _k ↦ o ∈ its, okNil OK o) }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"Replace")) (Val #nl))
      (Val #rv))
    @@ ∅
  <<{ storeSt γ (σ.replace its rv) }>>
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
