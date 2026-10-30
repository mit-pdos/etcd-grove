module
public import Proof.go_etcd_io.bbolt.internal.freelist.HashImpl
public import Proof.go_etcd_io.bbolt.internal.freelist.WeakState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.Init(pgids)`: the free ids become `pgids` (sorted, so `Init` does not panic: the new state
is weakly well-formed, `FLState.WFw`: the ids may be pending, as in `Reload`), the cache rebuilt
(`reindex`).

Unlike `array.Init`, `hashMap.Init` returns before `reindex` when `pgids` is empty: the cache
is then left as it was, holding the old free ids too. So this spec needs `xs ≠ []` or the old
free ids all pending (none in a well-formed state), when the old cache is already right. -/
abbrev hashMap.Init.spec : Prop :=
  ∀ (h s : Loc) (σ : FLState) (ids : GoSlice) (xs : List w64),
  ({ σ with free := xs } : FLState).WFw → (xs ≠ [] ∨ ∀ x ∈ σ.free, x ∈ σ.pendingIds) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ hashHdl (GF := GF) h s ∗
      ownSharedW s (hashMapImpl (GF := GF) h).iface σ ∗
      ownHashMap h s σ.free ∗ ids ↦* xs ∗ ownSliceCap w64 ids (DFrac.own 1) }}
    (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"Init")) (Val #ids))
  {{ RET #(); ownSharedW s (hashMapImpl (GF := GF) h).iface { σ with free := xs } ∗ ownHashMap h s xs }}

end spec

end bbolt
end EtcdGrove
end Perennial
