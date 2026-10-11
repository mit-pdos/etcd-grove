/-
`newStore(degree, historyCapacity)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newStore(degree, historyCapacity)`: an empty store (`StoreState.init`) with a
history of capacity `historyCapacity`, for `1 < degree <= 2^62` (`btree.New` panics below;
above, the btree's `maxItems()` overflows and its second insert panics) and
`0 < historyCapacity ≤ 2^61` (`newRingBuffer`'s bound; Go's caller validates the
capacity). Returns the persistent `isStore` and `isStoreWriter` (any number of writers), a lower
bound `0`, and all but one of the `RWMutex`'s reader tokens. `E` is the store's snapshot
certificate (`snapCert`), `R` its latest revision's, chosen by the caller (`R 0` for the empty
store). -/
abbrev newStore.spec : Prop :=
  ∀ (E : w64 → KvMap → IProp GF) (R : w64 → IProp GF) (degree historyCapacity : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ⌜1 < sint.Z degree ∧ sint.Z degree ≤ 2 ^ 62⌝ ∗ ⌜0 < sint.Z historyCapacity ∧ sint.Z historyCapacity ≤ 2 ^ 61⌝ ∗
      □ R (W64 0) }}
    (App (App (Val (@! newStore)) (Val #degree)) (Val #historyCapacity))
  {{ (s : Loc) (γ : StoreNames), RET #s;
      isStore s γ (sint.nat historyCapacity) ∗
      isStoreWriter s γ (sint.nat historyCapacity) E R ∗
      storeRevLb γ (W64 0) ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (),
        storeReader s γ (sint.nat historyCapacity) E R }}

end spec

end EtcdGrove
end Perennial
