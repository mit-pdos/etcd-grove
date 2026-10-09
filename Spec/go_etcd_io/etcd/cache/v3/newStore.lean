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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newStore(degree, historyCapacity)`: an empty store (`StoreState.init`) with a
history of capacity `historyCapacity`, for `degree > 1` (`btree.New` panics otherwise) and
`0 < historyCapacity ≤ 2^61` (`newRingBuffer`'s bound; Go's caller validates the
capacity). Returns the persistent `isStore`, the writer's half, a lower bound `0`, and the
`RWMutex`'s reader tokens but the writer's. -/
abbrev newStore.spec : Prop :=
  ∀ (degree historyCapacity : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ⌜1 < sint.Z degree⌝ ∗ ⌜0 < sint.Z historyCapacity ∧ sint.Z historyCapacity ≤ 2 ^ 61⌝ }}
    (App (App (Val (@! newStore)) (Val #degree)) (Val #historyCapacity))
  {{ (s : Loc) (γ : StoreNames), RET #s;
      isStore s γ (sint.nat historyCapacity) ∗
      storeWriter s γ (sint.nat historyCapacity) StoreState.init ∗
      storeRevLb γ (W64 0) ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (),
        storeReader s γ (sint.nat historyCapacity) }}

end spec

end EtcdGrove
end Perennial
