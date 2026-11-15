/-
`newStore` (`cache/*.go`), an internal helper.
Users: `newCache`.
Proof sketch: `btree.New.spec` at `kvItemLess` (`BTree.New.spec`, the degree's bounds), `newRingBuffer.spec`, `sync.NewCond` on the read locker; allocates the invariant (latest `0`, no snapshot) and the ceiling at `0`.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newStore(degree, historyCapacity)`: an empty store for any cluster and prefix. -/
def newStore.spec : Prop :=
  ∀ (γ : Cluster) (pfx : GoString) (degree cap : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ ⌜2 ≤ sint.Z degree ∧ sint.Z degree ≤ 2 ^ 62 ∧ 0 < sint.Z cap ∧ sint.Z cap ≤ 2 ^ 61⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.cache.v3.newStore)) (Val #degree)) (Val #cap))
  {{ (s : Loc), RET #s; isStore s γ pfx ∗ storeCeil s 0 }}

end spec

end Cache
end EtcdGrove
end Perennial
