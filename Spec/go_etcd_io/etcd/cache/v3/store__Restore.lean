/-
`store.Restore` (`cache/*.go`), an internal helper.
Users: `Cache.get` (the initial list, and every re-list).
Proof sketch: under the write lock: a new tree (`BTree.New.spec`) with each key-value inserted (`newKVItem.spec`, `BTree.ReplaceOrInsert.spec`), the history emptied and the one snapshot appended (`newClonedSnapshot.spec`, `ringBuffer.Append.spec`); its certificate is the list's (`snapCert`); the ceiling at most `rev` keeps the latest revision monotone; `Broadcast` on `revCond`.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

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

/-- `s.Restore(kvs, rev)` by the ceiling's holder, for key-values that are etcd's store under the prefix at `rev`: the store is that snapshot at `rev`. -/
def store.Restore.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (pfx : GoString) (r : Nat) (kvsSl : GoSlice) (rev : w64) (σ : State)
    (kvs : List KV),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isStore s γ pfx ∗ storeCeil s r ∗ msgsOwn keyValueOwn kvsSl DFrac.discard (kvs.map KeyValueM.ofKV) ∗ etcdLb γ σ ∗ ⌜r ≤ sint.Z rev ∧ sint.Z rev = σ.kv.rev ∧ Store.rangeKVs σ.kv.store (prefixRange pfx) kvs⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.store.ty @!! go!"Restore")) (Val #kvsSl)) (Val #rev))
  {{ RET #(); storeCeil s (sint.Z rev).toNat ∗ storeRevLb s (sint.Z rev).toNat ∗
      storeUpTo s (sint.Z rev + 1) }}

end spec

end Cache
end EtcdGrove
end Perennial
