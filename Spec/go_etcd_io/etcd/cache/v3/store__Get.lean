/-
`store.Get` (`cache/*.go`), an internal helper.
Users: `Cache.Get`.
Proof sketch: `store.getSnapshot.spec`, then `snapshot.Range.spec` on the snapshot (frozen: read after the lock is released); the range inside the prefix (`rangeOk`).
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

/-- `s.Get(start, end, rev)`: for a range the cache serves, the key-values of etcd's store at `rev` (the latest for `0`) in the range, and the latest revision; or an error. -/
def store.Get.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (pfx : GoString) (startSl endSl : GoSlice) (sk ek : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isStore s γ pfx ∗ startSl ↦*□ sk ∗ endSl ↦*□ ek ∗ ⌜rangeOk pfx ({ key := sk, rangeEnd := ek } : KeyRange)⌝ }}
    (App (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.store.ty @!! go!"Get")) (Val #startSl)) (Val #endSl)) (Val #rev))
  {{ (kvsSl : GoSlice) (lrev : w64) (err : GoInterface), RET (PairV (PairV #kvsSl #lrev) #err);
      (⌜err = GoInterface.nil⌝ ∗ storeRevLb s (sint.Z lrev).toNat ∗
        ∃ (σ : State) (kvs : List KV), etcdLb γ σ ∗
          msgsOwn keyValueOwn kvsSl DFrac.discard (kvs.map KeyValueM.ofKV) ∗
          ⌜0 ≤ sint.Z rev ∧ sint.Z rev ≤ sint.Z lrev ∧ sint.Z lrev ≤ σ.kv.rev ∧
            Store.rangeKVs (σ.kv.storeAt (if sint.Z rev = 0 then (sint.Z lrev).toNat else (sint.Z rev).toNat))
              ({ key := sk, rangeEnd := ek } : KeyRange) kvs⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end Cache
end EtcdGrove
end Perennial
