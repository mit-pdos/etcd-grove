/-
`newKVItem` (`cache/*.go`), an internal helper.
Users: `store.Restore`, `store.applyEventsLocked`.
Proof sketch: reads `kv.Key` (read-only), allocates the item.
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

/-- `newKVItem(kv)`: an item keyed by the key-value's key. -/
def newKVItem.spec : Prop :=
  ∀ (kv : Loc) (dq : DFrac) (m : KeyValueM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ keyValueOwn kv dq m }}
    (App (Val (@! go_etcd_io.etcd.cache.v3.newKVItem)) (Val #kv))
  {{ (p : Loc), RET #p; keyValueOwn kv dq m ∗ kvItemAt p m.key kv }}

end spec

end Cache
end EtcdGrove
end Perennial
