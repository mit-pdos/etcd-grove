/-
`(*watcherGroup).contains(key)` (internal): whether a watcher of the group watches `key` (its key's
set, or `ranges.Intersects` of the key's point).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def watcherGroup.contains.spec : Prop :=
  ∀ (wg : Loc) (v : watcherGroup) (dq dq' : DFrac) (G : List (Loc × MRange)) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wg ↦{dq} v ∗ wgOwn v dq' G }}
    (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"contains")) (Val #k))
  {{ RET #(decide (∃ y ∈ G, y.2.watchMem k)); wg ↦{dq} v ∗ wgOwn v dq' G }}

end spec

end Mvcc
end EtcdGrove
end Perennial
