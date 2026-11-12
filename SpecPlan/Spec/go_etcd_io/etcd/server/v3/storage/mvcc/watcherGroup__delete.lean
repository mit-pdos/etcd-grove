/-
`(*watcherGroup).delete(wa)` (internal): `wa` removed (from the set of all, and its key's set or its
range's set, the range removed from the tree when its set empties: the tree's `Delete` succeeds, the
group's invariant); whether it was in the group.
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

def watcherGroup.delete.spec : Prop :=
  ∀ (wg : Loc) (v : watcherGroup) (dq : DFrac) (G : List (Loc × MRange)) (wa : Loc) (ι : WsNames)
    (id : w64) (W : WatcherM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wg ↦{dq} v ∗ wgOwn v (DFrac.own 1) G ∗ watcherAt wa ι id W }}
    (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"delete")) (Val #wa))
  {{ RET #(decide (wa ∈ G.map Prod.fst)); wg ↦{dq} v ∗
      wgOwn v (DFrac.own 1) (G.filter (fun x => decide (x.1 ≠ wa))) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
