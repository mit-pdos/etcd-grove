/-
`(*watcherGroup).add(wa)` (internal): `wa` added to the set of all, and to its key's set (a single
key) or its range's set in the interval tree (`Find`, then the set's `add`; a new set `Insert`ed).

**Proof sketch.** `watcherSet.add`; `watcherSetByKey.add`; `adt.NewStringAffineInterval`,
`ranges.Find` (`Adt.intervalTree.Find.spec`: the set lent, its `add`, the tree back),
`ranges.Insert` (below `ivtCountMax` entries: at most one per watcher, the premise).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import Spec.go_uber_org.zap.Api

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

def watcherGroup.add.spec : Prop :=
  ∀ (wg : Loc) (v : watcherGroup) (dq : DFrac) (G : List (Loc × MRange)) (wa : Loc) (ι : WsNames)
    (id : w64) (W : WatcherM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wg ↦{dq} v ∗ wgOwn v (DFrac.own 1) G ∗ watcherAt wa ι id W ∗
      ⌜wa ∉ G.map Prod.fst ∧ G.length < Adt.ivtCountMax⌝ }}
    (App (Val (wg @!! go.GoType.PointerType watcherGroup.ty @!! go!"add")) (Val #wa))
  {{ RET #(); wg ↦{dq} v ∗ wgOwn v (DFrac.own 1) (G ++ [(wa, W.range)]) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
