/-
`newWatcherBatch(wg, evs)` (internal): `nil` for an empty group; else each event (in order) added,
as a fresh copy (`Type`, `Kv` shared, `PrevKv`), to the batch of each watcher of its key whose
`minRev` is at most its revision (`wbOf`).

**Proof sketch.** `wg.watcherSetByKey(key)` for each event (its spec, the set lent by the group),
the records' `minRev`; `watcherBatch.add` of a fresh event struct (its `Kv` read-only, shared).
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

def newWatcherBatch.spec : Prop :=
  ∀ (wg : Loc) (v : watcherGroup) (dq dq' : DFrac) (G : List (Loc × MRange)) (R : Loc → WRec)
    (evs : GoSlice) (ps : List Loc) (es : List EvM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wg ↦{dq} v ∗ wgOwn v dq' G ∗ ([∗list] x ∈ G, wRecAt x.1 (R x.1)) ∗
      evs ↦*□ ps ∗ ([∗list] p; e ∈ ps; es, evOwn p e) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherBatch)) (Val #wg)) (Val #evs))
  {{ (wb : GoMap), RET #wb; wg ↦{dq} v ∗ wgOwn v dq' G ∗ ([∗list] x ∈ G, wRecAt x.1 (R x.1)) ∗
      ([∗list] p; e ∈ ps; es, evOwn p e) ∗ wbOwn wb (wbOf G (fun w => (R w).minRev) es) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
