/-
`watcherSetByKey.delete(wa)` (internal): `wa` removed from its key's set (the set removed when
empty); whether it was there.
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

def watcherSetByKey.delete.spec : Prop :=
  ∀ (m : GoMap) (K : Key → List Loc) (wa : Loc) (ι : WsNames) (id : w64) (W : WatcherM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wskOwn m K ∗ watcherAt wa ι id W }}
    (App (Val (m @!! watcherSetByKey.ty @!! go!"delete")) (Val #wa))
  {{ RET #(decide (wa ∈ K W.range.key));
      wskOwn m (fun k => if k = W.range.key then (K k).erase wa else K k) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
