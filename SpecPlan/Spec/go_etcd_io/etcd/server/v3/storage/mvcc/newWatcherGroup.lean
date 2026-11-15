/-
`newWatcherGroup()` (internal): an empty group (two maps and an interval tree over string keys:
`adt.NewIntervalTree`).
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

def newWatcherGroup.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup)) (Val #()))
  {{ (v : watcherGroup), RET #v; wgOwn v (DFrac.own 1) [] }}

end spec

end Mvcc
end EtcdGrove
end Perennial
