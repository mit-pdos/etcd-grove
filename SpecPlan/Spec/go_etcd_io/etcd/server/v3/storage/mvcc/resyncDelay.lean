/-
`resyncDelay(syncDuration, last, now)` (internal): the last pass's duration when it made progress
and watchers are left (and it is positive), else `watchResyncPeriod`: always positive
(`issues/etcd-watch-sync-ticker-reset-zero` was the fork's fix).

**Proof sketch.** The comparisons; `watchResyncPeriod` read (`watch_init.spec`).
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

def resyncDelay.spec : Prop :=
  ∀ (d last now : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.resyncDelay)) (Val #d)) (Val #last)) (Val #now))
  {{ RET #(if sint.Z now ≠ 0 ∧ sint.Z now < sint.Z last ∧ 0 < sint.Z d then d else W64 100000000);
      True }}

end spec

end Mvcc
end EtcdGrove
end Perennial
