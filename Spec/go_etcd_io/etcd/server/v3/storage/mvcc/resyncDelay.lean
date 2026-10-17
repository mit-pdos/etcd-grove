/-
`resyncDelay` (`watchable_store.go`, added by etcd-io/etcd#22297). Lean-first (no Rocq
counterpart); see `Base.lean` for `watchResyncPeriod`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

/-- The delay `resyncDelay` picks: the last pass's duration `sd` when that pass made progress
(`last > un`), left watchers unsynced (`un ≠ 0`) and its duration is measurable (`sd > 0`);
otherwise `watchResyncPeriod` (`100 * time.Millisecond`, read-only at that value). -/
def mvcc.resyncDelayOf (sd last un : w64) : w64 :=
  if un ≠ W64 0 ∧ sint.Z un < sint.Z last ∧ 0 < sint.Z sd then sd else W64 100000000

theorem mvcc.resyncDelayOf_pos (sd last un : w64) : 0 < sint.Z (mvcc.resyncDelayOf sd last un) := by
  unfold mvcc.resyncDelayOf
  split
  · omega
  · decide

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `resyncDelay(syncDuration, lastUnsyncedWatchers, unsyncedWatchers)`: `resyncDelayOf` of its
arguments, a positive duration (`resyncDelayOf_pos`) — what `Ticker.Reset` needs — whatever the
measured `syncDuration` (zero or negative included). -/
abbrev mvcc.resyncDelay.spec : Prop :=
  ∀ (sd : time.Duration) (last un : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.resyncDelay)) (Val #sd))
      (Val #last)) (Val #un))
  {{ (d : time.Duration), RET #d; ⌜d = mvcc.resyncDelayOf sd last un ∧ 0 < sint.Z d⌝ }}

end spec

end EtcdGrove
end Perennial
