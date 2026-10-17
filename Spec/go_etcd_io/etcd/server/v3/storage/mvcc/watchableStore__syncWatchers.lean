/-
`watchableStore.syncWatchers` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.syncWatchers()` with the caller's reader slots: under `s.mu` (and `s.store.revMu` read), a
batch of the unsynced watchers (`choose`) is grouped into cohorts by `minRev`
(`cohortsByRevision`, etcd-io/etcd#22304), and each cohort gets the events of the committed log
in a window of at most `watchBatchMaxRevs + 1` revisions from its least `minRev`, or up to the
current revision if that is nearer (`syncWatcherCohort`), each member its own
(`newWatcherBatch`): a member with none becomes synced if the window reached the current revision,
else stays unsynced at the window's end; one with events gets them in one response (all of them,
or under the cap of `watchBatchMaxRevs` revisions those below the first revision left out), and
becomes synced if the window reached the current revision and none was left out, stays unsynced
otherwise, or becomes a victim with its batch if its channel is full. The lock invariant is kept
(every delivery recorded); the number returned is the unsynced watchers left. (Before #22304: one
scan from the batch's least `minRev` up to the current revision.) -/
abbrev mvcc.watchableStore.syncWatchers.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.watchReader s st γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"syncWatchers")) (Val #()))
  {{ (n : w64), RET #n; mvcc.watchReader s st γ }}

end spec

end EtcdGrove
end Perennial
