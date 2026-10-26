/-
`watchableStore.Restore` (`watchable_store.go`). Lean-first (no Rocq counterpart); see
`InvWatchStore.lean` and `store__Restore.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Restore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

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

/-- **`s.Restore(b')` of the watchable store `s` over the store `st`** (D22 receiver epochs, S6,
2026-10-22): under its `s.mu`, the inner store restored over the new backend `b'` holding the log
`L' = [[], []] ++ R` (`store.Restore`, whose precondition this collects: the watchable store's
lock gives its quarter of the fields and its deposit, `wsFields 1`, and the outer quarter of the
committed log's authority, `wlogQ`), then every synced watcher moved to the unsynced group with
its `restore` flag set (`syncWatchers` then sends it the restored log's events from its
`minRev`, or, past the restored log, moves it back: `chooseAll` clears the flag rather than
panic), the synced group emptied; `nil`. The sole writer at the committed (and notified) log `L`
(`watchWriter`) is at `L'` after: the lock's notified log is `L'` (no watcher is synced: the
restored revisions' events go out through `syncWatchers`). A move delivers no event: each moved
watcher keeps its delivered events, and the lock records it delivered up to its `minRev`, as
far as its events go (`popFacts`: nothing of its range between its `minRev` and its delivery
bound), so the clients' view of their watchers (`chanWatcher`, `isClientWatcher`) is unchanged.
The rest as `store.Restore`'s: the caller's parts of the inner store's current objects and names
(its closer, the writer's fragment and retired token, never compacted), the new backend's, and
back the new closer, fragment, token, the old backend's tokens and the new one's left over. -/
abbrev mvcc.watchableStore.Restore.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ ⌜∃ d, γ.st.kb = some d⌝ ∗
      mvcc.storeCloser st γ.st ∗ mvcc.writerFrag γ.st ∗ mvcc.writerOwn γ.st ∗
      mvcc.crevFrozen γ.st ∗ mvcc.watchWriter γ L ∗
      mvcc.certOk γ.st ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.storeBackendT b' st (γ.st.withPhys p) P') ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanRead b' (mvcc.bucketViewC (γ.st.withPhys p)) (mvcc.storeRT (γ.st.withPhys p))) ∗
      mvcc.kbViewC (some d') γb' 1 (mvcc.bucketMap ([[], []] ++ R)) ∗
      mvcc.kbNoCmp (some d') γb' ∗ mvcc.kbRegRight (some d') ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.storeCloser st (γ.st.withPhys p') ∗
      mvcc.writerFrag (γ.st.withPhys p') ∗ mvcc.writerOwn (γ.st.withPhys p') ∗
      mvcc.hookP (γ.st.withPhys p') P' ∗
      mvcc.watchWriter γ ([[], []] ++ R) ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1) (), mvcc.storeRT γ.st) ∗
      mvcc.storeRT (γ.st.withPhys p') }}

end spec

end EtcdGrove
end Perennial
