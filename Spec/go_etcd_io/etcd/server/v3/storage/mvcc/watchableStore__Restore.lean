/-
`watchableStore.Restore` (`watchable_store.go`). Lean-first (no Rocq counterpart); see
`InvWatchStore.lean` and `store__Restore.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Restore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
back the new closer, fragment, token, the old backend's tokens and the new one's left over; no
restore in compaction mode (`store.Restore`'s two `cm = false` premises, Q5-3/Q5-4). -/
abbrev mvcc.watchableStore.Restore.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (L R : mvcc.Log),
  L <+: [[], []] ++ R → mvcc.restoreLogOk R →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ ⌜∃ d, γ.st.kb = some d ∧ d.cm = false⌝ ∗ ⌜d'.cm = false⌝ ∗
      mvcc.storeCloser st γ.st ∗ mvcc.writerFrag γ.st ∗ mvcc.writerOwn γ.st ∗
      mvcc.crevFrozen γ.st ∗ mvcc.watchWriter γ L ∗
      mvcc.certOk γ.st ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.storeBackendT b' st (γ.st.withPhys p) P') ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanRead b' (mvcc.bucketViewC (γ.st.withPhys p)) (mvcc.storeRT (γ.st.withPhys p))
          (mvcc.kbNoCmp (γ.st.withPhys p).kb (γ.st.withPhys p).bucket)) ∗
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

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `ws.Restore(b)`: the store's `Restore` (`store.Restore.specC`), its watchers reset to
resynchronize from the new state. The update gives that `σ'` extends the state's history and does not lower its
compaction revision (the stored hashes survive a restore and stay hashes of the history,
`mvccHashOk_state`; the watchers resynchronize from it). Each re-attached key is on a live lease
and shorter than `2 ^ 63 - 1` (`isLessor`'s `Attach`); the lessor's item map, emptied by its own
recovery, becomes the new state's. Open: the backend's identity (`mvccBackend`, `mvccBackendIs`,
the hook) is fixed in the vocabulary, but a restore replaces the backend; a compaction the new
backend left unfinished is resumed (`restore`'s `compactLockfree`: the hook and a commit) with no
contract here yet (the backend boundary, `notes/mvcc-api-candidate.md`). -/
abbrev mvcc.watchableStore.Restore.specC : Prop :=
  ∀ (ws : Loc) (γ : mvcc.MvccName) (b : Loc) (σ' : mvcc.MvccState) (L : List w64)
    (Q : mvcc.MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableMvcc ws γ ∗ mvcc.mvccOpen γ 1 ∗ mvcc.mvccRestorable γ b σ' ∗
      lease.leaseOwn (mvcc.mvccLeases γ) L ∅ ∗
      ⌜∀ it lid, (mvcc.pendItems σ'.log []).lookup it = some lid →
        lid ∈ L ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      AU <{ ∃∃ (σ : mvcc.MvccState), mvcc.mvccState γ σ ∗ ⌜σ.log <+: σ'.log ∧ σ.crev ≤ σ'.crev⌝ }>
          @ ⊤ \ ↑mvcc.mvccN, ∅
        <{ mvcc.mvccState γ σ', COMM Q σ }> }}
    (App (Val (ws @!! go.GoType.PointerType watchableStore.ty @!! go!"Restore"))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b)))
  {{ RET #(GoInterface.nil); mvcc.mvccOpen γ 1 ∗
      lease.leaseOwn (mvcc.mvccLeases γ) L (mvcc.pendItems σ'.log []) ∗ ∃ σ : mvcc.MvccState, Q σ }}

end spec

end EtcdGrove
end Perennial
