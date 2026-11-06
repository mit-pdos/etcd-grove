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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`s.Restore(b')` of the watchable store `s` over the store `st`, in either mode** (D22
receiver epochs, S6, 2026-10-22; in compaction mode, M2's item 15, 2026-11-02): under its `s.mu`,
the inner store restored over the new backend `b'` holding the log `L' = [[], []] ++ R`
(`store.Restore`, whose precondition this collects: the watchable store's lock gives its quarter of
the fields and its deposit, `wsFields 1`, and the outer quarter of the committed log's authority,
`wlogQ`), then every synced watcher moved to the unsynced group with its `restore` flag set
(`syncWatchers` then sends it the restored log's events from its `minRev`, or, past the restored
log, moves it back: `chooseAll` clears the flag rather than panic), the synced group emptied;
`nil`. The committed (and notified) log, a prefix of `L'` (the caller's premise over every
certified log; 2026-11-06: until then the sole writer's `watchWriter`, whose tokens and pin the
inner store's writer state now keeps, its notified-log half the lock's), is `L'` after: the lock's
notified log is `L'` (no watcher is synced: the restored revisions' events
go out through `syncWatchers`). A move delivers no event: each moved watcher keeps its delivered
events, and the lock records it delivered up to its `minRev`, as far as its events go (`popFacts`:
nothing of its range between its `minRev` and its delivery bound), so the clients' view of their
watchers (`chanWatcher`, `isClientWatcher`) is unchanged. The rest is `store.Restore`'s, by the
mode (the mode survives the install, `d'.cm = d.cm`): the restored log's receipt and the
compaction permit at the image's records `r` (`restoreRcptM`, `crevPermAt`), what `Restore` takes
of the inner store's right at its compaction revision `c ≤ r.crev` (`restoreRightM`), the writer's
fragment and retired tokens, the new backend's image, contract, clean read and tokens at the
records, and back the inner store's right at `r.crev` at the new names (`storeCloserM`), fragment,
tokens, the unset hook lent (`resumeHookM`), the old job's budgets (`compactJobResM`), the old
backend's readers and the new one's left over, the leases attached (the owner's map from `∅` to
`pendItems L' []`, each restored item's lease live); off, as before compaction mode
(`watchableStore.Restore.specOff_of_spec`). -/
abbrev mvcc.watchableStore.Restore.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (b' : GoInterface) (d' : mvcc.KBReal) (γb' : GName)
    (P' : IProp GF) (R : mvcc.Log) (c : Int) (r : mvcc.CmpRecs) (Ls : List w64) (Rr : IProp GF),
  mvcc.restoreLogOk R → c ≤ r.crev →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.restoreRcptM d' ([[], []] ++ R) ∗ mvcc.crevPermAt γ.st r.finRev ∗
      mvcc.crevPermAt γ.st r.crev ∗
      mvcc.isWatchableStore s st γ ∗ ⌜∃ d, γ.st.kb = some d ∧ d'.cm = d.cm⌝ ∗
      mvcc.restoreRightM st γ.st c ∗ mvcc.writerFrag γ.st ∗ mvcc.writerOwn γ.st ∗
      mvcc.certOk γ.st ([[], []] ++ R) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.restoreFixM d' (γ.st.withPhys p) -∗ mvcc.storeBackendTR b' st (γ.st.withPhys p) P' r) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb' ∧ p.kb = some d'⌝ →
        mvcc.keyCleanReadR b' (mvcc.bucketViewC (γ.st.withPhys p))
          iprop(mvcc.storeRT (γ.st.withPhys p) ∗ mvcc.restoreRegM d')
          (mvcc.kbRecs (γ.st.withPhys p).kb (γ.st.withPhys p).bucket r) r) ∗
      mvcc.restoreImageM d' γb' ([[], []] ++ R) r ∗ mvcc.kbNoDelOff (some d') ∗
      mvcc.kbRegRight (some d') ∗
      mvcc.restoreRegM d' ∗ mvcc.kbSRM (some d') ∗ mvcc.kbWTSupplyM (some d') ∗ mvcc.resumeHookM d' r ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) ∗
      lease.leaseOwn γ.st.leases Ls ∅ ∗
      ⌜∀ it lid, (mvcc.pendItems ([[], []] ++ R) []).lookup it = some lid →
        lid ∈ Ls ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      mvcc.api.shareTok γ.st.api 1 ∗ mvcc.restoreCb γ.st ([[], []] ++ R) r.crev Rr }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.storeCloserM st (γ.st.withPhys p') r.crev ∗
      mvcc.writerFrag (γ.st.withPhys p') ∗ mvcc.writerOwn (γ.st.withPhys p') ∗
      mvcc.hookP (γ.st.withPhys p') P' ∗
      mvcc.resumeHookM d' r ∗
      mvcc.compactJobResM γ.st.kb ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1 - mvcc.nJobRd γ.st.kb) (), mvcc.storeRT γ.st) ∗
      mvcc.storeRT (γ.st.withPhys p') ∗
      lease.leaseOwn γ.st.leases Ls (mvcc.pendItems ([[], []] ++ R) []) ∗
      mvcc.api.shareTok γ.st.api 1 ∗ Rr }}

end spec

end EtcdGrove
end Perennial
