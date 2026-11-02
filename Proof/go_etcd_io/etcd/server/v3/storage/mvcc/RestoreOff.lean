/-
**`watchableStore.Restore` off** (M2's item 15, step A3): its spec before compaction mode
(`watchableStore.Restore.specOff`), which the switched spec gives at a store and a backend that do
not compact (`specOff_of_spec`), for the server's callers until they restore in compaction mode
(M2's Stage B).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Restore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section off
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`watchableStore.Restore`'s spec before compaction mode** (D22 receiver epochs, S6,
2026-10-22; `watchableStore.Restore.spec` until M2's item 15, kept for the server's callers, which
restore over backends that do not compact until M2's Stage B): under its `s.mu`, the inner store restored over the new backend `b'` holding the log
`L' = [[], []] ++ R` (`store.Restore`, whose precondition this collects: the watchable store's
lock gives its quarter of the fields and its deposit, `wsFields 1`, and the outer quarter of the
committed log's authority, `wlogQ`), then every synced watcher moved to the unsynced group with
its `restore` flag set (`syncWatchers` then sends it the restored log's events from its
`minRev`, or, past the restored log, moves it back: `chooseAll` clears the flag rather than
panic), the synced group emptied; `nil`. The sole writer at the committed (and notified) log `L`
(`watchWriter`) is at `L'` after, at the inner store's new physical names (with the writer's pin
there, `writerPin`; M2's item 37, 2026-11-02): the lock's notified log is `L'` (no watcher is synced: the
restored revisions' events go out through `syncWatchers`). A move delivers no event: each moved
watcher keeps its delivered events, and the lock records it delivered up to its `minRev`, as
far as its events go (`popFacts`: nothing of its range between its `minRev` and its delivery
bound), so the clients' view of their watchers (`chanWatcher`, `isClientWatcher`) is unchanged.
The rest as `store.Restore`'s: the caller's parts of the inner store's current objects and names
(its closer, the writer's fragment and retired token, never compacted), the new backend's, and
back the new closer, fragment, token, the old backend's tokens and the new one's left over; no
restore in compaction mode (`store.Restore`'s two `cm = false` premises, Q5-3/Q5-4). -/
abbrev mvcc.watchableStore.Restore.specOff : Prop :=
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
      mvcc.kbNoCmp (some d') γb' ∗ mvcc.kbNoDel (some d') ∗ mvcc.kbRegRight (some d') ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d')) }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"Restore")) (Val #b'))
  {{ RET #GoInterface.nil; ∃ p' : mvcc.PhysNames,
      ⌜p'.bucket = γb' ∧ p'.kb = some d'⌝ ∗
      mvcc.storeCloser st (γ.st.withPhys p') ∗
      mvcc.writerFrag (γ.st.withPhys p') ∗ mvcc.writerOwn (γ.st.withPhys p') ∗
      mvcc.hookP (γ.st.withPhys p') P' ∗
      mvcc.watchWriter { γ with st := γ.st.withPhys p' } ([[], []] ++ R) ∗
      ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1) (), mvcc.storeRT γ.st) ∗
      mvcc.storeRT (γ.st.withPhys p') }}

/-- **Off, the spec reads as before compaction mode**: at no record and the revision `-1`. -/
theorem mvcc.watchableStore.Restore.specOff_of_spec
    (h : mvcc.watchableStore.Restore.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.Restore.specOff (GF := GF) (hG := hG) := by
  intro s st γ b' d' γb' P' L R hpre hR
  iintro %Φ ⟨#Hpkg, #Hws, %Hd, %Hd', Hcl, Hwf, Hwo, #Hfrz, Hww, #Hok, Hbk, Hkc, Hv, Hnc, #Hnd, Hrr,
    Hrts⟩ HΦ
  obtain ⟨d, hγd, hdcm⟩ := Hd
  obtain ⟨hoff, -, hsr, hws, -⟩ := mvcc.cmOff_true (GF := GF) d' Hd'
  obtain ⟨hoffd, hj0d, -, -, -⟩ := mvcc.cmOff_true (GF := GF) d hdcm
  have hoffγ : ¬ mvcc.kbCmpM γ.st.kb := by rw [hγd]; exact hoffd
  have hc : (-1 : Int) ≤ mvcc.CmpRecs.empty.crev := by rw [mvcc.CmpRecs.crev_empty]; exact Int.le_refl _
  iapply (h s st γ b' d' γb' P' L R (-1) mvcc.CmpRecs.empty hpre hR hc) $$
    [Hcl Hwf Hwo Hww Hbk Hkc Hv Hnc Hrr Hrts]
  · iframe Hpkg Hws Hwf Hwo Hww Hok Hrr Hrts
    simp only [mvcc.kbNoDelOff, hoff, ↓reduceIte]
    iframe Hnd
    rw [mvcc.restoreRcptM_off d' _ Hd', mvcc.CmpRecs.finRev_empty, mvcc.CmpRecs.crev_empty]
    isplitr
    · itrivial
    isplitr
    · iapply mvcc.crevPermAt_none
    isplitr
    · iapply mvcc.crevPermAt_none
    isplitr
    · ipureintro; exact ⟨d, hγd, by rw [Hd', hdcm]⟩
    isplitl [Hcl]
    · iapply (mvcc.restoreRightM_off st γ.st (-1) hoffγ).2
      iframe Hcl Hfrz; ipureintro; rfl
    isplitl [Hbk]
    · iintro %p %hp -
      ihave Hk := Hbk $$ %p %hp
      rw [mvcc.storeBackendTR_empty]
      iexact Hk
    isplitl [Hkc]
    · iintro %p %hp
      ihave Hk := Hkc $$ %p %hp
      rw [mvcc.kbRecs_empty]
      iapply mvcc.keyCleanReadR_frame
      rw [mvcc.keyCleanReadR_empty]
      iexact Hk
    isplitl [Hv Hnc]
    · iapply (mvcc.restoreImageM_off d' γb' _ mvcc.CmpRecs.empty Hd').2
      iframe Hv Hnc; ipureintro; rfl
    rw [hsr, hws, mvcc.resumeHookM_no _ _ mvcc.CmpRecs.resumes_empty, mvcc.restoreRegM_off d' Hd']
    isplitr <;> try isplitr
    all_goals itrivial
  have hr : mvcc.nReaders - 1 - mvcc.nJobRd γ.st.kb = mvcc.nReaders - 1 := by rw [hγd, hj0d]; rfl
  rw [hr]
  iintro !> ⟨%p', %hp', Hcl', Hwf, Hwo, #Hhook, Hww, -, -, Hrd, Hrt⟩
  iapply HΦ
  iexists p'
  have hoffp : ¬ mvcc.kbCmpM (γ.st.withPhys p').kb := by
    rw [StoreNames.withPhys_kb, hp'.2]; exact hoff
  ihave Hcl' := (mvcc.storeCloserM_off st (γ.st.withPhys p') _ hoffp).1 $$ Hcl'
  iframe Hcl' Hwf Hwo Hhook Hww Hrd Hrt
  ipureintro; exact hp'

end off

end EtcdGrove
end Perennial
