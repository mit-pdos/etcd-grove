/-
**What `applySnapshot`'s walk gives `watchableStore.Restore`, by the mode** (M2's item 15, stage
B2; `notes/m2-storage-plan.md`, "Step 2: restore in compaction mode"): the received backend's parts
of `Restore`'s precondition from what `OpenSnapshotBackend` gives (`snap_restoreBackendM`: off, the
creator's registration fixed to nothing deletable and today's contract and clean read; on, the
registration lent to `restore()`'s read and fixed to the store's deletable keys for the contract,
the records read off the image), the safe-range slot, the hook `restore()` resumes a compaction
with, and the old backend's readers back for its `Close` (`snap_oldReaders`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClientLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendRecsSnap
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreImageOpen

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- On, the image's merged ghost gives the bit the contract takes (`fkV`; persistent). -/
theorem mvcc.restoreImageM_fkV (d' : mvcc.KBReal) (γb : GName) (L : mvcc.Log) (r : mvcc.CmpRecs)
    (hcm : d'.cm = true) :
    mvcc.restoreImageM (GF := GF) d' γb L r ⊢ mvcc.restoreImageM d' γb L r ∗ backend.fkV d'.γB true := by
  unfold mvcc.restoreImageM
  simp only [hcm, ↓reduceIte]
  iintro ⟨%ents, Hv, Hr, Hw, %h⟩
  iunfold backend.fkVM at Hw
  icases Hw with ⟨%n, %v, #Hw⟩
  isplitl [Hv Hr]
  · iexists ents
    iframe Hv Hr
    isplitr
    · iunfold backend.fkVM; iexists n, v; iexact Hw
    ipureintro; exact h
  iunfold backend.fkV
  iexists n, v
  iunfold backend.fkVD at Hw
  iexact Hw

/-- **The received backend's parts of `Restore`'s precondition, by the mode**, from what
`OpenSnapshotBackend` gives over the image `D` (`newPostK`: the backend, its view, its
compaction-key resource and its creator's registration `dlInit`): the contract and the clean
read at the records `r` (`storeBackendTR`, `keyCleanReadR`), the image (`restoreImageM_of_open`),
and the registration by the mode: off, fixed to nothing deletable (`dlNoDel_fix`, `kbNoDelOff`);
on, kept unfixed for `Restore` (`restoreRegM`), which lends it to `restore()`'s read and then fixes
it to the store's deletable keys (`restoreFixM`), which the contract takes. -/
theorem snap_restoreBackendM [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
    [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hbUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hLSR : backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (d' : mvcc.KBReal) (hbr : mvcc.bridgeParams d'.P) (Pk : IProp GF) (γb : GName)
    (γst : mvcc.StoreNames) (s : Loc) (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data)
    (hkI : mvcc.keyImageM d'.cm L r D) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend d'.γB d'.P (mvcc.lateW d'.gx) Pk d'.be ∗ mvcc.keySized d'.γB d'.P d'.be ∗
      backend.dlInit d'.γB ∗ backend.bViewC d'.γB 1 (backend.vData d'.P (D, ⟨∅, W64 0⟩)) true ∗
      backend.fkCl d'.γB d'.P D ⊢ |==> (
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb ∧ p.kb = some d'⌝ →
        mvcc.restoreFixM d' (γst.withPhys p) -∗
        mvcc.storeBackendTR (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d'.be) s (γst.withPhys p) Pk r) ∗
      (∀ p : mvcc.PhysNames, ⌜p.bucket = γb ∧ p.kb = some d'⌝ →
        mvcc.keyCleanReadR (interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d'.be)
          (mvcc.bucketViewC (γst.withPhys p))
          iprop(mvcc.storeRT (γst.withPhys p) ∗ mvcc.restoreRegM d')
          (mvcc.kbRecs (γst.withPhys p).kb (γst.withPhys p).bucket r) r) ∗
      mvcc.restoreImageM d' γb L r ∗ mvcc.kbNoDelOff (some d') ∗ mvcc.restoreRegM d') := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsz, HDl, Hv, Hfk⟩
  cases hcm : d'.cm with
  | false =>
    rw [hcm] at hkI
    obtain ⟨-, hr⟩ := (mvcc.keyImageM_off L r D).1 hkI
    have hoff : ¬ mvcc.kbCmpM (some d') := by simp [mvcc.kbCmpM, hcm]
    imod backend.dlNoDel_fix _ $$ HDl with #Hnd
    ihave #HsbT := mvcc.storeBackendT_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU
      hrUR hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe d' hbr hcm Pk γb
      $$ [$Hpkg $Hsch $Hb $Hsz $Hnd]
    ihave #HkcR := mvcc.keyCleanRead_of_backend hRT hrRL hrRU hrUR hID hName hSafe d' hbr Pk γb
      $$ [$Hpkg $Hsch $Hb $Hsz $Hnd]
    ihave Him := mvcc.restoreImageM_of_open (GF := GF) d' γb L r D hbr (by rw [hcm]; exact hkI)
      $$ [$Hv $Hfk]
    subst hr
    imodintro
    iframe Him
    isplitr
    · iintro %p %hp -
      rw [mvcc.storeBackendTR_empty]
      iapply HsbT $$ %s %(γst.withPhys p) %hp
    isplitr
    · iintro %p %hp
      rw [mvcc.kbRecs_empty]
      iapply mvcc.keyCleanReadR_frame
      rw [mvcc.keyCleanReadR_empty]
      iapply HkcR $$ %(γst.withPhys p) %hp
    rw [mvcc.kbNoDelOff_off _ hoff, mvcc.restoreRegM_off d' hcm]
    isplitr
    · simp only [mvcc.kbNoDel]; iexact Hnd
    itrivial
  | true =>
    rw [hcm] at hkI
    have hsign : mvcc.recsSign r := by
      unfold mvcc.keyImageM at hkI
      simp only [↓reduceIte] at hkI
      obtain ⟨-, -, -, -, hok, -⟩ := hkI
      exact mvcc.recsOk_sign L r hok
    ihave Him := mvcc.restoreImageM_of_open (GF := GF) d' γb L r D hbr (by rw [hcm]; exact hkI)
      $$ [$Hv $Hfk]
    icases mvcc.restoreImageM_fkV d' γb L r hcm $$ Him with ⟨Him, #Hfv⟩
    imodintro
    iframe Him
    isplitr
    · iintro %p %hp
      have hfix : mvcc.restoreFixM (GF := GF) d' (γst.withPhys p) =
          mvcc.storeDlReg d'.γB (γst.withPhys p).idx := by
        unfold mvcc.restoreFixM; simp [hcm]
      rw [hfix]
      iintro #Hreg
      have hp' : (γst.withPhys p).bucket = γb ∧ (γst.withPhys p).kb = some d' ∧
          (γst.withPhys p).idx = (γst.withPhys p).idx := ⟨hp.1, hp.2, rfl⟩
      iapply mvcc.storeBackendTR_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR
        hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP d' hbr Pk γb (γst.withPhys p).idx
        r hsign $$ [$Hpkg $Hsch $Hb $Hsz $Hreg $Hfv] %s %(γst.withPhys p) %hp'
    have hreg : mvcc.restoreRegM (GF := GF) d' = backend.dlInit d'.γB := by
      unfold mvcc.restoreRegM; simp [hcm]
    have hnd : mvcc.kbNoDelOff (GF := GF) (some d') = iprop(True) := by
      unfold mvcc.kbNoDelOff; simp [mvcc.kbCmpM, hcm]
    rw [hreg, hnd]
    iframe HDl
    iintro %p %hp
    have hk : (γst.withPhys p).kb = some d' := hp.2
    rw [hk, mvcc.kbRecs_some]
    iapply mvcc.keyCleanRead_of_backendC hRT hrRL hrRU hrUR hID hName hSafe d' hbr Pk γb r hsign
      $$ [$Hpkg $Hsch $Hb $Hsz] %(γst.withPhys p) %hp

/-- **The store's revision below the records'**: on, the caller's (`hcc`); off, `cmpRight`'s `-1`
and no record (`r = empty`, whose revision is `-1`). -/
theorem snap_cmpRight_le (E : apply.AEnv GF) (c : Int) (r : mvcc.CmpRecs)
    (hcc : mvcc.kbCmpM E.γ.kb → c ≤ r.crev) (hr : ¬ mvcc.kbCmpM E.γ.kb → r = mvcc.CmpRecs.empty) :
    apply.cmpRight (GF := GF) E c ⊢ apply.cmpRight E c ∗ ⌜c ≤ r.crev⌝ := by
  by_cases h : mvcc.kbCmpM E.γ.kb
  · iintro H
    iframe H
    ipureintro; exact hcc h
  · unfold apply.cmpRight
    simp only [h, ↓reduceIte]
    iintro %hc
    isplitr
    · ipureintro; exact hc
    ipureintro
    rw [hr h, mvcc.CmpRecs.crev_empty, hc]; exact Int.le_refl _

/-- The new backend's safe-range slot (`newPostK`'s `srSlot`) is the slot `Restore` takes by the
mode (`kbSRM`: on, the slot; off, nothing). -/
theorem snap_kbSRM (d' : mvcc.KBReal) : backend.srSlot (GF := GF) d'.be ⊢ mvcc.kbSRM (some d') := by
  unfold mvcc.kbSRM
  split
  · simp only [mvcc.kbSR]; iintro H; iexact H
  · iintro -; itrivial

/-- The new backend's unset hook (`newPostK`'s `plHook … nil`) lent to `Restore` by the mode
(`resumeHookM`: on and resuming a compaction, the hook; otherwise nothing) and given back. -/
theorem snap_resumeHook (d' : mvcc.KBReal) (r : mvcc.CmpRecs) :
    backend.plHook (GF := GF) d'.γB func.nil ⊢
      mvcc.resumeHookM d' r ∗ (mvcc.resumeHookM d' r -∗ backend.plHook d'.γB func.nil) := by
  unfold mvcc.resumeHookM
  split
  · simp only [mvcc.kbHookNil]
    iintro H
    iframe H
    iintro H; iexact H
  · iintro H
    isplitr
    · itrivial
    iintro -; iexact H

/-- **The old backend's readers back** (for its `Close`, which takes every share): `Restore`'s
readers of the old store, with the old job's (`compactJobResM`: on, its reader and slot). -/
theorem snap_oldReaders (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d) :
    ([∗list] _x ∈ List.replicate (mvcc.nReaders - 1 - mvcc.nJobRd γ.kb) (), mvcc.storeRT (GF := GF) γ) ∗
      mvcc.compactJobResM γ.kb ⊢
      [∗list] _x ∈ List.replicate (mvcc.nReaders - 1) (), mvcc.bkRTx (GF := GF) d.γB d.P d.be := by
  have hrt : mvcc.storeRT (GF := GF) γ = mvcc.bkRTx d.γB d.P d.be := by
    unfold mvcc.storeRT; rw [hk]; rfl
  rw [hrt, hk]
  cases hcm : d.cm with
  | false =>
    have hoff : ¬ mvcc.kbCmpM (some d) := by simp [mvcc.kbCmpM, hcm]
    rw [mvcc.nJobRd_off _ hoff, mvcc.compactJobResM_off _ hoff, Nat.sub_zero]
    iintro ⟨H, -⟩; iexact H
  | true =>
    have hon : mvcc.kbCmpM (some d) := by simp [mvcc.kbCmpM, hcm]
    have h1 : mvcc.nJobRd (some d) = 1 := by simp [mvcc.nJobRd, hcm]
    unfold mvcc.compactJobResM
    simp only [hon, ↓reduceIte, h1]
    have e : List.replicate (mvcc.nReaders - 1) () = List.replicate (mvcc.nReaders - 1 - 1 + 1) () := by
      congr 1; rw [mvcc.nReaders_val]
    rw [e]
    iintro ⟨H, Hrt, -⟩
    iapply (mvcc.rep_split _ (mvcc.nReaders - 1 - 1) 1).2
    iframe H
    simp only [List.replicate]
    iapply BigSepL.bigSepL_cons.2
    rw [kbRT_some]
    iframe Hrt
    iapply BigSepL.bigSepL_nil.2; itrivial

end lemmas

end EtcdGrove
end Perennial
