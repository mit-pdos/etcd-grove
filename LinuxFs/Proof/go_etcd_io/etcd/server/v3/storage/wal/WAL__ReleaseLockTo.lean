/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReleaseLockTo.lean` (W9 of
`notes/wal-fsext-plan.md`): the update committed right after `w.mu.Lock()` (`walInv_unlAU`); the loop
over the locks reads each lock's file name (`walLockNamed`: `Name()`, `filepath.Base`,
`parseWALName`), stopping at the first index `≥ a`; the earlier locks but the last of them closed
(all non-tail locks, `walLockH`); the reslice `w.locks[smaller:]` keeps the tail last
(`ownSlice_slice_with_cap`). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReleaseLockTo
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.parseWALName
public import LinuxFs.Spec.path.filepath.Base
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReleaseAu
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReleaseLocks
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.wp_proof
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [_root_.Perennial.path.filepath.Assumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_Base : filepath.Base.spec (GF := GF) (hG := hG))
    (wp_parse : go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.spec (W := W) P Mr := by
  intro R jr r w dir a t i n cs Q
  wp_start as ⟨#Harea, Hw, #Hsy, Hau⟩
  icases (walOpenWF_iff P Mr w dir).1 $$ Hw with ⟨%h, Hh, %hD, %hmd, %hend, Hr⟩
  icases walHandleIn_lockFacts P Mr w dir h TailMetaW $$ Hh with ⟨Hh, #Hmu, #Hsync, -⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu', Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk,
    Hopen, %Hpure⟩
  ihave ⟨Htw, #Hfn⟩ := walTailW_named f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out
    TailMetaW $$ Htw
  ihave ⟨Hlks, #Hnamed⟩ := walLocks_named lfs lt f name Hlt $$ Hlks Hltf Hfn
  ihave %Hll := ownSlice_len _ _ _ $$ Hls
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  ihave #Harea2 := Harea
  iunfold WalFs.walAreaOk at Harea2
  icases Harea2 with ⟨#Hinv, #Hosinv, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  -- the commit, right after the lock
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walInv_unlAU walCodec Mr R jr r dir (fun d => walReleasePos (d.H.map WalOpG.toM) a)
    (fun d => d.H[i]? = some (WalOpG.snap ⟨cs, a, t⟩) ∧ i < n) Q $$ Hinv Hnc Hau with ⟨Hnc, %d, HQ⟩
  imodintro
  iframe Hnc
  (try wp_auto)
  have hlen : 0 < lfs.length := by
    obtain ⟨ls, rfl⟩ := List.getLast?_eq_some_iff.1 Hlt; simp
  have hne : locks.len ≠ W64 0 := by
    intro h0; have h1 := Hll.1; rw [h0] at h1; change lfs.length = 0 at h1; omega
  simp only [decide_eq_false hne]
  wp_auto
  -- the loop over the locks' names (`i2`: Go's `i`; `i`: the range's counter)
  rename_i i2_ptr
  irename i => Hcnt
  irename i => i2
  irename Hcnt => i
  ihave IH : iprop(∃ (k : w64) (lv : Loc) (iv : w64),
      "i" ∷ i_ptr ↦ k ∗ "l" ∷ l_ptr ↦ lv ∗ "i2" ∷ i2_ptr ↦ iv ∗ "Hls" ∷ locks ↦* lfs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ lfs.length⌝) $$ [i l i2 Hls]
  · iexists W64 0, _, _
    simp only [named]
    iframe
    ipureintro; exact ⟨by decide, by simp⟩
  wp_join (Q := fun v => iprop(∃ (sm : w64) (fnd : Bool) (err : GoInterface),
      «$res0_ptr» ↦ err ∗ smaller_ptr ↦ sm ∗ found_ptr ↦ fnd ∗ index_ptr ↦ a ∗ locks ↦* lfs ∗
      ⌜(v = executeVal ∧ err = GoInterface.nil ∧ ((fnd = false ∧ sm = W64 0) ∨
          (fnd = true ∧ -1 ≤ sint.Z sm ∧ sint.Z sm + 2 ≤ (lfs.length : Int)))) ∨
        v = returnVal #()⌝))
    at (App (App (App (Val doFor) _) _) _) with [IH «$res0» smaller found index]
  · wp_for IH
    obtain ⟨Hk0, Hkl⟩ := Hk
    wp_if_destruct
    · have hkl : sint.nat k < lfs.length := by
        have : sint.Z k < sint.Z locks.len := Hif
        rw [Hll.1]; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by have : sint.Z k < sint.Z locks.len := Hif; exact this⟩)]
      obtain ⟨lf, hlf⟩ : ∃ lf, lfs[sint.nat k]? = some lf := ⟨_, List.getElem?_eq_getElem hkl⟩
      wp_apply wp_load_slice_index locks (sint.Z k) lfs (DFrac.own 1) lf Hk0 $$ [Hls] as Hls
      · iframe; ipureintro; exact hlf
      (try wp_auto)
      ihave #Hlfn := (BigSepL.bigSepL_lookup (PROP := IProp GF) hlf) $$ Hnamed
      iunfold walLockNamed at Hlfn
      icases Hlfn with ⟨%f1, %nm1, #Hlf1, #Hfn1⟩
      ihave #Hlf2 := Hlf1
      iunfold fileutil.lockedFile at Hlf2
      iStructNamed Hlf2
      wp_method_call
      wp_call
      (try wp_auto)
      wp_apply os.File.Name.wp_named f1 nm1 $$ []
      · iexact Hfn1
      (try wp_auto)
      wp_apply wp_Base as %bn %hbn
      (try wp_auto)
      wp_apply wp_parse as %sq' %ix' %perr %hpe
      (try wp_auto)
      cases perr with
      | ok ie =>
        wp_auto
        iapply wp_for_post_return
        iexists _, _, _
        iframe
        ipureintro; right; rfl
      | nil =>
        wp_auto
        wp_if_destruct
        · (try wp_auto)
          iapply wp_for_post_break
          iexists _, true, _
          iframe
          ipureintro
          left
          refine ⟨rfl, rfl, Or.inr ⟨rfl, ?_, ?_⟩⟩
          · word
          · have : sint.nat k < sint.nat locks.len := Hll.1 ▸ hkl
            word
        · wp_for_post
          iframe
          iexists k + W64 1, lf, k
          simp only [named]
          iframe
          ipureintro
          have : sint.nat k < sint.nat locks.len := Hll.1 ▸ hkl
          constructor
          · word
          · rw [Hll.1]; word
    · (try wp_auto)
      iexists _, _, _
      iframe
      ipureintro
      left
      exact ⟨trivial, rfl, Or.inl ⟨rfl, rfl⟩⟩
  iintro ⟨%sm, %fnd, %err, «$res0», smaller, found, index, Hls, %Hq⟩
  rcases Hq with ⟨rfl, rfl, Hsm⟩ | rfl
  rotate_left
  · -- a lock's name `parseWALName` rejects: nothing closed
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    iframe HQ
    iapply (walOpenWF_iff P Mr w dir).2
    iexists h
    iframe Hr
    isplitl
    · iunfold walHandleIn
      iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
      iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
        Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
      ipureintro; exact ⟨Hen, Hlt, Hpure⟩
    · ipureintro; exact ⟨hD, hmd, hend⟩
  wp_auto
  have hlen63 : (lfs.length : Int) = sint.Z locks.len := by
    rw [Hll.1]; word
  wp_join (iprop(∃ sm' : w64, smaller_ptr ↦ sm' ∗ w_ptr ↦ w ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      ⌜-1 ≤ sint.Z sm' ∧ sint.Z sm' + 1 ≤ (lfs.length : Int)⌝)) at next with [smaller w Hlocks]
  · rcases Hsm with ⟨rfl, rfl⟩ | ⟨rfl, h2, h3⟩
    · wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro
      constructor <;> word
    · wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro
      omega
  iintro ⟨%sm', smaller, w, Hlocks, %Hsm'⟩
  wp_auto
  wp_if_destruct
  · -- nothing to release
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    iframe HQ
    iapply (walOpenWF_iff P Mr w dir).2
    iexists h
    iframe Hr
    isplitl
    · iunfold walHandleIn
      iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
      iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
        Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
      ipureintro; exact ⟨Hen, Hlt, Hpure⟩
    · ipureintro; exact ⟨hD, hmd, hend⟩
  -- the loop closing the locks before `smaller` (all non-tail)
  have hsm1 : 0 < sint.Z sm' := by
    have : ¬ sint.Z sm' ≤ sint.Z (W64 0) := Hif
    rw [show sint.Z (W64 0) = 0 from rfl] at this; omega
  ihave IH2 : iprop(∃ (k : w64), "i" ∷ i_ptr ↦ k ∗ "w" ∷ w_ptr ↦ w ∗ "smaller" ∷ smaller_ptr ↦ sm' ∗
      "Hlocks" ∷ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      "Hls" ∷ locks ↦* lfs ∗ "Hlks" ∷ ([∗list] lf ∈ lfs.dropLast.drop (sint.nat k), walLockH lf) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z sm'⌝) $$ [i w smaller Hlocks Hls Hlks]
  · iexists W64 0
    simp only [named]
    iframe
    ipureintro; exact ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩
  wp_join (iprop(w_ptr ↦ w ∗ smaller_ptr ↦ sm' ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* lfs ∗ ([∗list] lf ∈ lfs.dropLast.drop (sint.nat sm'), walLockH lf)))
    at (App (App (App (Val doFor) _) _) _) with [IH2]
  · wp_for IH2
    obtain ⟨Hk0, Hksm⟩ := Hk
    wp_if_destruct
    · have hksm : sint.Z k < sint.Z sm' := Hif
      have hkl : sint.nat k < lfs.dropLast.length := by
        rw [List.length_dropLast]; word
      have hkl' : sint.nat k < lfs.length := by
        rw [List.length_dropLast] at hkl; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by rw [← hlen63]; word⟩)]
      obtain ⟨lf, hlf⟩ : ∃ lf, lfs.dropLast[sint.nat k]? = some lf := ⟨_, List.getElem?_eq_getElem hkl⟩
      have hlf' : lfs[sint.nat k]? = some lf := by
        rw [List.getElem?_dropLast] at hlf; split at hlf
        · exact hlf
        · simp at hlf
      have hdrop : lfs.dropLast.drop (sint.nat k) = lf :: lfs.dropLast.drop (sint.nat (k + W64 1)) := by
        rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
        rw [List.drop_eq_getElem_cons hkl]
        rw [List.getElem?_eq_getElem hkl] at hlf
        cases hlf; rfl
      wp_apply wp_load_slice_index locks (sint.Z k) lfs (DFrac.own 1) lf Hk0 $$ [Hls] as Hls
      · iframe; ipureintro; exact hlf'
      (try wp_auto)
      rw [hdrop]
      icases Hlks with ⟨Hlf, Hlks⟩
      iunfold walLockH at Hlf
      icases Hlf with ⟨%f1, %fd1, %nm1, %d1, #Hlf1, Hf1, Hfd1⟩
      ihave #Hlf2 := Hlf1
      iunfold fileutil.lockedFile at Hlf2
      ihave %hlfn := typedPointsto_not_null lf _ _ $$ Hlf2
      simp only [decide_eq_false hlfn]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by rw [← hlen63]; word⟩)]
      wp_apply wp_load_slice_index locks (sint.Z k) lfs (DFrac.own 1) lf Hk0 $$ [Hls] as Hls
      · iframe; ipureintro; exact hlf'
      (try wp_auto)
      iStructNamed Hlf2
      wp_method_call
      wp_call
      (try wp_auto)
      wp_apply wp_Close f1 fd1 nm1 d1 $$ [Hf1 Hfd1] as %err1 -
      · iframe; iexact Hosinv
      wp_for_post
      iframe
      iexists k + W64 1
      simp only [named]
      iframe
      ipureintro
      constructor <;> word
    · (try wp_auto)
      have hk : k = sm' := by
        have : ¬ sint.Z k < sint.Z sm' := Hif
        apply BitVec.eq_of_toInt_eq; change sint.Z k = sint.Z sm'; omega
      subst hk
      iframe
  iintro ⟨w, smaller, Hlocks, Hls, Hlks⟩
  wp_auto
  -- the reslice `w.locks[smaller:]`
  have hb : 0 ≤ sint.Z sm' ∧ sint.Z sm' ≤ sint.Z locks.len ∧ sint.Z locks.len ≤ sint.Z locks.cap :=
    ⟨by omega, by omega, Hcw.2⟩
  simp only [hb, _root_.and_self, ite_true]
  icases ownSlice_slice_with_cap sm' locks.len locks lfs ⟨by omega, by omega, Int.le_refl _⟩
    $$ [Hls Hcap] with ⟨-, Hls, Hcap⟩
  · iframe
  have hsub : subslice (sint.nat sm') (sint.nat locks.len) lfs = lfs.drop (sint.nat sm') := by
    unfold subslice; rw [List.take_of_length_le (by rw [Hll.1]; exact Nat.le_refl _)]
  rw [hsub]
  have hsmn : sint.nat sm' < lfs.length := by word
  wp_auto
  wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
  (try wp_auto)
  iapply HΦ
  iframe HQ
  iapply (walOpenWF_iff P Mr w dir).2
  iexists h
  iframe Hr
  isplitl
  · iunfold walHandleIn
    iexists lg, df, sp, e, fp, lt, f, mds, slice.slice locks Loc sm' locks.len,
      lfs.drop (sint.nat sm'), fd, dfd, name, dnm, j, rc
    rw [dropLast_drop lfs (sint.nat sm')]
    iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
      Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
    ipureintro; exact ⟨Hen, by rw [getLast?_drop lfs _ hsmn]; exact Hlt, Hpure⟩
  · ipureintro; exact ⟨hD, hmd, hend⟩

end proof

end EtcdGrove
end Perennial
