/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__Close.lean` (W10 of `notes/wal-fsext-plan.md`):
one proof since wal-link L1a (2026-11-17, `notes/wal-link-scope.md` §8), by cases on the handle's state, each
state's proof a lemma: `failed` (`WAL__CloseFailed.lean`), `opening` (`WAL__CloseOpening.lean`), `unnamed`
(`WAL__CloseU.lean`), and `shared` here (the former `wp_proof` and `wp_proofNoErr` merged): after the lock the
whole share gives the handle (`walOpenWS_acquire`, `walHdl_open`); the pipeline's `Close` (its half of the call
permission and its leftover name back, `pipeLeft`), `w.sync()` of the tail over the handle without its
pipeline (`WAL.sync.specC`, or `specCNoErr` when `Sio` covers every inode: `walCov_syncC`), the loop closing
every lock's file (the non-tail locks' `walLockH`, then the tail's file, `walTailW`'s; a failed close is
logged), the invariant's put-back at the next step (`walCloseLaw`, `CloseLaw.lean`; the update committed, the
halves parked, the lock token back), the directory's `Close` (`os.File.Close.wp_dirS`, or `wp_dirSNE` when
covered); before the unlock the whole share is spent (`walOpenWS_finish`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncC
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CalleeCov
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.WAL__CloseFailed
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.WAL__CloseOpening
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.WAL__CloseU
public import Proof.os.CloseNE
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__Close
public import Spec.os.File__Close
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Proof.os.NsS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLaw
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.WAL__sync
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReleaseAu
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
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

theorem osCallPerm_join' (k : GoString) :
    osCallPerm (L := hG.goose_localGS) k (1 : Qp).half.half ∗
      osCallPerm (L := hG.goose_localGS) k (1 : Qp).half.half ⊢
      osCallPerm (L := hG.goose_localGS) k (1 : Qp).half := by
  have h := osCallPerm_split (L := hG.goose_localGS) k (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at h
  exact h.2

theorem pipeTmp_mem (n : Nat) : pipeTmp n ∈ walTmps := by
  unfold pipeTmp walTmps; split <;> simp

/-- **`Close` of the whole share** (see the file header). -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.wp_shared
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_syncC : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specC (W := W) P Mr)
    (wp_syncCNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specCNoErr (Sio := Sio) (W := W) P Mr)
    (wp_fpClose : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Close.spec (GF := GF) (hG := hG))
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_LError : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (γ : WalShN) (Q : WalDur → IProp GF) :
  {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWS Sio P Mr w dir γ 1 ∗ WalFs.walPurgeW w dir ∗
      AU <{ ∃∃ d : WalDur, WalFs.walDiskAt dir d }> @ walAuMask, ∅
        <{ WalFs.walDiskAt dir d, COMM Q d }> }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close"))
      (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜walCov Sio → err = GoInterface.nil⌝ ∗ ∃ d : WalDur, Q d ∗
          WalFs.walSyncedLb dir d.H.length ∗ WalFs.walUnlockedTok ∗ osCallPerm (callKey R dir) (1 : Qp).half) ∨
        ⌜err ≠ GoInterface.nil ∧ ¬ walCov Sio⌝ }} := by
  wp_start as ⟨#Harea, Hw, Hpw, Hau⟩
  icases walOpenWS_pers Sio P Mr w dir γ 1 $$ Hw with ⟨Hw, #Hpers⟩
  icases walShPers_facts Sio P Mr w dir γ $$ Hpers with ⟨#Hmu, #Hsync, -⟩
  ihave #Harea2 := Harea
  iunfold WalFs.walAreaOk at Harea2
  icases Harea2 with ⟨#Hinv, #Hosinv, -⟩
  icases walInv_roots _ _ _ _ _ $$ Hinv with %hWR
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (lc := 1) sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  iapply fupd_wp
  imod walOpenWS_acquire Sio P Mr w dir γ 1 $$ [Hw Hlocked Hlc1] with ⟨-, Hheld, Hh⟩
  · iframe Hw Hlocked Hlc1
  imodintro
  icases walHdl_open Sio P Mr w dir $$ Hh with ⟨%h, Hh, %hD, %hmd, Hr, %hroom⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu', Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk,
    Hopen, %Hpure⟩
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  -- the pipeline's `Close`
  iunfold walPipeH at Hpipe
  icases Hpipe with ⟨%γp, %Rp, %dqp, %szp, %np, #Hisfp, Hmain, Hpc, %hnp, %hfpn, %hRpW⟩
  simp only [decide_eq_false hfpn]
  (try wp_auto)
  wp_apply wp_fpClose fp γp Rp dir dqp j szp $$ [Hmain] as %perr Hleft
  · iframe Hisfp; ileft; iexists np; iexact Hmain
  (try wp_auto)
  -- `w.tail() != nil`, then `w.sync()`
  obtain ⟨ls, rfl⟩ := List.getLast?_eq_some_iff.1 Hlt
  wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
  · iframe
  ihave #Hlt0 := Hltf
  iunfold fileutil.lockedFile at Hlt0
  ihave %hltn := typedPointsto_not_null lt _ _ $$ Hlt0
  simp only [decide_eq_false hltn]
  (try wp_auto)
  wp_apply (walCov_syncC P Mr wp_syncC wp_syncCNE R jr r w dir j h (fun _ _ _ => WalFs.walNamed (W := W) dir) none
      hD.1 (fun hc => by have := hroom hc; omega)) $$ [Hlg Hdir Hdf Hdff Hmd Hsp Hdec Hrc Hns Henti Hsnapi He
      Henc Htw Hdh Hlocks Hls Hcap Hlks Hfp Hopen] as %err Hpost
  · iframe Harea
    iunfold walHandleC
    iexists lg, df, sp, e, lt, f, mds, locks, ls ++ [lt], fd, dfd, name, dnm, rc
    iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
      Hlocks Hls Hcap Hlks Hltf Hfp Henv Hcrc Hwpk Hopen
    ipureintro; exact ⟨Hen, Hlt, Hpure⟩
  icases Hpost with (⟨%Herr, Hh, #Hsy⟩ | %Herr)
  rotate_left
  · -- the sync failed: returned before the locks, the whole share spent
    rcases err with ei | _
    rotate_left
    · exact absurd rfl Herr.1
    wp_auto
    iapply fupd_wp
    imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hlocked
    · iframe Hpers Hheld
    imodintro
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    iright; ipureintro; exact Herr
  subst Herr
  wp_auto
  have hwr := (WalHS.split_rest0 Hpure.1 hD.1).2
  iunfold walHandleC at Hh
  icases Hh with ⟨%lg2, %df2, %sp2, %e2, %lt2, %f2, %mds2, %locks2, %lfs2, %fd2, %dfd2, %name2, %dnm2,
    %rc2, Hlg, #Hzap2, Hdir, Hdf, Hdff, Hmd, #Hmds2, Hsp, #Hst2, Hdec, Hrc, Hns, #Hmu2, Henti, Hsnapi,
    He, %Hen2, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt2, -, #Hltf2, Hfp, #Henv2, #Hcrc2, #Hwpk2,
    Hopen, %Hpure2⟩
  unfold walTailW
  icases Htw with ⟨Hf2, ⟨%rd2, %lo2, %lk2, Hfd2, Hlkt2⟩, Hoff2, Hk2, %m2, %bs2, Hm2, Hb2, %hp2, Hv2⟩
  unfold walDirH walDirLks
  icases Hdh with ⟨%Rd, %qd, %X, %hj, %nm0, %ph, #Hdk, Hcl, Hpd, #Hsid, %hRdW, Hperm, Hdfd, #Hnamed, Hout,
    ⟨%γt, %bL, %lsI, Htf, HlksI, %hlkr⟩, Hnf, %hdh⟩
  subst hRdW hRpW
  ihave Hlks := walLocksHI_H _ _ $$ HlksI
  ihave Hlkt2 := fdLocksW_locks _ _ $$ Hlkt2
  ihave %Hll2 := ownSlice_len _ _ _ $$ Hls
  have hlen2 : 0 < lfs2.length := by
    obtain ⟨ls2, rfl⟩ := List.getLast?_eq_some_iff.1 Hlt2; simp
  -- the loop closing the locks' files
  (try wp_auto)
  ihave IH : iprop(∃ (k : w64) (lv : Loc),
      "i" ∷ i_ptr ↦ k ∗ "l" ∷ l_ptr ↦ lv ∗ "Hls" ∷ locks2 ↦* lfs2 ∗
      "Hlks" ∷ ([∗list] lf ∈ lfs2.dropLast.drop (sint.nat k), walLockH lf) ∗
      "Htf" ∷ (if decide (sint.nat k < lfs2.length) then
          os.ownFile f2 fd2 name2 (DFrac.own 1) ∗ osFd fd2 (DFrac.own 1) ⟨h.ino, rd2, true, lo2, lk2⟩ ∗
            fdLocks fd2 ⟨h.ino, rd2, true, lo2, lk2⟩ else emp) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ lfs2.length⌝) $$ [i l Hls Hlks Hf2 Hfd2 Hlkt2]
  · iexists W64 0, _
    simp only [named]
    iframe
    rw [show sint.nat (W64 0) = 0 from rfl, decide_eq_true hlen2]
    simp only [ite_true]
    iframe
    ipureintro; exact ⟨by decide, by simp⟩
  wp_join (iprop(w_ptr ↦ w ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg2))
    at (App (App (App (Val doFor) _) _) _) with [IH w Hlg]
  · wp_for IH
    obtain ⟨Hk0, Hkl⟩ := Hk
    wp_if_destruct
    · have hkl : sint.nat k < lfs2.length := by
        have : sint.Z k < sint.Z locks2.len := Hif
        rw [Hll2.1]; word
      have hkb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z locks2.len := ⟨Hk0, Hif⟩
      (try wp_auto)
      rw [ite_eq_left_of_eq_true _ _ (eq_true hkb)]
      obtain ⟨lf, hlf⟩ : ∃ lf, lfs2[sint.nat k]? = some lf := ⟨_, List.getElem?_eq_getElem hkl⟩
      wp_apply wp_load_slice_index locks2 (sint.Z k) lfs2 (DFrac.own 1) lf Hk0 $$ [Hls] as Hls
      · iframe; ipureintro; exact hlf
      (try wp_auto)
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by
        have : sint.nat k < sint.nat locks2.len := Hll2.1 ▸ hkl
        word
      by_cases hlast : sint.nat k + 1 < lfs2.length
      · -- a non-tail lock
        have hkd : sint.nat k < lfs2.dropLast.length := by rw [List.length_dropLast]; omega
        have hlfd : lfs2.dropLast[sint.nat k]? = some lf := by
          rw [List.getElem?_dropLast, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; exact hlf
        have hdrop : lfs2.dropLast.drop (sint.nat k) =
            lf :: lfs2.dropLast.drop (sint.nat (k + W64 1)) := by
          rw [hk1, List.drop_eq_getElem_cons hkd]
          rw [List.getElem?_eq_getElem hkd] at hlfd
          cases hlfd; rfl
        rw [hdrop]
        icases Hlks with ⟨Hlf, Hlks⟩
        iunfold walLockH at Hlf
        icases Hlf with ⟨%f1, %fd1, %nm1, %d1, #Hlf1, Hf1, Hfd1, Hlks1, -⟩
        ihave Hlt1 := fdLocks_toks fd1 d1 $$ Hlks1
        ihave #Hlf3 := Hlf1
        iunfold fileutil.lockedFile at Hlf3
        ihave %hlfn := typedPointsto_not_null lf _ _ $$ Hlf3
        simp only [decide_eq_false hlfn]
        (try wp_auto)
        iStructNamed Hlf3
        wp_method_call
        wp_call
        (try wp_auto)
        wp_apply wp_Close f1 fd1 nm1 d1 $$ [Hf1 Hfd1 Hlt1] as %err1 ⟨-, -, #Herr⟩
        · iframe; iexact Hosinv
        (try wp_auto)
        have hdk : decide (sint.nat (k + W64 1) < lfs2.length) = decide (sint.nat k < lfs2.length) := by
          rw [hk1, decide_eq_true hlast, decide_eq_true hkl]
        cases err1 with
        | nil =>
          wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, lf
          simp only [named]
          rw [hdk]
          iframe
          ipureintro
          constructor <;> word
        | ok ie =>
          wp_auto
          wp_apply wp_Error as %fl -
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          (try wp_auto)
          wp_apply wp_LError lg2 _ _ $$ []
          · iexact Hzap2
          (try wp_auto)
          wp_for_post
          iframe
          iexists k + W64 1, lf
          simp only [named]
          rw [hdk]
          iframe
          ipureintro
          constructor <;> word
      · -- the tail
        have hkl1 : sint.nat k + 1 = lfs2.length := by omega
        have hlt2 : lf = lt2 := by
          rw [List.getLast?_eq_getElem?, show lfs2.length - 1 = sint.nat k by omega, hlf] at Hlt2
          exact Option.some.inj Hlt2
        subst hlt2
        rw [decide_eq_true hkl]
        simp only [ite_true]
        icases Htf with ⟨Hf2, Hfd2, Hlks2⟩
        ihave Hlt2c := fdLocks_toks fd2 _ $$ Hlks2
        ihave #Hlt3 := Hltf2
        iunfold fileutil.lockedFile at Hlt3
        ihave %hlfn := typedPointsto_not_null lf _ _ $$ Hlt3
        simp only [decide_eq_false hlfn]
        (try wp_auto)
        iStructNamed Hlt3
        wp_method_call
        wp_call
        (try wp_auto)
        wp_apply wp_Close f2 fd2 name2 _ $$ [Hf2 Hfd2 Hlt2c] as %err1 ⟨-, -, #Herr⟩
        · iframe; iexact Hosinv
        (try wp_auto)
        have hdk : decide (sint.nat (k + W64 1) < lfs2.length) = false := by
          rw [hk1, hkl1]; simp
        have hdrop : lfs2.dropLast.drop (sint.nat (k + W64 1)) = [] := by
          rw [hk1, hkl1, List.drop_eq_nil_iff, List.length_dropLast]; omega
        cases err1 with
        | nil =>
          wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, lf
          simp only [named]
          rw [hdrop, hdk]
          simp only [Bool.false_eq_true, ite_false]
          iframe
          isplitr
          · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
          isplitr
          · iempintro
          ipureintro
          constructor <;> word
        | ok ie =>
          wp_auto
          wp_apply wp_Error as %fl -
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          (try wp_auto)
          wp_apply wp_LError lg2 _ _ $$ []
          · iexact Hzap2
          (try wp_auto)
          wp_for_post
          iframe
          iexists k + W64 1, lf
          simp only [named]
          rw [hdrop, hdk]
          simp only [Bool.false_eq_true, ite_false]
          iframe
          isplitr
          · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
          isplitr
          · iempintro
          ipureintro
          constructor <;> word
    · (try wp_auto)
      iframe
  iintro ⟨w, Hlg⟩
  (try wp_auto)
  -- the put-back, at the next step
  iunfold pipeLeft at Hleft
  iunfold pipeRes at Hleft
  icases Hleft with ⟨⟨Hperm2, -⟩, %b, %hb, Htb⟩
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walInv_lksDrop (L := hG.goose_localGS) (W := W) walCodec Mr R jr r _ _ $$ Hinv Hnc Htf with ⟨Hnc, Htf⟩
  imod walCloseLaw (L := hG.goose_localGS) (W := W) Mr R jr r w dir h.γ γt h.ino j X hj h.H h.md h.cuts (h.o0 + (h.out ++ h.pend).length) m2 bs2
    b (pipeTmp (np + 1)) Q hp2.2.1 hwr hb (pipeTmp_mem _) $$ Hinv Hnc Hk2 [Hv2] Hm2 Hb2 Hdk Hcl Htb Hpc
    Hout Htf Hnf Hopen Hpw Hsy Hau with ⟨Hnc, %d, HQ, #Hsd, Hunl⟩
  · unfold tailVar; iexact Hv2
  imodintro
  iframe Hnc
  -- the directory's `Close` (no error when covered)
  by_cases hc : walCov Sio
  · wp_apply os.File.Close.wp_dirSNE hc df2 dfd2 dnm2 j ph $$ [Hdff Hdfd]
    · iframe; iexact Hosinv
    iintro -
    (try wp_auto)
    iapply fupd_wp
    imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hlocked
    · iframe Hpers Hheld
    imodintro
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; intro; rfl
    iexists d
    iframe HQ Hsd Hunl
    iapply walPerm_ofW hWR dir
    iapply osCallPerm_join' _
    iframe
  · wp_apply os.File.Close.wp_dirS df2 dfd2 dnm2 j ph $$ [Hdff Hdfd] as %err3 -
    · iframe; iexact Hosinv
    (try wp_auto)
    iapply fupd_wp
    imod walOpenWS_finish Sio P Mr w dir γ $$ [Hheld] with Hlocked
    · iframe Hpers Hheld
    imodintro
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; intro h; exact absurd h hc
    iexists d
    iframe HQ Hsd Hunl
    iapply walPerm_ofW hWR dir
    iapply osCallPerm_join' _
    iframe

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.wp_proof
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_syncC : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specC (W := W) P Mr)
    (wp_syncCNE : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specCNoErr (Sio := Sio) (W := W) P Mr)
    (wp_syncIdleF : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specIdleF (W := W) Mr)
    (wp_syncLent : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specLent (W := W) Mr)
    (wp_syncLentE : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specLentE (W := W) Mr)
    (wp_syncIdle : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specIdle (W := W) Mr)
    (wp_fpClose : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Close.spec (GF := GF) (hG := hG))
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_CloseNil : os.File.Close.specNil (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_LError : zap.Logger.Error.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.spec (Sio := Sio) (W := W) P Mr := by
  intro R jr r w dir m Q
  cases m with
  | shared γ =>
    exact go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.wp_shared P Mr wp_syncC wp_syncCNE wp_fpClose
      wp_tail wp_Close wp_Error wp_LError R jr r w dir γ Q
  | failed =>
    iintro %Φ ⟨#Harea, Hpk, Hrf⟩ HΦ
    iapply (go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.wp_failed Mr wp_syncIdleF wp_syncLent
      wp_syncLentE wp_fpClose wp_tail wp_Close wp_Error wp_LError R jr r w dir) $$ [Hpk Hrf]
    · iframe Hpk Harea Hrf
    inext
    iintro %err H
    iapply HΦ
    iexact H
  | opening s =>
    iintro %Φ ⟨#Harea, Hpk, Hop, Hrh, Hperm, Hdf⟩ HΦ
    iapply (go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.wp_opening Mr wp_syncIdle wp_fpClose wp_tail
      wp_Close wp_CloseNil wp_Error wp_LError R jr r w dir s) $$ [Hpk Hop Hrh Hperm Hdf]
    · iframe Hpk Harea Hop Hrh Hperm Hdf
    inext
    iintro %err H
    iapply HΦ
    iexact H
  | unnamed Rp qp tf =>
    iintro %Φ ⟨#Harea, Hw, Hpw⟩ HΦ
    iapply (go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.wp_unnamed P Mr wp_syncC wp_fpClose wp_tail
      wp_Close wp_Error wp_LError R jr r w dir Rp qp tf) $$ [Hw Hpw]
    · iframe Harea Hw Hpw
    inext
    iintro %err H
    iapply HΦ
    iexact H

end proof

end EtcdGrove
end Perennial
