/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__CloseU.lean` (W4 of
`notes/wal-fsext-plan.md`, twenty-fifth session): `WAL.Close.wp_proof` over the handle before naming
(`walOpenWFUI`, unsealed here: the proof never reads the naming fact), the put-back `walCloseLawU` (no
update), the sync's error arm keeping the lock token. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncC
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__Close
public import Spec.os.File__Close
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Proof.os.NsS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLawU
import all Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
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

theorem osCallPerm_joinU (k : GoString) :
    osCallPerm (L := hG.goose_localGS) k (1 : Qp).half.half ∗
      osCallPerm (L := hG.goose_localGS) k (1 : Qp).half.half ⊢
      osCallPerm (L := hG.goose_localGS) k (1 : Qp).half := by
  have h := osCallPerm_split (L := hG.goose_localGS) k (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at h
  exact h.2

theorem pipeTmp_memU (n : Nat) : pipeTmp n ∈ walTmps := by
  unfold pipeTmp walTmps; split <;> simp

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.wp_unnamed [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_syncC : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specC (W := W) P Mr)
    (wp_fpClose : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Close.spec (GF := GF) (hG := hG))
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_LError : zap.Logger.Error.spec (GF := GF) (hG := hG)) :
      ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString) (Rp : Roots) (qp : Qp) (tf : Loc) (i : Nat),
      {{ WalFs.walAreaOk walCodec Mr R jr r ∗ walOpenWFUI P Mr w dir Rp qp tf i ∗ WalFs.walPurgeW w dir }}
        (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close"))
          (Val #()))
      {{ (err : GoInterface), RET #err;
          (fmtErrorOkOrNil err ∗ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
            (∃ I, WalFs.walUnlockedTokXI I ∗ ⌜WalFs.incOf I dir = i⌝) ∗ WalFs.walNamesFrag (some dir) ∗ osCallPerm (callKey R dir) (1 : Qp).half ∗
            (∃ j : Ino, osPathS Rp dir (DFrac.own qp) j ∗ osPathS Rp dir (DFrac.own qp) j) ∗
            ∃ nmf : GoString, os.ownFile tf (-1 : w64) nmf (DFrac.own 1)) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ fmtErrorOk err ∗ (∃ I, WalFs.walLockedTokI I ∗ ⌜WalFs.incOf I dir = i⌝) ∗
            WalFs.walNamesFrag (some dir) ∗
            ∃ (fd : w64) (nmf : GoString) (d : OsFd),
              os.ownFile tf fd nmf (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d ∗ fdLocks fd d) }} := by
  intro R jr r w dir Rp qp tf i
  wp_start as ⟨#Harea, Hw, Hpw⟩
  unfold walOpenWFUI
  icases Hw with ⟨%h, Hh, %hD, %hmd, %hi, Hr⟩
  subst hi
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk,
    Hopen, %Hpure⟩
  ihave #Henv0 := Henv
  iunfold encEnv at Henv0
  icases Henv0 with ⟨-, -, #Hsync, -, -⟩
  ihave #Harea2 := Harea
  iunfold WalFs.walAreaOk at Harea2
  icases Harea2 with ⟨#Hinv, #Hosinv, -⟩
  icases walInv_roots _ _ _ _ _ $$ Hinv with %hWR
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  (try wp_auto)
  -- the pipeline's `Close`
  iunfold walPipeH at Hpipe
  icases Hpipe with ⟨%γp, %Rp', %dqp, %szp, %np, #Hisfp, Hmain, Hpc, %hnp, %hfpn, %hRpW⟩
  obtain ⟨-, ⟨hRp, rfl⟩, -⟩ := hnp
  subst Rp'
  subst hRp
  simp only [decide_eq_false hfpn]
  (try wp_auto)
  wp_apply wp_fpClose fp γp _ dir _ j szp $$ [Hmain] as %perr Hleft
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
  wp_apply (wp_syncC R jr r w dir j h (fun f R q => iprop(⌜f = tf ∧ R = W.roots ∧ q = qp⌝)) (some dir) hD.1) $$ [Hlg Hdir Hdf Hdff Hmd Hsp Hdec Hrc Hns Henti Hsnapi He
      Henc Htw Hdh Hlocks Hls Hcap Hlks Hfp Hopen] as %err Hpost
  · iframe Harea
    iunfold walHandleC
    iexists lg, df, sp, e, lt, f, mds, locks, ls ++ [lt], fd, dfd, name, dnm, rc
    iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
      Hlocks Hls Hcap Hlks Hltf Hfp Henv Hcrc Hwpk Hopen
    ipureintro; exact ⟨Hen, Hlt, Hpure⟩
  icases Hpost with (⟨%Herr, Hh, #Hsy⟩ | ⟨%Herr, #Hek, Hlk⟩)
  rotate_left
  · -- the sync failed: returned before the locks
    rcases err with ei | _
    rotate_left
    · exact absurd rfl Herr
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    icases Hlk with ⟨Hlk, ⟨%qs, Hnf⟩, %f', %fd', %nmf, %d', %R', %q', %hpin, Hf', Hfd', Hlks'⟩
    ihave Hnf := (walHLoans_some (W := W) dir dir qs).1 $$ Hnf
    obtain ⟨rfl, -, -⟩ := hpin
    iright; iframe Hlk Hnf Hek
    isplitr
    · ipureintro; exact Herr
    iexists fd', nmf, d'
    iframe Hf' Hfd' Hlks'
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
  icases Hdh with ⟨%Rd, %qd, %X, %hj, %nm0, %ph, #Hdk, Hcl, Hpd, #Hsid, %hRdW, Hperm, Hdfd, %hpin, Hout,
    ⟨%γt, %bL, %lsI, Htf, HlksI, %hlkr⟩, Hnf, %hdh⟩
  ihave Hnf := (walHLoans_some (W := W) dir dir _).1 $$ Hnf
  ihave Hlks := walLocksHI_H _ _ $$ HlksI
  ihave Hlkt2 := fdLocksW_locks _ _ $$ Hlkt2
  obtain ⟨rfl, rfl, rfl⟩ := hpin
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
            fdLocks fd2 ⟨h.ino, rd2, true, lo2, lk2⟩
        else os.ownFile f2 (-1 : w64) name2 (DFrac.own 1)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ lfs2.length⌝) $$ [i l Hls Hlks Hf2 Hfd2 Hlkt2]
  · iexists W64 0, _
    simp only [named]
    iframe
    rw [show sint.nat (W64 0) = 0 from rfl, decide_eq_true hlen2]
    simp only [ite_true]
    iframe
    ipureintro; exact ⟨by decide, by simp⟩
  wp_join (iprop(w_ptr ↦ w ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg2 ∗
      os.ownFile f2 (-1 : w64) name2 (DFrac.own 1)))
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
        wp_apply wp_Close f2 fd2 name2 _ $$ [Hf2 Hfd2 Hlt2c] as %err1 ⟨Hclf, -, #Herr⟩
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
          ipureintro
          constructor <;> word
    · (try wp_auto)
      have hkn : ¬ sint.nat k < lfs2.length := by
        intro hlt; apply Hif; rw [Hll2.1] at hlt; word
      rw [decide_eq_false hkn]
      simp only [Bool.false_eq_true, ite_false]
      iframe
  iintro ⟨w, Hlg, Hclf⟩
  (try wp_auto)
  -- the put-back, at the next step
  iunfold pipeLeft at Hleft
  iunfold pipeRes at Hleft
  icases Hleft with ⟨⟨Hperm2, Hpp, Hpkey⟩, %b, %hb, Htb⟩
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walInv_lksDrop (L := hG.goose_localGS) (W := W) walCodec Mr R jr r _ _ $$ Hinv Hnc Htf with ⟨Hnc, Htf⟩
  imod walCloseLawU (L := hG.goose_localGS) (W := W) Mr R jr r w dir h.γ γt h.ino j X hj h.H h.md h.cuts
    (h.o0 + (h.out ++ h.pend).length) m2 bs2 b (pipeTmp (np + 1)) hp2.2.1 hwr hb (pipeTmp_memU _)
    h.inc $$ Hinv Hnc Hk2 [Hv2] Hm2 Hb2 Hdk Hpkey Hcl Htb Hpc Hout Htf Hopen Hpw with ⟨Hnc, Hunl⟩
  · unfold tailVar; iexact Hv2
  imodintro
  iframe Hnc
  -- the directory's `Close`
  wp_apply os.File.Close.wp_dirS df2 dfd2 dnm2 j ph $$ [Hdff Hdfd] as %err3 #Hek3
  · iframe; iexact Hosinv
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
  (try wp_auto)
  iapply HΦ
  ileft
  iframe Hek3 Hunl Hdir Hnf
  isplitl [Hperm Hperm2]
  · iapply walPerm_ofW hWR dir
    iapply osCallPerm_joinU _
    iframe
  isplitl [Hpd Hpp]
  · iexists j
    iframe Hpd Hpp
  iexists name2
  iexact Hclf

end proof

end EtcdGrove
end Perennial
