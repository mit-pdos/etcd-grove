/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__ReleaseLockTo.lean` (W9 of
`notes/wal-fsext-plan.md`): the update committed right after `w.mu.Lock()` (`walInv_unlAU`); the loop
over the locks reads each lock's file name (`walLockNamed`: `Name()`, `filepath.Base`,
`parseWALName`), stopping at the first index `≥ a`; the earlier locks but the last of them closed
(all non-tail locks, `walLockH`); the reslice `w.locks[smaller:]` keeps the tail last
(`ownSlice_slice_with_cap`). Over a share of the handle since wal-link L1a (2026-11-17, `notes/wal-link-scope.md`
§8): after the lock the share gives the handle (`walOpenWS_acquire`, `walHdl_open`), which goes back before
the unlock (`walOpenWS_release`, `walHdl_close`: the tail's stream untouched, its room kept). The former
`specNoErr`'s proof; the former `spec` is its corollary `specR` (`spec_R`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReleaseLockTo
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.parseWALName
public import Spec.path.filepath.Base
public import Spec.os.File__Close
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReleaseAu
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReleaseLocks
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReleaseTie
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutName
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleShared
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

/-- See the file header; no error: every lock's name is a segment's (`walLockNamed`), which
`parseWALName` accepts (`scanWalName_walFileName`). -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.wp_proof
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [_root_.Perennial.path.filepath.Assumptions]
    (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_Base : filepath.Base.spec (GF := GF) (hG := hG))
    (wp_parse : go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.spec (Sio := Sio) (W := W) P Mr := by
  intro R jr r w dir γ q a t i n cs Q
  wp_start as ⟨#Harea, Hw, #Hsy, Hau⟩
  icases walOpenWS_pers Sio P Mr w dir γ q $$ Hw with ⟨Hw, #Hpers⟩
  icases walShPers_facts Sio P Mr w dir γ $$ Hpers with ⟨#Hmu, #Hsync, -⟩
  ihave #Harea2 := Harea
  iunfold WalFs.walAreaOk at Harea2
  icases Harea2 with ⟨#Hinv, #Hosinv, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (lc := 1) sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  iapply fupd_wp
  imod walOpenWS_acquire Sio P Mr w dir γ q $$ [Hw Hlocked Hlc1] with ⟨-, Hheld, Hh⟩
  · iframe Hw Hlocked Hlc1
  imodintro
  icases walHdl_open Sio P Mr w dir γ.inc $$ Hh with ⟨%h, Hh, %hD, %hmd, Hr, %hroom, %hinc⟩
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu', Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, #Hbefore, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk,
    Hopen, %Hpure⟩
  ihave ⟨Htw, #Hfn⟩ := walTailW_named f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out
    TailMetaW $$ Htw
  -- the tail's key and record; the directory's claim, key and locks
  iunfold walTailW at Htw
  icases Htw with ⟨Hf, Hfdo, Hoff, Htk, %m, %bs, Hm, Hbs, %hmb, Hv⟩
  iunfold walDirH at Hdh
  icases Hdh with ⟨%Rd, %qd, %X, %hj, %nm0, %ph, #Hdk, Hcl, Hpd, #Hsid, #HRdW, Hperm, Hdfd, #Hnmd, Hout, Hdl,
    Hnf, %hdh⟩
  iunfold walDirLks at Hdl
  icases Hdl with ⟨%γt, %b, %lsI, Htf, HlksI, %hlkr⟩
  have hdh' := hdh
  obtain ⟨-, hnm0c, ⟨pd, hname⟩, -, -, ⟨sq0, ix0, hnm0, -⟩, -⟩ := hdh'
  ihave ⟨HlksI, #Hbase⟩ := walLocksHI_base _ _ $$ HlksI
  ihave %hlen := BigSepL2.bigSepL2_length $$ HlksI
  have hlfs : lfs = lfs.dropLast ++ [lt] := by
    obtain ⟨ls0, hls0⟩ := List.getLast?_eq_some_iff.1 Hlt
    rw [hls0, List.dropLast_concat]
  -- every lock's name (`nms`: the non-tail locks' then the tail's)
  ihave #Hbn : iprop([∗list] lf; bn ∈ lfs.dropLast ++ [lt]; lsI.map (·.1) ++ [nm0],
      walLockBase (GF := GF) lf bn) $$ []
  · iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
    iframe Hbase
    unfold walLockBase
    iexists f, pd
    rw [← hname]
    iframe Hltf Hfn
    ipureintro; exact ⟨pd, sq0, ix0, by rw [hname, hnm0]⟩
  rw [← hlfs]
  have hnms := LkRel_names hlkr hnm0c
  have hnl : (lsI.map (·.1) ++ [nm0]).length = lfs.length := by
    rw [hlfs]; simp [hlen]
  ihave %Hll := ownSlice_len _ _ _ $$ Hls
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  -- the commit, right after the lock, the locked range raised with `unl`
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  icases walOpenWI_incQ (W := W) w dir h.inc $$ Hopen with ⟨%IQ, HIQ, %hIQ, Hopen⟩
  imod walInv_releaseLks walCodec Mr R jr r dir a
    (fun d => (∃ al, d.H[i]? = some (WalOpG.snap ⟨cs, a, t⟩ al)) ∧ i < n) Q γ.inc h.inc IQ hIQ j X hj h.γ
    ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG) γt b hlkr.2.1
    $$ Hinv Hnc Hau Hdk HIQ Hcl Htk [Hv] Htf with ⟨Hnc, HQ, HIQ, Hcl, Htk, Hv, %b', Htf, %hb'⟩
  · unfold tailVar; iexact Hv
  ihave Hopen := Hopen $$ HIQ
  iunfold tailVar at Hv
  imodintro
  iframe Hnc
  (try wp_auto)
  have hlen0 : 0 < lfs.length := by rw [hlfs]; simp
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
      "i" ∷ i_ptr ↦ k ∗ "l" ∷ l_ptr ↦ lv ∗ "i2" ∷ i2_ptr ↦ iv ∗ "w" ∷ w_ptr ↦ w ∗ "Hls" ∷ locks ↦* lfs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ lfs.length ∧
        ∀ (k' : Nat) (bn : GoString) (sq ix : Nat), k' < sint.nat k →
          (lsI.map (·.1) ++ [nm0])[k']? = some bn → bn = walFileName sq ix →
          uint.nat (W64 ix) < uint.nat a⌝) $$ [i l i2 w Hls]
  · iexists W64 0, _, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, by simp, ?_⟩
    intro k' _ _ _ hk'; exfalso; have : sint.nat (W64 0) = 0 := rfl; omega
  wp_join (Q := fun v => iprop(∃ (sm : w64) (fnd : Bool) (err : GoInterface),
      «$res0_ptr» ↦ err ∗ smaller_ptr ↦ sm ∗ found_ptr ↦ fnd ∗ index_ptr ↦ a ∗ w_ptr ↦ w ∗ locks ↦* lfs ∗
      ⌜v = executeVal ∧ err = GoInterface.nil ∧
        ((fnd = false ∧ sm = W64 0 ∧ ∀ (k' : Nat) (bn : GoString) (sq ix : Nat), k' < lfs.length →
            (lsI.map (·.1) ++ [nm0])[k']? = some bn → bn = walFileName sq ix →
            uint.nat (W64 ix) < uint.nat a) ∨
          (fnd = true ∧ -1 ≤ sint.Z sm ∧ sint.Z sm + 2 ≤ (lfs.length : Int) ∧
            (0 ≤ sint.Z sm → ∀ (bn : GoString) (sq ix : Nat),
              (lsI.map (·.1) ++ [nm0])[sint.nat sm]? = some bn → bn = walFileName sq ix →
              uint.nat (W64 ix) < uint.nat a)))⌝))
    at (App (App (App (Val doFor) _) _) _) with [IH «$res0» smaller found index]
  · wp_for IH
    obtain ⟨Hk0, Hkl, Hkp⟩ := Hk
    wp_if_destruct
    · have hkl : sint.nat k < lfs.length := by
        have : sint.Z k < sint.Z locks.len := Hif
        rw [Hll.1]; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by have : sint.Z k < sint.Z locks.len := Hif; exact this⟩)]
      obtain ⟨lf, hlf⟩ : ∃ lf, lfs[sint.nat k]? = some lf := ⟨_, List.getElem?_eq_getElem hkl⟩
      obtain ⟨bn, hbn⟩ : ∃ bn, (lsI.map (·.1) ++ [nm0])[sint.nat k]? = some bn :=
        ⟨_, List.getElem?_eq_getElem (by rw [hnl]; exact hkl)⟩
      obtain ⟨ixk, nk, hbnk, -⟩ := hnms _ _ hbn
      wp_apply wp_load_slice_index locks (sint.Z k) lfs (DFrac.own 1) lf Hk0 $$ [Hls] as Hls
      · iframe; ipureintro; exact hlf
      (try wp_auto)
      ihave #Hlfn := (BigSepL2.bigSepL2_lookup (PROP := IProp GF) hlf hbn) $$ Hbn
      iunfold walLockBase at Hlfn
      icases Hlfn with ⟨%f1, %pd1, #Hlf1, #Hfn1, -⟩
      ihave #Hlf2 := Hlf1
      iunfold fileutil.lockedFile at Hlf2
      iStructNamed Hlf2
      wp_method_call
      wp_call
      (try wp_auto)
      wp_apply os.File.Name.wp_named f1 (child pd1 bn) $$ []
      · iexact Hfn1
      (try wp_auto)
      wp_apply wp_Base as %bn' %hbn'
      (try wp_auto)
      rw [hbnk, baseModel_child_walFileName] at hbn'
      subst hbn'
      wp_apply wp_parse as %sq' %ix' %perr %hpe
      obtain ⟨hs1, hsc1⟩ := scanWalName_walFileName (h.cuts.length - lsI.length + sint.nat k) ixk
      (try wp_auto)
      obtain ⟨rfl, rfl, rfl⟩ := hpe.1 _ _ hs1 hsc1
      wp_auto
      rw [show (null : Loc) = map.nil from rfl]
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        iapply wp_for_post_break
        iexists _, true, _
        iframe
        ipureintro
        refine ⟨rfl, rfl, Or.inr ⟨rfl, ?_, ?_, fun h0 bn2 sq2 ix2 hb2 he2 => ?_⟩⟩
        · word
        · have : sint.nat k < sint.nat locks.len := Hll.1 ▸ hkl
          word
        · exact Hkp _ bn2 sq2 ix2 (by word) hb2 he2
      · wp_for_post
        iframe
        iexists k + W64 1, lf, k
        simp only [named]
        iframe
        ipureintro
        have : sint.nat k < sint.nat locks.len := Hll.1 ▸ hkl
        refine ⟨by word, by rw [Hll.1]; word, fun k' bn2 sq2 ix2 hk' hb2 he2 => ?_⟩
        have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        rcases Nat.lt_or_ge k' (sint.nat k) with hlt | hge
        · exact Hkp k' bn2 sq2 ix2 hlt hb2 he2
        · have e : k' = sint.nat k := by omega
          subst e
          rw [hbn] at hb2; cases hb2
          have hi := (walFileName_inj (hbnk.symm.trans he2)).2
          have e2 : (W64 (ix2 : Int)) = W64 (ixk : Int) := by
            apply BitVec.eq_of_toNat_eq; simp; omega
          rw [e2]
          have : ¬ uint.Z a ≤ uint.Z (W64 (ixk : Int)) := Hif
          word
    · (try wp_auto)
      iexists _, _, _
      iframe
      ipureintro
      have hk : sint.nat k = lfs.length := by
        have : ¬ sint.Z k < sint.Z locks.len := Hif
        rw [Hll.1]; word
      exact ⟨trivial, rfl, Or.inl ⟨rfl, rfl, fun k' bn2 sq2 ix2 hk' hb2 he2 =>
        Hkp k' bn2 sq2 ix2 (by omega) hb2 he2⟩⟩
  iintro ⟨%sm, %fnd, %err, «$res0», smaller, found, index, w, Hls, %Hq⟩
  obtain ⟨rfl, rfl, Hsm⟩ := Hq
  wp_auto
  have hlen63 : (lfs.length : Int) = sint.Z locks.len := by
    rw [Hll.1]; word
  wp_join (iprop(∃ sm' : w64, smaller_ptr ↦ sm' ∗ w_ptr ↦ w ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      ⌜-1 ≤ sint.Z sm' ∧ sint.Z sm' + 1 ≤ (lfs.length : Int) ∧
        (0 ≤ sint.Z sm' → ∀ (bn : GoString) (sq ix : Nat),
          (lsI.map (·.1) ++ [nm0])[sint.nat sm']? = some bn → bn = walFileName sq ix →
          uint.nat (W64 ix) < uint.nat a)⌝)) at next with [smaller w Hlocks]
  · rcases Hsm with ⟨rfl, rfl, hall⟩ | ⟨rfl, h2, h3, h4⟩
    · wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro
      refine ⟨by word, by word, fun _ bn sq ix hb he => hall _ bn sq ix ?_ hb he⟩
      rw [Hll.1]; word
    · wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro
      exact ⟨h2, by omega, h4⟩
  iintro ⟨%sm', smaller, w, Hlocks, %Hsm'⟩
  obtain ⟨hsmA, hsmB, hsmC⟩ := Hsm'
  have hs0 := hlkr.2.1
  have hle0 : lsI.length ≤ h.cuts.length := hlkr.1
  wp_auto
  wp_if_destruct
  · -- nothing to release
    (try wp_auto)
    iapply fupd_wp
    imod walOpenWS_release Sio P Mr w dir γ q $$ [Hheld Hr Hlg Hdir Hdf Hdff Hmd Hsp Hdec Hrc Hns Henti
      Hsnapi He Henc Hlocks Hls Hcap Hfp Hpipe Hopen Hf Hfdo Hoff Htk Hm Hbs Hv Hcl Hpd Hperm Hdfd Hout Hnf
      Htf HlksI] with ⟨Hw, Hlocked⟩
    · iframe Hpers Hheld
      iapply walHdl_close Sio P Mr w dir h hD hmd hroom _ hinc
      iframe Hr
      iunfold walHandleIn
      iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
      iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc
        Hlocks Hls Hcap Hbefore Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
      isplitr
      · ipureintro; exact Hen
      isplitl [Hf Hfdo Hoff Htk Hm Hbs Hv]
      · iunfold walTailW
        iframe Hf Hfdo Hoff Htk
        iexists m, bs
        iframe Hm Hbs Hv
        ipureintro; exact hmb
      isplitl [Hcl Hpd Hperm Hdfd Hout Hnf Htf HlksI]
      · iunfold walDirH
        iexists Rd, qd, X, hj, nm0, ph
        iframe Hdk Hcl Hpd Hsid HRdW Hperm Hdfd Hnmd Hout Hnf
        isplitl [Htf HlksI]
        · iunfold walDirLks
          iexists γt, b', lsI
          iframe Htf HlksI
          ipureintro
          have := LkRel_release (m := 0) hlkr (Nat.zero_le _)
            (Nat.le_trans hlkr.2.2.2.2.2 hb'.1)
          simpa using this
        ipureintro; exact hdh
      ipureintro; exact ⟨Hlt, Hpure⟩
    imodintro
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    isplitr; · ipureintro; rfl
    iframe HQ Hw
  -- the kept lock `m`'s segment starts at or before the raised range
  have hsm1 : 0 < sint.Z sm' := by
    have : ¬ sint.Z sm' ≤ sint.Z (W64 0) := Hif
    rw [show sint.Z (W64 0) = 0 from rfl] at this; omega
  have hlf1 : lfs.length = lsI.length + 1 := by
    have : (lfs.dropLast ++ [lt]).length = lsI.length + 1 := by simp [hlen]
    rw [← hlfs] at this; exact this
  have hmL : sint.nat sm' ≤ lsI.length := by rw [hlf1] at hsmB; word
  have hkept : segStart h.cuts (h.cuts.length - lsI.length + sint.nat sm') ≤ b' := by
    obtain ⟨bn, hbn⟩ : ∃ bn, (lsI.map (·.1) ++ [nm0])[sint.nat sm']? = some bn :=
      ⟨_, List.getElem?_eq_getElem (by simp only [List.length_append, List.length_map, List.length_singleton]; omega)⟩
    obtain ⟨ix, nb, hbx, hlk⟩ := hnms _ _ hbn
    have hia := hsmC (by word) bn _ ix hbn hbx
    rw [hbx] at hlk
    exact hb'.2 _ ix nb (by omega) hlk hia
  have hrel := LkRel_release hlkr hmL hkept
  icases walLocksHI_split (sint.nat sm') _ _ $$ HlksI with ⟨Hcls, HlksI⟩
  ihave IH2 : iprop(∃ (k : w64), "i" ∷ i_ptr ↦ k ∗ "w" ∷ w_ptr ↦ w ∗ "smaller" ∷ smaller_ptr ↦ sm' ∗
      "Hlocks" ∷ structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      "Hls" ∷ locks ↦* lfs ∗
      "Hcls" ∷ ([∗list] lf ∈ (lfs.dropLast.take (sint.nat sm')).drop (sint.nat k), walLockH lf) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z sm'⌝) $$ [i w smaller Hlocks Hls Hcls]
  · iexists W64 0
    simp only [named]
    iframe
    ipureintro; exact ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩
  wp_join (iprop(w_ptr ↦ w ∗ smaller_ptr ↦ sm' ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* lfs))
    at (App (App (App (Val doFor) _) _) _) with [IH2]
  · wp_for IH2
    obtain ⟨Hk0, Hksm⟩ := Hk
    wp_if_destruct
    · have hksm : sint.Z k < sint.Z sm' := by simpa [intoVal_eq_iff] using Hif
      have htl : (lfs.dropLast.take (sint.nat sm')).length = sint.nat sm' := by
        rw [List.length_take, hlen]; omega
      have hkl : sint.nat k < (lfs.dropLast.take (sint.nat sm')).length := by rw [htl]; word
      have hkl' : sint.nat k < lfs.length := by rw [hlf1]; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by rw [← hlen63]; word⟩)]
      obtain ⟨lf, hlf⟩ : ∃ lf, (lfs.dropLast.take (sint.nat sm'))[sint.nat k]? = some lf :=
        ⟨_, List.getElem?_eq_getElem hkl⟩
      have hlf' : lfs[sint.nat k]? = some lf := by
        rw [List.getElem?_take, if_pos (by omega), List.getElem?_dropLast] at hlf
        split at hlf
        · exact hlf
        · simp at hlf
      have hdrop : (lfs.dropLast.take (sint.nat sm')).drop (sint.nat k) =
          lf :: (lfs.dropLast.take (sint.nat sm')).drop (sint.nat (k + W64 1)) := by
        rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
        rw [List.drop_eq_getElem_cons hkl]
        rw [List.getElem?_eq_getElem hkl] at hlf
        cases hlf; rfl
      wp_apply wp_load_slice_index locks (sint.Z k) lfs (DFrac.own 1) lf Hk0 $$ [Hls] as Hls
      · iframe; ipureintro; exact hlf'
      (try wp_auto)
      rw [hdrop]
      icases Hcls with ⟨Hlf, Hcls⟩
      iunfold walLockH at Hlf
      icases Hlf with ⟨%f1, %fd1, %nm1, %d1, #Hlf1, Hf1, Hfd1, Hlks1, -⟩
      ihave Hlt1 := fdLocks_toks fd1 d1 $$ Hlks1
      ihave #Hlf2 := Hlf1
      iunfold fileutil.lockedFile at Hlf2
      ihave %hlfn := typedPointsto_not_null lf _ _ $$ Hlf2
      simp only [decide_eq_false hlfn]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by rw [← hlen63]; word⟩)]
      wp_apply wp_load_slice_index locks (sint.Z k) lfs (DFrac.own 1) lf Hk0 $$ [Hls] as Hls
      · iframe; ipureintro; exact hlf'
      (try wp_auto)
      rw [show (null : Loc) = map.nil from rfl]
      (try wp_auto)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hk0, by rw [← hlen63]; word⟩)]
      wp_apply wp_load_slice_index locks (sint.Z k) lfs (DFrac.own 1) lf Hk0 $$ [Hls] as Hls
      · iframe; ipureintro; exact hlf'
      (try wp_auto)
      iStructNamed Hlf2
      wp_method_call
      wp_call
      (try wp_auto)
      wp_apply wp_Close f1 fd1 nm1 d1 $$ [Hf1 Hfd1 Hlt1] as %err1 -
      · iframe; iexact Hosinv
      wp_for_post
      iframe
      iexists k + W64 1
      simp only [named]
      iframe
      ipureintro
      constructor <;> word
    · (try wp_auto)
      iframe
  iintro ⟨w, smaller, Hlocks, Hls⟩
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
  iapply fupd_wp
  imod walOpenWS_release Sio P Mr w dir γ q $$ [Hheld Hr Hlg Hdir Hdf Hdff Hmd Hsp Hdec Hrc Hns Henti
    Hsnapi He Henc Hlocks Hls Hcap Hfp Hpipe Hopen Hf Hfdo Hoff Htk Hm Hbs Hv Hcl Hpd Hperm Hdfd Hout Hnf
    Htf HlksI] with ⟨Hw, Hlocked⟩
  · iframe Hpers Hheld
    iapply walHdl_close Sio P Mr w dir h hD hmd hroom _ hinc
    iframe Hr
    iunfold walHandleIn
    iexists lg, df, sp, e, fp, lt, f, mds, slice.slice locks Loc sm' locks.len,
      lfs.drop (sint.nat sm'), fd, dfd, name, dnm, j, rc
    rw [dropLast_drop lfs (sint.nat sm')]
    iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc
      Hlocks Hls Hcap Hbefore Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
    isplitr
    · ipureintro; exact Hen
    isplitl [Hf Hfdo Hoff Htk Hm Hbs Hv]
    · iunfold walTailW
      iframe Hf Hfdo Hoff Htk
      iexists m, bs
      iframe Hm Hbs Hv
      ipureintro; exact hmb
    isplitl [Hcl Hpd Hperm Hdfd Hout Hnf Htf HlksI]
    · iunfold walDirH
      iexists Rd, qd, X, hj, nm0, ph
      iframe Hdk Hcl Hpd Hsid HRdW Hperm Hdfd Hnmd Hout Hnf
      isplitl [Htf HlksI]
      · iunfold walDirLks
        iexists γt, b', lsI.drop (sint.nat sm')
        iframe Htf HlksI
        ipureintro; exact hrel
      ipureintro; exact hdh
    ipureintro; exact ⟨by rw [getLast?_drop lfs _ hsmn]; exact Hlt, Hpure⟩
  imodintro
  wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
  (try wp_auto)
  iapply HΦ
  isplitr; · ipureintro; rfl
  iframe HQ Hw

/-- `ReleaseLockTo.specR` is `spec` with the result forgotten. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.spec_R (P : WalPbIn GF) (Mr : WalMarshal)
    (h : go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.spec (Sio := Sio) (W := W) P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.specR (Sio := Sio) (W := W) P Mr := by
  intro R jr r w dir γ q a t i n cs Q
  iintro %Φ Hpre HΦ
  iapply (h R jr r w dir γ q a t i n cs Q) $$ Hpre
  inext
  iintro %err ⟨-, Hw, HQ⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
