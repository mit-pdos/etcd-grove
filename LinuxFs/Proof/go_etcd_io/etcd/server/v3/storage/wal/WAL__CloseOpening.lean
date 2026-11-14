/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__CloseOpening.lean` (W10 of
`notes/wal-fsext-plan.md`; the W7-W12 log, eighth session): `Close` of `Open`'s handle before
`Open` set `dirFile`. The pipeline's `Close` (its half of the call permission and its leftover name
back, `pipeLeft`); the decoder's files out of it (`ownDecoder_streams`, `walTie_files`); `w.sync()`
with no encoder (`WAL.sync.specIdle`: the fdatasync of the idle tail, the file at the claim's last
`.wal` name); then, at the next step, the put-back (`walInv_unpin`: the segments' halves, the
directory claim's half and the pipeline names back to the parked state, the lock token from the
ghost handle, `walOpening_lockedTok`), whatever the sync answered; on success the loop closing every
lock's file (a failed close logged) and `Close` of the nil `dirFile` (`os.File.Close.specNil`).
Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__CloseOpening
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncIdle
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__Close
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Spec.os.File__CloseNil
public import LinuxFs.Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseOpeningFiles
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLaw
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtSteps
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecStreams
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
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]

theorem osCallPerm_halves :
    osCallPerm (L := hG.goose_localGS) (1 : Qp).half ∗ osCallPerm (L := hG.goose_localGS) (1 : Qp).half ⊢
      osCallPerm (L := hG.goose_localGS) 1 := by
  have h := osCallPerm_split (L := hG.goose_localGS) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.2

theorem pipeTmp_mem_walTmps (n : Nat) : pipeTmp n ∈ walTmps := by
  unfold pipeTmp walTmps; split <;> simp

/-- The synced or unsynced halves of the tail, as a segment of the same inode and size. -/
theorem syncOut_seg (g : SegG) (hlen : g.bs.length = g.om.size) (P : Prop) :
    ((⌜P⌝ ∗ osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om.synced ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) (g.bs.map (fun x => durB x.1))) ∨
      (⌜¬ P⌝ ∗ osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs)) ⊢
      ∃ g' : SegG, ⌜g'.ino = g.ino ∧ g'.om.size = g'.bs.length⌝ ∗ segRes (L := hG.goose_localGS) g' := by
  iintro (⟨-, Hm, Hb⟩ | ⟨-, Hm, Hb⟩)
  · iexists { g with om := g.om.synced, bs := g.bs.map (fun x => durB x.1) }
    unfold segRes
    iframe Hm Hb
    ipureintro
    exact ⟨rfl, by simp [OsMeta.synced, hlen]⟩
  · iexists g
    unfold segRes
    iframe Hm Hb
    ipureintro
    exact ⟨rfl, hlen.symm⟩

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.wp_proofOpening [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] (Mr : WalMarshal)
    (wp_syncIdle : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specIdle (W := W) Mr)
    (wp_fpClose : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Close.spec (GF := GF) (hG := hG))
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_CloseNil : os.File.Close.specNil (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_LError : zap.Logger.Error.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.specOpening (W := W) Mr := by
  intro R jr r w dir s
  wp_start as ⟨#Harea, Hop, Hrh, Hperm, Hdf⟩
  unfold walReadH walOpenIn walReadTie
  simp only [↓reduceIte]
  icases Hrh with ⟨⟨%lg, %sp, Hlg, #Hzap, Hdir, Hstart, #Hsp⟩, %dec, %IoE, %eof, %ueof, %fs, %locks,
    %lfs, %fp, %rc, %j, Hdecf, Hdec, #Hdenv, ⟨%X, %hj, %gs, %fls, Hn, Hout, ⟨Htf, Hnf⟩, #Hk, %Hgs,
    %Hfs, #Hlks⟩, Hlocks, Hls, Hcap, Hrc, Hfp, ⟨%hrc, Hpipe⟩, He, Hst, Hmd, Henti, Hsnapi, Hns,
    #Hmu, #Henv, #Hcrc⟩
  obtain ⟨hgs0, hnd, hsz, -, hlast, -⟩ := Hgs
  obtain ⟨hfl, hll, hfll, hfk⟩ := Hfs
  ihave #Harea2 := Harea
  iunfold WalFs.walAreaOk at Harea2
  icases Harea2 with ⟨#Hinv, #Hosinv, -⟩
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Henv0 := Henv
  iunfold encEnv at Henv0
  icases Henv0 with ⟨-, -, #Hsync, -, -⟩
  -- the lock token, out of the ghost handle
  ihave Hl := walOpening_lockedTok w dir s $$ Hop
  unfold walLockedTok
  icases Hl with ⟨Hlt, Hpf, Hcf⟩
  -- the files, out of the decoder
  ihave Hst0 := ownDecoder_streams dec IoE eof fs 0 0#32 true $$ Hdec
  icases walTie_files dir (walReadFlag true) gs fs fls hfl hfll (fun k F g h1 h2 =>
      let ⟨f, fd, h3, h4⟩ := (hfk k F g h1 h2).2.2; ⟨f, fd, h3, h4⟩) $$ Hst0 with ⟨Hsegs, Hfiles⟩
  obtain ⟨gs0, gL, rfl⟩ : ∃ gs0 gL, gs = gs0 ++ [gL] := by
    rcases List.eq_nil_or_concat gs with h | ⟨L, b, h⟩
    · exact absurd h hgs0
    · exact ⟨L, b, by simpa using h⟩
  obtain ⟨ls, lt, rfl⟩ : ∃ ls lt, lfs = ls ++ [lt] := by
    rcases List.eq_nil_or_concat lfs with h | ⟨L, b, h⟩
    · subst h; simp at hll
    · exact ⟨L, b, by simpa using h⟩
  have hlsl : ls.length = gs0.length := by simpa using hll
  icases (BigSepL.bigSepL_snoc (PROP := IProp GF)).1 $$ Hsegs with ⟨Hsegs, HsL⟩
  icases (BigSepL.bigSepL_snoc (PROP := IProp GF)).1 $$ Hfiles with ⟨Hfiles, HfL⟩
  ihave #HltL := (BigSepL.bigSepL_snoc (PROP := IProp GF)).1 $$ Hlks
  icases HltL with ⟨-, #HltL⟩
  -- the tail's facts
  have hkL : (gs0 ++ [gL])[gs0.length]? = some gL := by simp
  obtain ⟨FL, hFL⟩ : ∃ F, fs[gs0.length]? = some F :=
    ⟨_, List.getElem?_eq_getElem (by rw [hfl]; simp)⟩
  obtain ⟨-, hiL, -⟩ := hfk gs0.length FL gL hFL hkL
  have hbL : (walNames hj.cur).getLast? = some gL.name := (hlast trivial).1 gL (by simp)
  have hlenL : gL.bs.length = gL.om.size := (hsz gL (by simp)).symm
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  (try wp_auto)
  -- the pipeline's `Close`
  iunfold walPipeH at Hpipe
  icases Hpipe with ⟨%γp, %Rp, %dqp, %szp, %np, #Hisfp, Hmain, Hpc, %hnp, %hfpn⟩
  simp only [decide_eq_false hfpn]
  (try wp_auto)
  wp_apply wp_fpClose fp γp Rp dir dqp j szp $$ [Hmain] as %perr Hleft
  · iframe Hisfp; ileft; iexists np; iexact Hmain
  (try wp_auto)
  -- `w.tail() != nil`, then `w.sync()`
  wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
  · iframe
  rw [hlsl]
  ihave #Hlt0 := HltL
  iunfold fileutil.lockedFile at Hlt0
  ihave %hltn := typedPointsto_not_null lt _ _ $$ Hlt0
  simp only [decide_eq_false hltn]
  (try wp_auto)
  iunfold walTieFile at HfL
  icases HfL with ⟨%fdL, HfL, HfdL⟩
  wp_apply (wp_syncIdle R jr r w lg locks ls lt (fls.getD gs0.length null) fdL (child dir gL.name)
      dir j X hj gL.name (openFd gL.ino (walReadFlag true)) gL.om gL.bs hbL hiL hlenL)
      $$ [He Hns Hlg Hlocks Hls HfL HfdL Hn Htf Hcf HsL]
      as %err ⟨He, Hns, Hlg, Hlocks, Hls, HfL, HfdL, -, Hn, Htf, Hcf, Hsy⟩
  · iunfold segRes at HsL
    icases HsL with ⟨Hm, Hb⟩
    iframe
    iframe #
  -- the put-back, at the next step
  ihave Hsy := syncOut_seg gL hlenL (err = GoInterface.nil) $$ Hsy
  icases Hsy with ⟨%gL', %hgL', HsL⟩
  iunfold pipeLeft at Hleft
  iunfold pipeRes at Hleft
  icases Hleft with ⟨⟨Hperm2, -⟩, %b, %hb, Htb⟩
  ihave Htmps := tmpClaims_walTmpsRes (L := hG.goose_localGS) j b (pipeTmp (np + 1)) hb
    (pipeTmp_mem_walTmps _) $$ [Htb Hpc]
  · iframe
  iapply (wp_notCrashed_acc _ _ rfl)
  iintro Hnc
  imod walInv_unpin walCodec Mr R jr r dir j X hj (gs0 ++ [gL']) true (by
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hsz g (List.mem_append_left _ hg)
      · simp at hg; subst hg; exact hgL'.2) $$ Hinv Hnc [Hlt Hpf Hcf] [Htf Hnf] [Hout]
      [Hsegs HsL] Hn [Htmps] Hk with ⟨Hnc, Hunl⟩
  · unfold walLockedTok; iframe
  · iframe
  · iapply walOutFrag_eq' (W := W) $$ Hout
    ipureintro
    simp [hgL'.1]
  · iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
    iframe
  · simp only [↓reduceIte]; iexact Htmps
  imodintro
  iframe Hnc
  cases err with
  | ok ei =>
    -- the sync failed: returned before the locks
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
    (try wp_auto)
    iapply HΦ
    iframe Hunl
    iapply osCallPerm_halves
    iframe
  | nil =>
  wp_auto
  -- the locks' files
  ihave HfL' : walFileAt (GF := GF) fls gs0.length $$ [HfL HfdL]
  · unfold walFileAt; iexists fdL, _, _; iframe
  ihave Hfiles := BigSepL.bigSepL_mono (PROP := IProp GF)
    (fun {k g} _ => walTieFile_at (GF := GF) dir (walReadFlag true) fls k g) $$ Hfiles
  ihave Hlh := walTie_locks (GF := GF) (gs0 ++ [gL]) (ls ++ [lt]) fls hll $$ [Hfiles HfL']
  · iframe Hlks
    iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
    iframe
  ihave %Hll2 := ownSlice_len _ _ _ $$ Hls
  (try wp_auto)
  ihave IH : iprop(∃ (k : w64) (lv : Loc),
      "i" ∷ i_ptr ↦ k ∗ "l" ∷ l_ptr ↦ lv ∗ "Hls" ∷ locks ↦* (ls ++ [lt]) ∗
      "Hlks" ∷ ([∗list] lf ∈ (ls ++ [lt]).drop (sint.nat k), walLockH lf) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ (ls ++ [lt]).length⌝) $$ [i l Hls Hlh]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; exact ⟨by decide, by rw [show sint.nat (W64 0) = 0 from rfl]; omega⟩
  wp_join (iprop(w_ptr ↦ w ∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"lg" w ↦ lg))
    at (App (App (App (Val doFor) _) _) _) with [IH w Hlg]
  · wp_for IH
    obtain ⟨Hk0, Hkl⟩ := Hk
    wp_if_destruct
    · have Hif' : sint.Z k < sint.Z locks.len := by simpa using Hif
      have hkl : sint.nat k < (ls ++ [lt]).length := by
        rw [Hll2.1]; word
      have hkb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z locks.len := ⟨Hk0, Hif'⟩
      (try wp_auto)
      rw [ite_eq_left_of_eq_true _ _ (eq_true hkb)]
      obtain ⟨lf, hlf⟩ : ∃ lf, (ls ++ [lt])[sint.nat k]? = some lf :=
        ⟨_, List.getElem?_eq_getElem hkl⟩
      wp_apply wp_load_slice_index locks (sint.Z k) (ls ++ [lt]) (DFrac.own 1) lf Hk0 $$ [Hls] as Hls
      · iframe; ipureintro; exact hlf
      (try wp_auto)
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by
        have : sint.nat k < sint.nat locks.len := Hll2.1 ▸ hkl
        word
      have hdrop : (ls ++ [lt]).drop (sint.nat k) = lf :: (ls ++ [lt]).drop (sint.nat (k + W64 1)) := by
        rw [hk1, List.drop_eq_getElem_cons hkl]
        rw [List.getElem?_eq_getElem hkl] at hlf
        cases hlf; rfl
      rw [hdrop]
      icases Hlks with ⟨Hlf, Hlks⟩
      iunfold walLockH at Hlf
      icases Hlf with ⟨%f1, %fd1, %nm1, %d1, #Hlf1, Hf1, Hfd1⟩
      ihave #Hlf3 := Hlf1
      iunfold fileutil.lockedFile at Hlf3
      ihave %hlfn := typedPointsto_not_null lf _ _ $$ Hlf3
      simp only [decide_eq_false hlfn]
      (try wp_auto)
      iStructNamed Hlf3
      wp_method_call
      wp_call
      (try wp_auto)
      wp_apply wp_Close f1 fd1 nm1 d1 $$ [Hf1 Hfd1] as %err1 ⟨-, #Herr⟩
      · iframe; iexact Hosinv
      (try wp_auto)
      cases err1 with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, lf
        simp only [named]
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
        wp_apply wp_LError lg _ _ $$ []
        · iexact Hzap
        (try wp_auto)
        wp_for_post
        iframe
        iexists k + W64 1, lf
        simp only [named]
        iframe
        ipureintro
        constructor <;> word
    · simp
      (try wp_auto)
      iframe
  iintro ⟨w, Hlg⟩
  (try wp_auto)
  -- the nil directory's `Close`
  wp_apply wp_CloseNil as %err3 -
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
  (try wp_auto)
  iapply HΦ
  iframe Hunl
  iapply osCallPerm_halves
  iframe

end proof

end EtcdGrove
end Perennial
