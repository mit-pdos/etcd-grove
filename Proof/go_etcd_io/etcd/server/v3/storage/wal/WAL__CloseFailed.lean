/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__CloseFailed.lean` (unit `closefailed`):
`Close` of the handle a failed `ReadAll` leaves (`walReadFailedF`, `ReadDefs.lean`). The pipeline's `Close`
(its quarter of the call permission and its leftover name back, `pipeLeft`); `w.sync()` of the tail: put back
(`walFailIdle`: `WAL.sync.specIdleF`, an idle fdatasync whose failure changes nothing) or lent (`walFailLent`:
`WAL.sync.specLent`/`specLentE`, which unregister it on success). Then, but on a lent tail's failed sync, the
put-back at the next step (`walInv_unpin`: the segments' halves, the directory claim's half and the pipeline
names back to the parked state, the lock token from the ghost handle, `walReadFailed_lockedTok`) and, on
success, the loop closing every lock's file (a failed close logged) and the directory's `Close`
(`os.File.Close.wp_dirS`). On a lent tail's failed sync `Close` returns before any lock: what the handle held
of the directory goes back to the caller (`walCloseLeft`: a path to `dir`, `walInv_dirPath`; the claim's half
with the layout facts `ReadAll` read; the tail's lock, `fdLocksW_held`; the call permission's half).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncIdleF
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncLent
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncLentE
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__Close
public import Spec.os.File__Close
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Proof.os.NsS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllFail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseOpeningFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLaw
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.NameClaims
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

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.wp_failed
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] (Mr : WalMarshal)
    (wp_syncIdleF : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specIdleF (W := W) Mr)
    (wp_syncLent : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specLent (W := W) Mr)
    (wp_syncLentE : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specLentE (W := W) Mr)
    (wp_fpClose : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Close.spec (GF := GF) (hG := hG))
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_LError : zap.Logger.Error.spec (GF := GF) (hG := hG)) :
      ∀ (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString),
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
          WalFs.walAreaOk walCodec Mr R jr r ∗ walReadFailedF Mr w dir }}
        (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!! go!"Close"))
          (Val #()))
      {{ (err : GoInterface), RET #err;
          (WalFs.walUnlockedTok ∗ osCallPerm (callKey R dir) (1 : Qp).half) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ WalFs.walCloseLeft dir) }} := by
  intro R jr r w dir
  wp_start as ⟨#Harea, Hrf⟩
  icases walReadFailedF_elim Mr w dir $$ Hrf with ⟨Hfail, %lg, %locks, %ls, %lt, %fp, %j, %X, %hj, %gs0, %gL,
    %fls, %df, %dfd, %ph, Hcm, Ht⟩
  unfold walFailCommon
  icases Hcm with ⟨Hlg, #Hzap, Hdir, Hlocks, Hls, Hfp, Hpipe, Hns, #Hmu, #Henv, Hdff, Hdf, Hdfs, Hph, Hn, Hout,
    Hnf, #Hk, %hp, Hsegs, Hfiles, #Hlks⟩
  obtain ⟨hlsl, hlastN, hiL, hXt, hsz0⟩ := hp
  ihave #Harea2 := Harea
  iunfold WalFs.walAreaOk at Harea2
  icases Harea2 with ⟨#Hinv, #Hosinv, #Hsi, -⟩
  icases walInv_roots _ _ _ _ _ $$ Hinv with %hWR
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Henv0 := Henv
  iunfold encEnv at Henv0
  icases Henv0 with ⟨-, -, #Hsync, -, -⟩
  -- the lock token, out of the ghost handle
  ihave Hl := walReadFailed_lockedTok w dir $$ Hfail
  unfold walLockedTok
  icases Hl with ⟨Hlt, Hpf, Hcf⟩
  ihave #HltL := (BigSepL.bigSepL_snoc (PROP := IProp GF)).1 $$ Hlks
  icases HltL with ⟨-, #HltL⟩
  have hll : (ls ++ [lt]).length = (gs0 ++ [gL]).length := by simp [hlsl]
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync] as ⟨Hlocked, -⟩
  (try wp_auto)
  -- the pipeline's `Close`
  iunfold walPipeH at Hpipe
  icases Hpipe with ⟨%γp, %Rp, %dqp, %szp, %np, #Hisfp, Hmain, Hpc, %hnp, %hfpn, %hRpW⟩
  simp only [decide_eq_false hfpn]
  (try wp_auto)
  wp_apply wp_fpClose fp γp Rp dir dqp j szp $$ [Hmain] as %perr Hleft
  · iframe Hisfp; ileft; iexists np; iexact Hmain
  subst hRpW
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
  icases Ht with (Ht | Ht)
  · -- the tail put back: an idle fdatasync
    unfold walFailIdle
    icases Ht with ⟨Htf, %gT, %fdt, %d, %e, HsT, Hft, Hfdt, Hlkt, %hgT, He, Henc⟩
    obtain ⟨hgTi, hgTs, hd⟩ := hgT
    iunfold segRes at HsT
    icases HsT with ⟨Hm, Hb⟩
    rw [hgTi, ← hd]
    wp_apply (wp_syncIdleF R jr r w lg locks ls lt (fls.getD gs0.length null) fdt (child dir gL.name)
        dir j X hj gL.name d gT.om gT.bs e hlastN (by rw [hd]; exact hiL) hgTs.symm)
        $$ [He Henc Hns Hlg Hlocks Hls Hft Hfdt Hn Htf Hcf Hm Hb]
        as %err ⟨He, Henc, Hns, Hlg, Hlocks, Hls, Hft, Hfdt, -, Hn, Htf, Hcf, Hsy⟩
    · iframe; iframe #
    ihave Hsy := syncOut_segF { gT with ino := d.ino } hgTs.symm (err = GoInterface.nil) $$ Hsy
    icases Hsy with ⟨%g', %hg', HsT⟩
    ihave Hres : iprop((walTailsFrag (W := W) ∅ ∗ ∃ (fdt : w64) (d : OsFd) (g : SegG),
          os.ownFile (fls.getD gs0.length null) fdt (child dir gL.name) (DFrac.own 1) ∗
          osFd fdt (DFrac.own 1) d ∗ fdLocks fdt d ∗ segRes g ∗
          ⌜d.ino = gL.ino ∧ g.ino = gL.ino ∧ g.om.size = g.bs.length⌝) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ ∃ (k : LockKind) (fdt : w64), osLock k gL.ino fdt ∗
          fileutil.lockKind k ∗
          ⌜∃ (segs : List SegG) (gLL : SegG), CloseLeftOk X hj segs gLL ∧ gLL.ino = gL.ino⌝))
        $$ [Htf Hft Hfdt Hlkt HsT]
    · ileft
      iframe Htf
      iexists fdt, d, g'
      iframe
      ipureintro; exact ⟨hd, hg'.1.trans hd, hg'.2⟩
    iclear Henc He
    -- after the sync: the put-back, or (a lent tail's failed sync) what the handle held of the directory
    iunfold pipeLeft at Hleft
    iunfold pipeRes at Hleft
    icases Hleft with ⟨⟨Hperm2, -⟩, %b, %hb, Htb⟩
    icases Hres with (⟨Htf, %fdt', %d', %g', Hft, Hfdt, Hlkt, HsT, %hg'⟩ | ⟨%he, %kk, %fdt', Hlk, #Hkk, %hcl⟩)
    rotate_left
    · -- returned before the locks
      rcases err with ei | _
      rotate_left
      · exact absurd rfl he
      wp_auto
      iapply (wp_notCrashed_acc _ _ rfl)
      iintro Hnc
      imod walInv_dirPath walCodec Mr R jr r dir j X $$ Hinv Hnc Hnf Hk with ⟨Hnc, Hnf, %qd, Hpd⟩
      imodintro
      iframe Hnc
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact he
      unfold walCloseLeft
      obtain ⟨segs, gLL, hcl, hgLL⟩ := hcl
      iexists R, j, X, hj, segs, gLL, qd, kk, fdt'
      rw [hgLL]
      iframe Hsi Hpd Hn Hlk Hkk
      isplitr
      · ipureintro; exact hcl
      isplitr
      · ipureintro; exact hWR.symm
      iapply walPerm_ofW hWR dir
      iapply osCallPerm_halves' _
      iframe
    ihave Htmps := tmpClaims_walTmpsRes (L := hG.goose_localGS) j b (pipeTmp (np + 1)) hb
      (pipeTmp_mem_walTmpsF _) $$ [Htb Hpc]
    · iframe
    iapply (wp_notCrashed_acc _ _ rfl)
    iintro Hnc
    imod walInv_unpin walCodec Mr R jr r dir j X hj (gs0 ++ [g']) true (by
        intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact hsz0 g hg
        · simp at hg; subst hg; exact hg'.2.2) $$ Hinv Hnc [Hlt Hpf Hcf] [Htf Hnf] [Hout]
        [Hsegs HsT] Hn [Htmps] Hk with ⟨Hnc, Hunl⟩
    · unfold walLockedTok; iframe
    · iframe
    · iapply walOutFrag_eq' (W := W) $$ Hout
      ipureintro
      simp [hg'.2.1]
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
      ileft
      iframe Hunl
      iapply walPerm_ofW hWR dir
      iapply osCallPerm_halves' _
      iframe
    | nil =>
      wp_auto
      -- the locks' files
      ihave HfL' : walFileAt (GF := GF) fls gs0.length $$ [Hft Hfdt Hlkt]
      · unfold walFileAt; iexists fdt', _, _; iframe
      ihave Hfiles := BigSepL.bigSepL_mono (PROP := IProp GF)
        (fun {k g} _ => walTieFile_at (GF := GF) dir true fls k g) $$ Hfiles
      ihave Hlh := walTie_locks (GF := GF) (gs0 ++ [gL]) (ls ++ [lt]) fls hll $$ [Hfiles HfL']
      · iframe Hlks
        iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
        iframe
      ihave %Hll2 := ownSlice_len _ _ _ $$ Hls
      (try wp_auto)
      ihave IH : iprop(∃ (k : w64) (lv : Loc),
          "i" ∷ i_ptr ↦ k ∗ "l" ∷ l_ptr ↦ lv ∗ "Hls" ∷ locks ↦* (ls ++ [lt]) ∗
          "Hlks" ∷ ([∗list] lf ∈ (ls ++ [lt]).drop (sint.nat k), walLockH lf (fun _ => True)) ∗
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
        · have Hif' : sint.Z k < sint.Z locks.len := by simpa [intoVal_eq_iff] using Hif
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
        · (try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif)
          simp [intoVal_eq_iff, Hif]
          (try wp_auto)
          iframe
      iintro ⟨w, Hlg⟩
      (try wp_auto)
      -- the directory's `Close`
      wp_apply os.File.Close.wp_dirS df dfd dir j ph $$ [Hdf Hdfs] as %err3 -
      · iframe Hdf Hdfs; iexact Hosinv
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
      (try wp_auto)
      iapply HΦ
      ileft
      iframe Hunl
      iapply walPerm_ofW hWR dir
      iapply osCallPerm_halves' _
      iframe
  · -- the tail lent: its fdatasync puts it back on success
    unfold walFailLent
    icases Ht with ⟨%γt, %H, %md, %cuts, %o0, %sz, %kt, %fdt, Htf, %hlp, He, Ht⟩
    obtain ⟨hwr, segs, gLL, hcl, hgLL⟩ := hlp
    icases Ht with (Htw | Htw)
    · wp_apply (wp_syncLent R jr r w lg locks ls lt (fls.getD gs0.length null) fdt (child dir gL.name) dir γt
          gL.ino H md cuts o0 sz kt hwr) $$ [He Hns Hlg Hlocks Hls Htf Hcf Htw]
          as %err ⟨He, Hns, Hlg, Hlocks, Hls, Hcf, Hr⟩
      · iframe; iframe #
      ihave Hres : iprop((walTailsFrag (W := W) ∅ ∗ ∃ (fdt : w64) (d : OsFd) (g : SegG),
            os.ownFile (fls.getD gs0.length null) fdt (child dir gL.name) (DFrac.own 1) ∗
            osFd fdt (DFrac.own 1) d ∗ fdLocks fdt d ∗ segRes g ∗
            ⌜d.ino = gL.ino ∧ g.ino = gL.ino ∧ g.om.size = g.bs.length⌝) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ ∃ (k : LockKind) (fdt : w64), osLock k gL.ino fdt ∗
            fileutil.lockKind k ∗
            ⌜∃ (segs : List SegG) (gLL : SegG), CloseLeftOk X hj segs gLL ∧ gLL.ino = gL.ino⌝))
          $$ [Hr]
      · icases Hr with (⟨-, Htf, Hft, ⟨%d, Hfdt, Hlkt, %hd⟩, %g, HsT, %hg⟩ | ⟨%he, -, Htw⟩)
        · ileft
          iframe Htf
          iexists fdt, d, g
          iframe
          ipureintro; exact ⟨hd, hg.1, hg.2⟩
        · iright
          isplitr
          · ipureintro; exact he
          unfold walTailP
          icases Htw with ⟨-, ⟨%rd, %lo, %lk, -, Hlkw⟩, -⟩
          icases fdLocksW_held fdt ⟨gL.ino, rd, true, lo, lk⟩ rfl $$ Hlkw with ⟨%kk, Hlk, #Hkk⟩
          iexists kk, fdt
          iframe Hlk Hkk
          ipureintro; exact ⟨segs, gLL, hcl, hgLL⟩
      -- after the sync: the put-back, or (a lent tail's failed sync) what the handle held of the directory
      iunfold pipeLeft at Hleft
      iunfold pipeRes at Hleft
      icases Hleft with ⟨⟨Hperm2, -⟩, %b, %hb, Htb⟩
      icases Hres with (⟨Htf, %fdt', %d', %g', Hft, Hfdt, Hlkt, HsT, %hg'⟩ | ⟨%he, %kk, %fdt', Hlk, #Hkk, %hcl⟩)
      rotate_left
      · -- returned before the locks
        rcases err with ei | _
        rotate_left
        · exact absurd rfl he
        wp_auto
        iapply (wp_notCrashed_acc _ _ rfl)
        iintro Hnc
        imod walInv_dirPath walCodec Mr R jr r dir j X $$ Hinv Hnc Hnf Hk with ⟨Hnc, Hnf, %qd, Hpd⟩
        imodintro
        iframe Hnc
        wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
        (try wp_auto)
        iapply HΦ
        iright
        isplitr
        · ipureintro; exact he
        unfold walCloseLeft
        obtain ⟨segs, gLL, hcl, hgLL⟩ := hcl
        iexists R, j, X, hj, segs, gLL, qd, kk, fdt'
        rw [hgLL]
        iframe Hsi Hpd Hn Hlk Hkk
        isplitr
        · ipureintro; exact hcl
        isplitr
        · ipureintro; exact hWR.symm
        iapply walPerm_ofW hWR dir
        iapply osCallPerm_halves' _
        iframe
      ihave Htmps := tmpClaims_walTmpsRes (L := hG.goose_localGS) j b (pipeTmp (np + 1)) hb
        (pipeTmp_mem_walTmpsF _) $$ [Htb Hpc]
      · iframe
      iapply (wp_notCrashed_acc _ _ rfl)
      iintro Hnc
      imod walInv_unpin walCodec Mr R jr r dir j X hj (gs0 ++ [g']) true (by
          intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact hsz0 g hg
          · simp at hg; subst hg; exact hg'.2.2) $$ Hinv Hnc [Hlt Hpf Hcf] [Htf Hnf] [Hout]
          [Hsegs HsT] Hn [Htmps] Hk with ⟨Hnc, Hunl⟩
      · unfold walLockedTok; iframe
      · iframe
      · iapply walOutFrag_eq' (W := W) $$ Hout
        ipureintro
        simp [hg'.2.1]
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
        ileft
        iframe Hunl
        iapply walPerm_ofW hWR dir
        iapply osCallPerm_halves' _
        iframe
      | nil =>
        wp_auto
        -- the locks' files
        ihave HfL' : walFileAt (GF := GF) fls gs0.length $$ [Hft Hfdt Hlkt]
        · unfold walFileAt; iexists fdt', _, _; iframe
        ihave Hfiles := BigSepL.bigSepL_mono (PROP := IProp GF)
          (fun {k g} _ => walTieFile_at (GF := GF) dir true fls k g) $$ Hfiles
        ihave Hlh := walTie_locks (GF := GF) (gs0 ++ [gL]) (ls ++ [lt]) fls hll $$ [Hfiles HfL']
        · iframe Hlks
          iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
          iframe
        ihave %Hll2 := ownSlice_len _ _ _ $$ Hls
        (try wp_auto)
        ihave IH : iprop(∃ (k : w64) (lv : Loc),
            "i" ∷ i_ptr ↦ k ∗ "l" ∷ l_ptr ↦ lv ∗ "Hls" ∷ locks ↦* (ls ++ [lt]) ∗
            "Hlks" ∷ ([∗list] lf ∈ (ls ++ [lt]).drop (sint.nat k), walLockH lf (fun _ => True)) ∗
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
          · have Hif' : sint.Z k < sint.Z locks.len := by simpa [intoVal_eq_iff] using Hif
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
          · (try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif)
            simp [intoVal_eq_iff, Hif]
            (try wp_auto)
            iframe
        iintro ⟨w, Hlg⟩
        (try wp_auto)
        -- the directory's `Close`
        wp_apply os.File.Close.wp_dirS df dfd dir j ph $$ [Hdf Hdfs] as %err3 -
        · iframe Hdf Hdfs; iexact Hosinv
        (try wp_auto)
        wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
        (try wp_auto)
        iapply HΦ
        ileft
        iframe Hunl
        iapply walPerm_ofW hWR dir
        iapply osCallPerm_halves' _
        iframe
    · wp_apply (wp_syncLentE R jr r w lg locks ls lt (fls.getD gs0.length null) fdt (child dir gL.name) dir γt
          gL.ino H md cuts o0 sz kt hwr) $$ [He Hns Hlg Hlocks Hls Htf Hcf Htw]
          as %err ⟨He, Hns, Hlg, Hlocks, Hls, Hcf, Hr⟩
      · iframe; iframe #
      ihave Hres : iprop((walTailsFrag (W := W) ∅ ∗ ∃ (fdt : w64) (d : OsFd) (g : SegG),
            os.ownFile (fls.getD gs0.length null) fdt (child dir gL.name) (DFrac.own 1) ∗
            osFd fdt (DFrac.own 1) d ∗ fdLocks fdt d ∗ segRes g ∗
            ⌜d.ino = gL.ino ∧ g.ino = gL.ino ∧ g.om.size = g.bs.length⌝) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ ∃ (k : LockKind) (fdt : w64), osLock k gL.ino fdt ∗
            fileutil.lockKind k ∗
            ⌜∃ (segs : List SegG) (gLL : SegG), CloseLeftOk X hj segs gLL ∧ gLL.ino = gL.ino⌝))
          $$ [Hr]
      · icases Hr with (⟨-, Htf, Hft, ⟨%d, Hfdt, Hlkt, %hd⟩, %g, HsT, %hg⟩ | ⟨%he, -, Htw⟩)
        · ileft
          iframe Htf
          iexists fdt, d, g
          iframe
          ipureintro; exact ⟨hd, hg.1, hg.2⟩
        · iright
          isplitr
          · ipureintro; exact he
          unfold walTailPE
          icases Htw with ⟨-, ⟨%rd, %lo, %lk, -, Hlkw⟩, -⟩
          icases fdLocksW_held fdt ⟨gL.ino, rd, true, lo, lk⟩ rfl $$ Hlkw with ⟨%kk, Hlk, #Hkk⟩
          iexists kk, fdt
          iframe Hlk Hkk
          ipureintro; exact ⟨segs, gLL, hcl, hgLL⟩
      -- after the sync: the put-back, or (a lent tail's failed sync) what the handle held of the directory
      iunfold pipeLeft at Hleft
      iunfold pipeRes at Hleft
      icases Hleft with ⟨⟨Hperm2, -⟩, %b, %hb, Htb⟩
      icases Hres with (⟨Htf, %fdt', %d', %g', Hft, Hfdt, Hlkt, HsT, %hg'⟩ | ⟨%he, %kk, %fdt', Hlk, #Hkk, %hcl⟩)
      rotate_left
      · -- returned before the locks
        rcases err with ei | _
        rotate_left
        · exact absurd rfl he
        wp_auto
        iapply (wp_notCrashed_acc _ _ rfl)
        iintro Hnc
        imod walInv_dirPath walCodec Mr R jr r dir j X $$ Hinv Hnc Hnf Hk with ⟨Hnc, Hnf, %qd, Hpd⟩
        imodintro
        iframe Hnc
        wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
        (try wp_auto)
        iapply HΦ
        iright
        isplitr
        · ipureintro; exact he
        unfold walCloseLeft
        obtain ⟨segs, gLL, hcl, hgLL⟩ := hcl
        iexists R, j, X, hj, segs, gLL, qd, kk, fdt'
        rw [hgLL]
        iframe Hsi Hpd Hn Hlk Hkk
        isplitr
        · ipureintro; exact hcl
        isplitr
        · ipureintro; exact hWR.symm
        iapply walPerm_ofW hWR dir
        iapply osCallPerm_halves' _
        iframe
      ihave Htmps := tmpClaims_walTmpsRes (L := hG.goose_localGS) j b (pipeTmp (np + 1)) hb
        (pipeTmp_mem_walTmpsF _) $$ [Htb Hpc]
      · iframe
      iapply (wp_notCrashed_acc _ _ rfl)
      iintro Hnc
      imod walInv_unpin walCodec Mr R jr r dir j X hj (gs0 ++ [g']) true (by
          intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact hsz0 g hg
          · simp at hg; subst hg; exact hg'.2.2) $$ Hinv Hnc [Hlt Hpf Hcf] [Htf Hnf] [Hout]
          [Hsegs HsT] Hn [Htmps] Hk with ⟨Hnc, Hunl⟩
      · unfold walLockedTok; iframe
      · iframe
      · iapply walOutFrag_eq' (W := W) $$ Hout
        ipureintro
        simp [hg'.2.1]
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
        ileft
        iframe Hunl
        iapply walPerm_ofW hWR dir
        iapply osCallPerm_halves' _
        iframe
      | nil =>
        wp_auto
        -- the locks' files
        ihave HfL' : walFileAt (GF := GF) fls gs0.length $$ [Hft Hfdt Hlkt]
        · unfold walFileAt; iexists fdt', _, _; iframe
        ihave Hfiles := BigSepL.bigSepL_mono (PROP := IProp GF)
          (fun {k g} _ => walTieFile_at (GF := GF) dir true fls k g) $$ Hfiles
        ihave Hlh := walTie_locks (GF := GF) (gs0 ++ [gL]) (ls ++ [lt]) fls hll $$ [Hfiles HfL']
        · iframe Hlks
          iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
          iframe
        ihave %Hll2 := ownSlice_len _ _ _ $$ Hls
        (try wp_auto)
        ihave IH : iprop(∃ (k : w64) (lv : Loc),
            "i" ∷ i_ptr ↦ k ∗ "l" ∷ l_ptr ↦ lv ∗ "Hls" ∷ locks ↦* (ls ++ [lt]) ∗
            "Hlks" ∷ ([∗list] lf ∈ (ls ++ [lt]).drop (sint.nat k), walLockH lf (fun _ => True)) ∗
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
          · have Hif' : sint.Z k < sint.Z locks.len := by simpa [intoVal_eq_iff] using Hif
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
          · (try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif)
            simp [intoVal_eq_iff, Hif]
            (try wp_auto)
            iframe
        iintro ⟨w, Hlg⟩
        (try wp_auto)
        -- the directory's `Close`
        wp_apply os.File.Close.wp_dirS df dfd dir j ph $$ [Hdf Hdfs] as %err3 -
        · iframe Hdf Hdfs; iexact Hosinv
        (try wp_auto)
        wp_apply sync.Mutex.wp_Unlock _ (BI.pure True : IProp GF) $$ [$Hmu $Hsync $Hlocked]
        (try wp_auto)
        iapply HΦ
        ileft
        iframe Hunl
        iapply walPerm_ofW hWR dir
        iapply osCallPerm_halves' _
        iframe

end proof

end EtcdGrove
end Perennial
