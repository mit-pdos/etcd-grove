/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/Open.lean` (W3/W5 of
`notes/wal-fsext-plan.md`, thirteenth session): `openAtIndex` in write mode (its spec), then
`fileutil.OpenDir(w.dir)` (`OpenDir.wp_proofOk`) over a path to the WAL directory (`walInv_dirPath`,
from the WAL's key and the lock's `walNamesFrag none` the handle holds, `walReadH_namesOut`; until
2026-11-14 the hypothesis `WalDirPathLaw`); on its error, `w.Close()` (`WAL.Close.spec` at the state `opening`,
proved: `WAL.Close.wp_opening`, `WAL__CloseOpening.lean`) and the error wrapped. Callee specs:
`openAtIndex.spec`, `WAL.Close.spec` at the state `opening`, `fmt.ErrorfErrs.spec`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Open
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openAtIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import Spec.fmt.ErrorfErrs
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDirOk
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtPin
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.NameLoans
import all Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]
variable [os.file.FieldAssumptions] [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- The WAL's key, held by a read handle (persistent). -/
theorem walReadH_key (write : Bool) (w : Loc) (dir : GoString) (s : w64 × w64) (i : Nat) :
    walReadH (W := W) write w dir s i ⊢
      walReadH (W := W) write w dir s i ∗ ∃ (j : Ino) (X : List GoString), walDirKey (W := W) dir i j X := by
  unfold walReadH walReadTie
  iintro ⟨Hin, %dec, %IoE, %eof, %ueof, %fs, %locks, %lfs, %fp, %rc, %j, %qs, Hd, Hdec, Hde, Htie, Hr⟩
  icases Htie with ⟨%X, %hj, %gs, %fls, Hn, Ho, Ht, #Hk, Hrest⟩
  isplitl [Hin Hd Hdec Hde Hn Ho Ht Hrest Hr]
  · iframe Hin
    iexists dec, IoE, eof, ueof, fs, locks, lfs, fp, rc, j, qs
    iframe Hd Hdec Hde Hr
    iexists X, hj, gs, fls
    iframe
    iexact Hk
  · iexists j, X; iexact Hk

/-- **The lock's registration token out of a read handle and back** (with its loans, and the WAL's key,
persistent): `walInv_dirPath`'s inputs. -/
theorem walReadH_namesOut (write : Bool) (w : Loc) (dir : GoString) (s : w64 × w64) (i : Nat) :
    walReadH (W := W) write w dir s i ⊢
      walOpenIn w dir s ∗
      ∃ Lo : List (GoString × Qp), walNamesFragS (W := W) ⟨none, none, Lo⟩ ∗
      (walOpenIn w dir s -∗ walNamesFragS (W := W) ⟨none, none, Lo⟩ -∗
        walReadH (W := W) write w dir s i) ∗
      ∃ (j : Ino) (X : List GoString), walDirKey (W := W) dir i j X := by
  unfold walReadH walReadTie
  iintro ⟨Hin, %dec, %IoE, %eof, %ueof, %fs, %locks, %lfs, %fp, %rc, %j, %qs, Hd, Hdec, Hde, Htie, Hr⟩
  icases Htie with ⟨%X, %hj, %gs, %fls, Hn, Ho, ⟨Ht, Hnf⟩, #Hk, Hrest⟩
  unfold walHLoans
  icases Hnf with ⟨%Lh, Hnf, %hLh⟩
  iframe Hin
  iexists Lh
  iframe Hnf
  isplitl [Hd Hdec Hde Hn Ho Ht Hrest Hr]
  · iintro Hin Hnf
    iframe Hin
    iexists dec, IoE, eof, ueof, fs, locks, lfs, fp, rc, j, qs
    iframe Hd Hdec Hde Hr
    iexists X, hj, gs, fls
    iframe
    isplitr
    · ipureintro; exact hLh
    iexact Hk
  · iexists j, X; iexact Hk

/-- A `fmtErrorOkOrNil` error is `errOk`. -/
theorem walOpenDir_errOk (e : GoInterfaceOk) :
    fmtErrorOkOrNil (GF := GF) (GoInterface.ok e) ⊢ errOk e := by
  exact errOk_of_fmtErrorOkOrNil e

theorem go_etcd_io.etcd.server.v3.storage.wal.Open.wp_proof (Mr : WalMarshal)
    (wp_open : go_etcd_io.etcd.server.v3.storage.wal.openAtIndex.spec (W := W) Mr)
    (wp_Close : go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.spec (W := W) (Sio := WalFs.ioNone) WalFs.walPbNone Mr)
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.Open.spec (W := W) Mr := by
  intro lg R jr r dir nm sp s qp Q ic hin hnmO hr hdl
  have hdl' : dir.length < 4096 := hdl.1
  wp_start as ⟨#Hzap, #Hok, Hp, Hres, Hperm, #Hsp, Hu, Hau⟩
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb0, %hrb1, -⟩
  have hrb := And.intro hrb0 hrb1
  icases osPathS_callKey R r _ jr $$ Hp with ⟨Hp, %hkc⟩
  have hdc : dir = child r nm := by rw [hin.2]; simp [child]; rfl
  have hkd : callKey R dir = callKey R r := by rw [hdc]; exact hkc nm
  icases walInv_roots _ _ _ _ _ $$ Hinv with %hWR
  rw [← hkd]
  try wp_auto
  wp_apply wp_open lg R jr r dir nm sp s true qp Q ic hin hnmO hr hdl $$ [Hp Hres Hperm Hu Hau]
    as %w %err ⟨Hp, Hres, %o, HQ, Hr⟩
  · (try rw [hkd]); iframe; iframe #
  (try rw [← hkd])
  icases Hr with (⟨%he, Hu, Hperm, %e, %hee, #He⟩ | ⟨%he, %ho, Hdf, Hop, Hrh, Hperm, Hcp⟩)
  · -- `openAtIndex` failed
    subst hee
    try wp_auto
    try wp_auto
    wp_apply wp_slice_literal (V := GoAny) [interface.ok e]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply wp_Errorf _ _ [interface.ok e] [e] ?wf $$ [Hasl] as %e1 #He1
    case wf => errargs_wf
    · iframe
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
      iexact He
    try wp_auto
    iapply HΦ
    iframe Hp Hres
    iexists o
    iframe HQ
    ileft
    isplitr
    · ipureintro; nofun
    iframe
  · subst he
    try wp_auto
    icases walReadH_namesOut true w dir s ic $$ Hrh with ⟨Hin, %Lo, Hnf, Hback, %j, %X, #Hkey⟩
    icases walOpening_incQ (W := W) w dir s ic $$ Hop with ⟨%IQ, HIQ, %hIQ, Hop⟩
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    rw [← hIQ] at *
    imod walInv_dirPath walCodec Mr R jr r dir IQ j X Lo $$ Hinv Hnc Hnf Hkey HIQ
      with ⟨Hnc, HIQ, %nmd, %qd, %hdn, Hnf, Hpd⟩
    ihave Hop := Hop $$ HIQ
    imodintro
    iframe Hnc
    unfold walOpenIn
    icases Hin with ⟨%lg', %sp', Hlg, #Hzap', Hdir, Hstart, #Hsp'⟩
    try wp_auto
    wp_apply go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.wp_proofOk dir R j (DFrac.own qd)
      (1 : Qp).half $$ [Hpd Hcp] as %f %err2 ⟨Hpd, Hcp, Hod⟩
    · iframe; iframe #
    -- the directory path's loan back (the handle keeps only the pipeline's)
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod walInv_dirPathRetDL walCodec Mr R jr r dir nmd qd j Lo hdn $$ Hinv Hnc Hnf Hpd with ⟨Hnc, Hnf⟩
    ihave Hrh := Hback $$ [Hlg Hdir Hstart] Hnf
    · iexists lg', sp'
      iframe
      iframe #
    imodintro
    iframe Hnc
    icases Hod with (⟨%fd, %he2, Hf, Hfd⟩ | ⟨⟨%he2, %hf⟩, #He2⟩)
    · -- success: the directory fd kept as `w.dirFile`
      subst he2
      try wp_auto
      iapply HΦ
      iframe Hp Hres
      iexists o
      iframe HQ
      iright
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact ho
      ihave Hperm := walPerm_toW hWR dir _ $$ Hperm
      unfold walOpeningF
      iframe Hop Hperm Hcp Hrh
      iexists f, fd, j, X
      iframe
      iframe #
    · -- `OpenDir` failed: `w.Close()`, the error wrapped
      subst hf
      obtain ⟨e2, rfl⟩ : ∃ e2, err2 = GoInterface.ok e2 := by
        cases err2 with
        | nil => exact absurd rfl he2
        | ok e2 => exact ⟨e2, rfl⟩
      try wp_auto
      try wp_auto
      wp_apply wp_Close R jr r w dir (.opening s) (fun _ => iprop(True)) $$ [Hop Hrh Hperm Hdf]
        as %ec ⟨Hu, Hperm⟩
      · dsimp only
        iframe Hop Hperm
        iframe #
        isplitr [Hdf]
        · iexact Hrh
        iexact Hdf
      try wp_auto
      wp_apply wp_slice_literal (V := GoAny) [interface.ok e2]
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      ihave #He2' := walOpenDir_errOk e2 $$ He2
      wp_apply wp_Errorf _ _ [interface.ok e2] [e2] ?wf $$ [Hasl] as %e1 #He1
      case wf => errargs_wf
      · iframe
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
        iexact He2'
      try wp_auto
      ihave Hperm := osCallPerm_halfJoin _ 1 $$ Hperm Hcp
      iapply HΦ
      iframe Hp Hres
      iexists o
      iframe HQ
      ileft
      isplitr
      · ipureintro; nofun
      iframe

end proof

end EtcdGrove
end Perennial
