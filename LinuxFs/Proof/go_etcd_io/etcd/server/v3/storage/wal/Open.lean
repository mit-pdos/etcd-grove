/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/Open.lean` (W3/W5 of
`notes/wal-fsext-plan.md`, thirteenth session): `openAtIndex` in write mode (its spec), then
`fileutil.OpenDir(w.dir)` (`OpenDir.wp_proofOk`) over a path to the WAL directory (`WalDirPathLaw`, from
the WAL's key the handle holds); on its error, `w.Close()` (`WAL.Close.specOpening`, a hypothesis until
W10) and the error wrapped. Hypotheses: `openAtIndex.spec`, `WalDirPathLaw` (`wal-path13`'s law to
replace), `WAL.Close.specOpening`, `fmt.ErrorfErrs.spec`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.Open
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.openAtIndex
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__CloseOpening
public import LinuxFs.Spec.fmt.ErrorfErrs
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDirOk
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtPin
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs

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
theorem walReadH_key (write : Bool) (w : Loc) (dir : GoString) (s : w64 × w64) :
    walReadH (W := W) write w dir s ⊢
      walReadH (W := W) write w dir s ∗ ∃ (j : Ino) (X : List GoString), walDirKey (W := W) dir j X := by
  unfold walReadH walReadTie
  iintro ⟨Hin, %dec, %IoE, %eof, %ueof, %fs, %locks, %lfs, %fp, %rc, Hd, Hdec, Hde, Htie, Hr⟩
  icases Htie with ⟨%j, %X, %hj, %gs, %fls, Hn, Ho, Ht, #Hk, Hrest⟩
  isplitl [Hin Hd Hdec Hde Hn Ho Ht Hrest Hr]
  · iframe Hin
    iexists dec, IoE, eof, ueof, fs, locks, lfs, fp, rc
    iframe Hd Hdec Hde Hr
    iexists j, X, hj, gs, fls
    iframe
    iexact Hk
  · iexists j, X; iexact Hk

/-- A `fmtErrorOkOrNil` error is `errOk`. -/
theorem walOpenDir_errOk (e : GoInterfaceOk) :
    fmtErrorOkOrNil (GF := GF) (GoInterface.ok e) ⊢ errOk e := by
  unfold fmtErrorOkOrNil fmtErrorOk
  iintro ⟨-, H⟩
  unfold errOk
  rw [fmt.stringMethodSpec_unfold]
  iexact H

theorem go_etcd_io.etcd.server.v3.storage.wal.Open.wp_proof (Mr : WalMarshal)
    (wp_open : go_etcd_io.etcd.server.v3.storage.wal.openAtIndex.spec (W := W) Mr)
    (hpath : ∀ R jr r, WalDirPathLaw (L := hG.goose_localGS) (W := W) walCodec Mr R jr r)
    (wp_Close : go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.specOpening (W := W) Mr)
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.Open.spec (W := W) Mr := by
  intro lg R jr r dir nm sp s qp Q hin hnmO hr hdl
  wp_start as ⟨#Hzap, #Hok, Hp, Hres, Hperm, #Hsp, Hu, Hau⟩
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb⟩
  try wp_auto
  wp_apply wp_open lg R jr r dir nm sp s true qp Q hin hnmO hr hdl $$ [Hp Hres Hperm Hu Hau]
    as %w %err ⟨Hp, Hres, %o, HQ, Hr⟩
  · iframe; iframe #
  icases Hr with (⟨%he, Hu, Hperm, %e, %hee, #He⟩ | ⟨%he, %ho, Hdf, Hop, Hrh, Hperm⟩)
  · -- `openAtIndex` failed
    subst hee
    try wp_auto
    try wp_auto
    wp_apply wp_slice_literal (V := GoAny) [interface.ok e]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply wp_Errorf _ _ [interface.ok e] [e] (by
        intro ii hii
        right
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
        cases hii
        simp) $$ [Hasl] as %e1 #He1
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
    ihave ⟨Hrh, %j, %X, #Hkey⟩ := walReadH_key true w dir s $$ Hrh
    ihave Hrh' := Hrh
    unfold walReadH walOpenIn
    icases Hrh' with ⟨⟨%lg', %sp', Hlg, #Hzap', Hdir, Hstart, #Hsp'⟩, Hrest⟩
    try wp_auto
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod hpath R jr r dir j X qp $$ Hinv Hnc Hkey Hp with ⟨Hnc, Hp, %qd, Hpd⟩
    imodintro
    iframe Hnc
    wp_apply go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.wp_proofOk dir R j (DFrac.own qd)
      (1 : Qp).half $$ [Hpd Hperm] as %f %err2 ⟨Hpd, Hperm, Hod⟩
    · iframe; iframe #
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
      unfold walOpeningF
      iframe Hop Hperm
      isplitl [Hlg Hdir Hstart Hrest]
      · unfold walReadH walOpenIn
        iframe Hrest
        iexists lg', sp'
        iframe
        iframe #
      iexists f, fd, j
      iframe
    · -- `OpenDir` failed: `w.Close()`, the error wrapped
      subst hf
      obtain ⟨e2, rfl⟩ : ∃ e2, err2 = GoInterface.ok e2 := by
        cases err2 with
        | nil => exact absurd rfl he2
        | ok e2 => exact ⟨e2, rfl⟩
      try wp_auto
      try wp_auto
      wp_apply wp_Close R jr r w dir s $$ [Hop Hrest Hlg Hdir Hstart Hperm Hdf] as %ec ⟨Hu, Hperm⟩
      · iframe Hop Hperm
        iframe #
        isplitr [Hdf]
        · unfold walReadH walOpenIn
          iframe Hrest
          iexists lg', sp'
          iframe
          iframe #
        iexact Hdf
      try wp_auto
      wp_apply wp_slice_literal (V := GoAny) [interface.ok e2]
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      ihave #He2' := walOpenDir_errOk e2 $$ He2
      wp_apply wp_Errorf _ _ [interface.ok e2] [e2] (by
          intro ii hii
          right
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
          cases hii
          simp) $$ [Hasl] as %e1 #He1
      · iframe
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
        iexact He2'
      try wp_auto
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
