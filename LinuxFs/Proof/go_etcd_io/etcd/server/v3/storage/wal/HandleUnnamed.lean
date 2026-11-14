/- Lean-first (no Rocq counterpart).

# The handle before naming (W4 of `notes/wal-fsext-plan.md`, twenty-second session)

`walOpenWFU` (`Handle.lean`) is `walOpenWF` with the naming fact `walNamed dir` left out
(`walDirH`'s `nmd := emp`): the WAL `Create` holds between its commit (the rename of `nm.tmp` onto
`nm`) and the parent directory's fsync. `renameWAL`'s two success arms converge on it (arm 1 through
`Create`'s assembly, arm 2 as the retry returns it), and the parent's fsync gives `walNamed dir`
(`walInv_named`), which seals it into `walOpenWF` (`walOpenWFU_named`). A named handle forgets its
naming (`walOpenWF_unnamed`: the retry's `ReadAll` names the WAL itself). `walOpenWFU_dirAcc` lends
the `dir` field (`Create` reads `w.dir` after `renameWAL`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The directory share's naming fact changed** along a wand. -/
theorem walDirH_nmd (dir : GoString) (j : Ino) (dfd : w64) (ino : Ino) (name : GoString) (k : Nat)
    (A B : IProp GF) :
    ⊢ (A -∗ B) -∗ walDirH (W := W) dir j dfd ino name k A -∗ walDirH (W := W) dir j dfd ino name k B := by
  iintro Hw Hd
  unfold walDirH
  icases Hd with ⟨%R, %q, %X, %hj, %nm0, %ph, Hk, Hn, Hp, Hsi, Hperm, Hdfd, Ha, Hrest⟩
  iexists R, q, X, hj, nm0, ph
  iframe Hk Hn Hp Hsi Hperm Hdfd Hrest
  iapply Hw $$ Ha

/-- **The handle's naming fact changed** along a wand. -/
theorem walHandleIn_nmd (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (h : WalHS)
    (tm : Fs.OsMeta → List Fs.ByteG → Prop) (A B : IProp GF) :
    ⊢ (A -∗ B) -∗ walHandleIn (W := W) P Mr w dir h tm A -∗ walHandleIn (W := W) P Mr w dir h tm B := by
  iintro Hw Hh
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, Hd, Hr⟩
  iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19
  isplitl [Hw Hd]
  · iapply walDirH_nmd $$ Hw Hd
  iexact Hr

/-- **A named handle forgets its naming.** -/
theorem walOpenWF_unnamed (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    ⊢ walOpenWF (W := W) P Mr w dir -∗ walOpenWFU (W := W) P Mr w dir := by
  iintro H
  unfold walOpenWF walOpenWFU
  icases H with ⟨%h, Hh, Hr⟩
  iexists h
  iframe Hr
  iapply walHandleIn_nmd P Mr w dir h TailMetaW (walNamed (W := W) dir) emp $$ [] Hh
  iintro -
  iempintro

/-- **The parent's fsync names the handle** (`Create`): with `walNamed dir`, the client handle. -/
theorem walOpenWFU_named (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    ⊢ walOpenWFU (W := W) P Mr w dir -∗ walNamed (W := W) dir -∗ walOpenWF (W := W) P Mr w dir := by
  iintro H #Hn
  unfold walOpenWF walOpenWFU
  icases H with ⟨%h, Hh, Hr⟩
  iexists h
  iframe Hr
  iapply walHandleIn_nmd P Mr w dir h TailMetaW emp (walNamed (W := W) dir) $$ [] Hh
  iintro -
  iexact Hn

/-- **The `dir` field of the handle before naming, lent** (`Create` reads `w.dir` after `renameWAL`). -/
theorem walOpenWFU_dirAcc (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    ⊢ walOpenWFU (W := W) P Mr w dir -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
      (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir -∗
        walOpenWFU (W := W) P Mr w dir) := by
  iintro H
  unfold walOpenWFU
  icases H with ⟨%h, Hh, Hr⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    H1, H2, H3, Hh⟩
  iframe H3
  iintro H3
  iexists h
  iframe Hr
  iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
  iframe H1 H2 H3 Hh

/-- **The handle before naming holds the lock token** (`create_areaBack`'s `T`). -/
theorem walOpenWFU_unlocked_excl (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    ⊢ walOpenWFU (W := W) P Mr w dir -∗ walUnlockedTok (W := W) -∗ False := by
  iintro H Hu
  unfold walOpenWFU
  icases H with ⟨%h, Hh, -⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hw, -⟩
  unfold walOpenW
  icases Hw with ⟨-, Hl⟩
  iapply walLockedTok_unlocked_excl $$ Hl Hu

/-- **The handle holds the lock token.** -/
theorem walOpenWF_unlocked_excl (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    ⊢ walOpenWF (W := W) P Mr w dir -∗ walUnlockedTok (W := W) -∗ False := by
  iintro H Hu
  ihave H := walOpenWF_unnamed P Mr w dir $$ H
  iapply walOpenWFU_unlocked_excl P Mr w dir $$ H Hu

end handle

end WalFs
end EtcdGrove
end Perennial

end
