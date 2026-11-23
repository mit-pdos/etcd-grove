/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__cleanupWAL.lean` (W4 of
`notes/wal-fsext-plan.md`, `notes/wal-units/create.md`): `w.Close()` (`WAL.Close.spec` at the state `unnamed`), then the
broken name (`time.Now.specLoc`, `time.Time.Format.specBroken`, `fmt.SprintfBroken.spec`) and the rename
(`os.Rename.specDirAnySnc`) over the caller's law. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cleanupWAL
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Close
public import Spec.time.Time__FormatBroken
public import Spec.fmt.SprintfBroken
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.time.NowLoc
public import Proof.os.NsS

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
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.cleanupWAL.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_CloseU : go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.spec (W := W) (Sio := WalFs.ioNone) P Mr)
    (wp_Now : time.Now.specLoc (GF := GF) (hG := hG))
    (wp_Format : time.Time.Format.specBroken (GF := GF) (hG := hG))
    (wp_Sprintf : fmt.SprintfBroken.spec (GF := GF) (hG := hG))
    (wp_Rename : os.Rename.specDirAnySnc (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.cleanupWAL.spec (W := W) P Mr := by
  intro R jr r nm w lg Rp qp tf Fr Fin hnmO
  wp_start as ⟨#Hzap, #Harea, Hw, Hpw, Hperm, Hfr, Hlaw⟩
  ihave #Harea2 := Harea
  iunfold WalFs.walAreaOk at Harea2
  icases Harea2 with ⟨-, #Hosi, #Hsi, -⟩
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨-, -, #Hfmt, -, -, -, -, -, -, -, -, -, #Hos, #Htime, -, -, #Hzp, -, -, -, -, -, -, -⟩
  try wp_auto
  wp_apply wp_CloseU R jr r w (child r nm) (.unnamed Rp qp tf) (fun _ => iprop(True)) $$ [Hw Hpw] as %cerr Hc
  · dsimp only
    iframe; iframe #
  icases Hc with (⟨#Hek, Hdir, Hu, Hnf, Hperm2, Hpaths, Htf⟩ | ⟨%hcerr, #Hek, Hlk, Hnf, Htf⟩)
  rotate_left
  · -- the sync failed: `Close`'s error returned
    rcases cerr with ei | _
    rotate_left
    · exact absurd rfl hcerr
    try wp_auto
    wp_apply wp_Error as %f1 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    try wp_auto
    wp_apply wp_Warn lg _ _ $$ []
    · iframe #
    try wp_auto
    iapply HΦ
    ileft
    iframe
    isplitr
    · ipureintro; exact hcerr
    iexact Hek
  by_cases hce : cerr = interface.nil
  rotate_left
  · -- `Close` returned everything but an error: returned
    rcases cerr with ei | _
    rotate_left
    · exact absurd rfl hce
    try wp_auto
    wp_apply wp_Error as %f1 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    try wp_auto
    wp_apply wp_Warn lg _ _ $$ []
    · iframe #
    try wp_auto
    iapply HΦ
    iright; ileft
    iframe
    isplitr
    · ipureintro; exact hce
    iapply fmtErrorOkOrNil_ne _ hce; iexact Hek
  subst hce
  try wp_auto
  wp_apply wp_Now as %t ⟨%l, #Hl, %htl⟩
  wp_apply wp_Format t l $$ [] as %ts %hts
  · iframe #; ipureintro; exact Or.inr htl
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #(child r nm), interface.mkOk go.string #ts]
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  try wp_auto
  wp_apply wp_Sprintf (child r nm) ts _ _ $$ [$Hasl] as %bn ⟨-, %hbn⟩
  rw [child_brokenName] at hbn
  subst hbn
  try wp_auto
  -- the rename, over the law
  iunfold cleanupLaw at Hlaw
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod Hlaw $$ %ts %hts Hfr Hu Hnf Hpaths Htf Hnc with
    ⟨Hnc, %J, %N, %qd, %h, %q, %rr, %lb, %Qr, %hp, Hp, Hlb, HN, Hau, Hk⟩
  iframe Hnc
  imodintro
  obtain ⟨hN1, hN2, hJ, hq⟩ := hp
  icases osPathS_callKey R r _ _ $$ Hp with ⟨Hp, %hkc⟩
  ihave Hperm2 := osCallPerm_congr _ (hkc nm) $$ Hperm2
  ihave Hperm := (osCallPerm_split (L := hG.goose_localGS) (callKey R r) (1 : Qp).half (1 : Qp).half).2 $$ [Hperm Hperm2]
  · iframe
  rw [Qp.half_add_half]
  have hne : nm ≠ brokenName nm ts := fun he => by
    have := congrArg List.length he
    simp [brokenName] at this
  wp_apply wp_Rename r nm (brokenName nm ts) jr J N R qd h q rr lb Qr hnmO
    (brokenName_nameOk hnmO hts) hN1 hN2 hne hJ hq $$ [Hp Hperm Hlb HN Hau] as %rerr ⟨Hp, Hperm, #Hrf, Hout⟩
  · iframe; iframe #
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod Hk $$ %rerr Hnc Hp Hperm Hout with ⟨Hnc, Hfin⟩
  iframe Hnc
  imodintro
  try wp_auto
  rcases rerr with ei | _
  · -- the rename failed (or took effect and failed): logged, its error returned
    try wp_auto
    wp_apply wp_Error as %f1 -
    wp_apply wp_String as %f2 -
    wp_apply wp_String as %f3 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    try wp_auto
    wp_apply wp_Warn lg _ _ $$ []
    · iframe #
    try wp_auto
    iapply HΦ
    iright; iright
    iframe Hfin Hrf
  · try wp_auto
    iapply HΦ
    iright; iright
    iframe Hfin Hrf

end proof

end EtcdGrove
end Perennial

end
