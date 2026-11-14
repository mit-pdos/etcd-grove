/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__cleanupWAL.lean` (W4 of
`notes/wal-fsext-plan.md`, `notes/wal-units/create.md`): `w.Close()` (`WAL.Close.specU`), then the
broken name (`time.Now`, `time.Time.Format.specBroken`, `fmt.SprintfBroken.spec`) and the rename
(`os.Rename.specDirAnySnc`) over the caller's law. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cleanupWAL
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__CloseU
public import LinuxFs.Spec.time.Time__FormatBroken
public import LinuxFs.Spec.fmt.SprintfBroken
public import LinuxFs.Spec.go_uber_org.zap.String
public import LinuxFs.Spec.go_uber_org.zap.Error
public import LinuxFs.Spec.go_uber_org.zap.Logger__Warn
public import Perennial.Spec.time.Now
public import LinuxFs.Proof.os.NsS

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
    (wp_CloseU : go_etcd_io.etcd.server.v3.storage.wal.WAL.Close.specU (W := W) P Mr)
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
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
  wp_apply wp_CloseU R jr r w (child r nm) Rp qp tf $$ [Hw Hpw] as %cerr Hc
  · iframe; iframe #
  icases Hc with (⟨Hdir, Hu, Hnf, Hperm2, Hpaths, Htf⟩ | ⟨%hcerr, Hlk, Hnf, Htf⟩)
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
    ipureintro; exact hcerr
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
    ipureintro; exact hce
  subst hce
  try wp_auto
  wp_apply wp_Now as %t -
  wp_apply wp_Format t as %ts %hts
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
  ihave Hperm := (osCallPerm_split (L := hG.goose_localGS) (1 : Qp).half (1 : Qp).half).2 $$ [Hperm Hperm2]
  · iframe
  rw [Qp.half_add_half]
  iunfold cleanupLaw at Hlaw
  imod Hlaw $$ %ts %hts Hfr Hu Hnf Hpaths Htf with
    ⟨%J, %N, %qd, %h, %q, %rr, %lb, %Qr, %hp, Hp, Hlb, HN, Hau, Hk⟩
  obtain ⟨hN1, hN2, hJ, hq⟩ := hp
  have hne : nm ≠ brokenName nm ts := fun he => by
    have := congrArg List.length he
    simp [brokenName] at this
  wp_apply wp_Rename r nm (brokenName nm ts) jr J N R qd h q rr lb Qr hnmO
    (brokenName_nameOk hnmO hts) hN1 hN2 hne hJ hq $$ [Hp Hperm Hlb HN Hau] as %rerr ⟨Hp, Hperm, Hout⟩
  · iframe; iframe #
  imod Hk $$ %rerr Hp Hperm Hout with Hfin
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
    iexact Hfin
  · try wp_auto
    iapply HΦ
    iright; iright
    iexact Hfin

end proof

end EtcdGrove
end Perennial

end
