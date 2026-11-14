/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/CheckDirPermission.lean`, over
`Exist`, `os.Stat.wp_dirS` and `fmt.ErrorfStrs.spec`. Lean-first (`wal-leaf5`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.CheckDirPermission
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Exist
public import LinuxFs.Spec.fmt.ErrorfStrs
public import LinuxFs.Proof.os.StatS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.fileStat.FieldAssumptions]

/-- `os.Stat` of a directory, its result dropped (the form `fileutil.Exist.spec` takes). -/
theorem wp_statDir_err' (p : GoString) (R : Roots) (J : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osCallPerm qc }}
      (App (Val (@! os.Stat)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R p dq J ∗
        osCallPerm qc }} := by
  iintro %Φ Hpre HΦ
  wp_apply os.Stat.wp_dirS p R J dq qc $$ Hpre as %fi %err ⟨Hp, Hperm, -⟩
  iapply HΦ
  iframe

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.CheckDirPermission.wp_proof
    (wp_Exist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfStrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.CheckDirPermission.spec (GF := GF) (hG := hG) := by
  intro p perm R J dq qc
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm⟩
  wp_auto
  wp_apply wp_Exist p _ _ (wp_statDir_err' p R J dq qc) $$ [Hp Hperm] as %b ⟨%err, %hb, Hp, Hperm⟩
  · iframe; isplitl [] <;> iassumption
  subst hb
  by_cases he : err = GoInterface.nil
  rotate_left
  · rw [decide_eq_false he]
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf _ _ [interface.ok (interface.mk go.string #p)] _ $$ [Hsl] as %e ⟨-, -, -⟩
    · iframe
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ a => fmt.strArgOk (GF := GF) a)).2
      unfold fmt.strArgOk
      ileft; ipureintro; exact Or.inl (argWf_string _)
    try wp_auto
    iapply HΦ
    iframe
  rw [decide_eq_true he]
  wp_auto
  wp_apply os.Stat.wp_dirS p R J dq qc $$ [Hp Hperm] as %fi %err2 ⟨Hp, Hperm, Hres⟩
  · iframe; isplitl [] <;> iassumption
  icases Hres with (⟨%fs, %sz, ⟨%he2, %hfi⟩, Hfs⟩ | %he2)
  rotate_left
  · cases err2 with
    | nil => exact absurd rfl he2
    | ok ie =>
    wp_auto
    iapply HΦ
    iframe
  subst he2 hfi
  wp_auto
  unfold os.ownFileStat
  icases Hfs with ⟨#Hsz, ⟨%mode, #Hmode⟩, -⟩
  wp_method_call
  wp_call
  try wp_auto
  haveI : go.NotInterface go.uint32 := ⟨trivial⟩
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  by_cases hpm : mode &&& W32 511 = perm
  · rw [decide_eq_true hpm]
    wp_auto
    iapply HΦ
    iframe
  rw [decide_eq_false hpm]
  wp_auto
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.string #p,
    interface.mkOk io.fs.FileMode.ty #mode, interface.mkOk os.FileMode.ty #(W32 448)]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_Errorf _ _ [interface.mkOk go.string #p,
    interface.mkOk io.fs.FileMode.ty #mode, interface.mkOk os.FileMode.ty #(W32 448)] _ $$ [Hsl]
    as %e ⟨-, -, -⟩
  · iframe Hsl
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · simp only [fmt.strArgOk]; ileft; ipureintro; exact Or.inl (argWf_string _)
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · simp only [fmt.strArgOk]; ileft; ipureintro; right; simp; exact ⟨_, rfl⟩
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ a => fmt.strArgOk (GF := GF) a)).2
    simp only [fmt.strArgOk]; ileft; ipureintro; right; simp; exact ⟨_, rfl⟩
  try wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
