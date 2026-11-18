/-
`DB.fileSize` (U4, `notes/bbolt-proof-plan.md`): the file's size by `Stat`, an error when it is
under two pages. Its errors are `fmt.Errorf`'s, `fmtErrorOk`.
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.ErrPtr
public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.os.File__Stat
public import Spec.os.fileStat__Size
public import Spec.fmt.Errorf
public import Spec.fmt.ErrorOk
public import Proof.go_etcd_io.bbolt.Mmap.FileSizeDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section fsz
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.fileSize.wp_proof (hStat : os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    DB.fileSize.spec (GF := GF) (hG := hG) := by
  intro db f fd p dqf dqo dqd dqm d m hp hsz
  rcases p with ⟨pp, pi⟩
  dsimp only at hp ⊢
  subst hp
  wp_start as ⟨#Hos, Hf, Hfo, Hfd, Hm, #Hps⟩
  wp_auto
  wp_apply hStat f fd pp dqo dqd dqm d m $$ [Hfo Hfd Hm] as %fi %err ⟨Hfo, Hfd, Hm, Hr, #Hek, -⟩
  · rw [← fileOwn_eq]; iframe; iframe #
  ihave Hfo : fileOwn f fd pp dqo $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  try wp_auto
  icases Hr with (⟨%fs, %Hfs, Hst⟩ | %Hfs)
  · obtain ⟨rfl, rfl⟩ := Hfs
    wp_auto
    wp_apply hSize fs (W64 (m.size : Int)) $$ [Hst] as Hst
    · iframe
    try wp_auto
    have e1 : sint.Z (W64 (m.size : Int)) = (m.size : Int) := by word
    have e2 : sint.Z (W64 4096 * W64 2) = 8192 := by word
    rw [e1, e2]
    by_cases hs : (m.size : Int) < 8192
    · rw [decide_eq_true hs]
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply hErrorf _ _ _ _ $$ [$Hsl] as %e ⟨-, #HeS0, %Hty0, %Hptr0⟩
      · iframe
        fmt_args_ok
      try wp_auto
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => nomatch h), errPtrTyped_of_ptr _ Hptr0⟩
      · iapply errorf_fmtErrorOk
        isplitl
        · iexact HeS0
        · ipureintro; exact Hty0
    · rw [decide_eq_false hs]
      wp_auto
      iapply HΦ
      iframe
      ileft
      ipureintro
      exact ⟨rfl, rfl, by omega⟩
  · obtain ⟨hne, rfl⟩ := Hfs
    cases err with
    | nil => exact absurd rfl hne
    | ok ii =>
      ihave #Hek : fmtErrorOk (GF := GF) (GoInterface.ok ii) $$ []
      · iapply fmtErrorOkOrNil_ne _ hne $$ Hek
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply hErrorf _ _ _ _ $$ [$Hsl] as %e ⟨-, #HeS0, %Hty0, %Hptr0⟩
      · iframe
        fmt_args_intro
        isplitl
        · fmt_arg_method; iapply fmtErrorOk_argOk $$ Hek
        · itrivial
      try wp_auto
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => nomatch h), errPtrTyped_of_ptr _ Hptr0⟩
      · iapply errorf_fmtErrorOk
        isplitl
        · iexact HeS0
        · ipureintro; exact Hty0

end fsz

end bbolt
end EtcdGrove
end Perennial
