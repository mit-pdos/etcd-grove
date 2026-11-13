/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/syncDir.lean`, over `OpenDir`'s and
`Fsync`'s directory specs.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FsyncS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.wp_proof
    (wp_OpenDir : go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.spec (GF := GF) (hG := hG))
    (wp_Fsync : go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specDirS (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.spec (GF := GF) (hG := hG) := by
  intro p R j dq qc n
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm, #Hlb⟩
  wp_auto
  wp_apply wp_OpenDir p R j dq qc $$ [Hp Hperm] as %f %err ⟨Hp, Hperm, Hr⟩
  · iframe; isplitl [] <;> iassumption
  icases Hr with (⟨%fd, %herr, Hf, Hfd⟩ | %herr)
  · subst herr
    wp_auto
    wp_apply wp_Fsync f fd p (DFrac.own 1) R j .idle n $$ [Hf Hfd] as %e ⟨Hf, Hfd, He⟩
    · iframe; isplitl [] <;> try iassumption
      isplitl [] <;> iassumption
    icases He with (%he | ⟨%he, #Hc⟩)
    · cases e with
      | nil => exact absurd rfl he
      | ok i =>
        wp_auto
        wp_apply os.File.Close.wp_dirS f fd p j .idle $$ [Hf Hfd] as %e' -
        · iframe; iassumption
        iapply HΦ
        iframe
        ileft; ipureintro; exact he
    · subst he
      wp_auto
      wp_apply os.File.Close.wp_dirS f fd p j .idle $$ [Hf Hfd] as %e' -
      · iframe; iassumption
      iapply HΦ
      iframe
      by_cases he' : e' = interface.nil
      · iright; isplitr
        · ipureintro; exact he'
        iassumption
      · ileft; ipureintro; exact he'
  · obtain ⟨herr, rfl⟩ := herr
    cases err with
    | nil => exact absurd rfl herr
    | ok i =>
      wp_auto
      iapply HΦ
      iframe
      ileft; ipureintro; exact herr

end proof

end EtcdGrove
end Perennial
