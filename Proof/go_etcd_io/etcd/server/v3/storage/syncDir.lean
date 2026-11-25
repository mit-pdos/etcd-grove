/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/syncDir.lean`, over `fileutil.OpenDir`'s and
`fileutil.Fsync`'s directory specs, at any instances of the file extension: `fileutil.syncDir`'s proof
(`Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/syncDir.lean`), the code being the same.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.syncDir
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FsyncS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

theorem storage.syncDir.wp_proof
    (wp_OpenDir : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [os.file.FieldAssumptions],
      go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.spec (GF := GF) (hG := hG))
    (wp_Fsync : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt],
      go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specDirS (GF := GF) (hG := hG)) :
    storage.syncDir.spec (GF := GF) (hG := hG) := by
  intro _ _ _ _ p R j dq qc n
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm, #Hlb⟩
  wp_auto
  wp_apply wp_OpenDir p R j dq qc $$ [Hp Hperm] as %f %err ⟨Hp, Hperm, Hr⟩
  · iframe; (repeat' isplitl []) <;> (first | iassumption | iPkgInit)
  icases Hr with (⟨%fd, %herr, Hf, Hfd⟩ | ⟨%herr, #Hfe⟩)
  · subst herr
    wp_auto
    wp_apply wp_Fsync f fd p (DFrac.own 1) R j .idle n $$ [Hf Hfd] as %e ⟨Hf, Hfd, He⟩
    · iframe; isplitl [] <;> try iassumption
      isplitl [] <;> iassumption
    icases He with (⟨%he, #Hfe⟩ | ⟨%he, #Hc⟩)
    · cases e with
      | nil => exact absurd rfl he.1
      | ok i =>
        wp_auto
        wp_apply os.File.Close.wp_dirS f fd p j .idle $$ [Hf Hfd] as %e' -
        · iframe; iassumption
        iapply HΦ
        isplitr
        · iapply fmtErrorOkOrNil_of $$ Hfe
        iframe
        ileft; ipureintro; exact he.1
    · subst he
      wp_auto
      wp_apply os.File.Close.wp_dirS f fd p j .idle $$ [Hf Hfd] as %e' #Hfe'
      · iframe; iassumption
      iapply HΦ
      isplitr
      · iexact Hfe'
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
      isplitr
      · iexact Hfe
      iframe
      ileft; ipureintro; exact herr

end proof

end EtcdGrove
end Perennial
