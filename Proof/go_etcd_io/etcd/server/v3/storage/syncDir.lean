/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/syncDir.lean`, over `fileutil.OpenDir`'s no-error
spec and `fileutil.Fsync`'s directory spec, at any instances of the file extension, and the close of a
directory fd with no error (`os.File.Close.wp_dirSNE`): `fileutil.syncDir`'s proof
(`Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/syncDir.lean`), the code being the same, with every
error refuted by `FsNoErrOn (· = dir)`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.syncDir
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FsyncS
public import Proof.os.CloseNE

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
    (wp_OpenDir : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt],
      go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.specNE (GF := GF) (hG := hG))
    (wp_Fsync : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt],
      go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specDirS (GF := GF) (hG := hG)) :
    storage.syncDir.spec (GF := GF) (hG := hG) := by
  intro _ _ _ p R j dq qc n hne hfit
  obtain ⟨Sio, hino, h1, h2, hpS⟩ := hne
  haveI := h1; haveI := h2
  have hino' : FsNoErrIno := ⟨Sio, hino, h1, h2, fun _ h => h.elim⟩
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm, #Hlb⟩
  wp_auto
  wp_apply wp_OpenDir p R j dq qc ⟨Sio, hino, h1, h2, hpS⟩ hfit $$ [Hp Hperm]
    as %f %err ⟨Hp, Hperm, %fd, %herr, Hf, Hfd⟩
  · iframe; (repeat' isplitl []) <;> (first | iassumption | iPkgInit)
  subst herr
  wp_auto
  wp_apply wp_Fsync f fd p (DFrac.own 1) R j .idle n $$ [Hf Hfd] as %e ⟨Hf, Hfd, He⟩
  · iframe; isplitl [] <;> try iassumption
    isplitl [] <;> iassumption
  icases He with (⟨%he, -⟩ | ⟨%he, #Hc⟩)
  · exact (he.2 hino').elim
  subst he
  wp_auto
  wp_apply os.File.Close.wp_dirSNE hino f fd p j .idle $$ [Hf Hfd]
  · iframe; iassumption
  iintro -
  wp_auto
  iapply HΦ
  iframe
  iexact Hc

end proof

end EtcdGrove
end Perennial
