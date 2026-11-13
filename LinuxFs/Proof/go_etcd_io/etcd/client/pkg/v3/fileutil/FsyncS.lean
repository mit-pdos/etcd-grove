/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/FsyncS.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FsyncS
public import LinuxFs.Proof.os.NsAbove

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

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.wp_proofDirS
    (wp_Sync : os.File.Sync.specDirS (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specDirS (GF := GF) (hG := hG) := by
  intro f fd name dqf R j ph n
  wp_start as Hpre
  wp_auto
  wp_apply wp_Sync f fd name dqf R j ph n $$ Hpre as %err Hr
  iapply HΦ
  iexact Hr

variable [os.Assumptions] [go.BasicIntoValInj] in
theorem go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.wp_proofOutS :
    go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync.specOutS (GF := GF) (hG := hG) := by
  intro f fd name dqf
  wp_start as Hpre
  wp_auto
  wp_apply os.File.Sync.wp_outS f fd name dqf $$ Hpre as %err Hr
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial
