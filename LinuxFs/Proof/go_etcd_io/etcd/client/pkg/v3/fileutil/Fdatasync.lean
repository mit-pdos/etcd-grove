/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/Fdatasync.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync

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

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.wp_proof
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.Fdatasync.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m lo xs hcov
  wp_start as ⟨#Hinv, Hf, Hfd, Hm, Hb⟩
  wp_auto
  wp_apply wp_Fd f fd name dqf $$ Hf as Hf
  wp_apply wp_Fdatasync fd dq d m lo xs hcov $$ [Hfd Hm Hb] as %e ⟨Hfd, Hr⟩
  · iframe; iexact Hinv
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
