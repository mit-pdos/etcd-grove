/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/OpenDirOk.lean`, over
`os.Open.wp_dirSOk` (`LinuxFs/Proof/os/NsSOk.lean`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDirOk
public import LinuxFs.Proof.os.NsSOk

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

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.wp_proofOk :
    go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.specOk (GF := GF) (hG := hG) := by
  intro p R j dq qc
  wp_start as ⟨#Hinv, #Hsi, Hp, Hperm⟩
  wp_auto
  wp_apply os.Open.wp_dirSOk p R j dq qc $$ [Hinv Hsi Hp Hperm] as %f %err Hr
  · iframe; isplitl [] <;> iassumption
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial
