/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/ReadDirAbsent.lean`, over
`os.Open.wp_absentS` (`LinuxFs/Proof/os/NsAbsentS.lean`). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirAbsent

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
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.wp_proofAbsent :
    go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.specAbsent (GF := GF) (hG := hG) := by
  intro d b R j dq qc N dqn h hb hN hi
  wp_start as ⟨#Hos, #Hsi, #Hpkg, Hp, Hperm, Hn⟩
  wp_auto
  sorry

end proof

end EtcdGrove
end Perennial

end
