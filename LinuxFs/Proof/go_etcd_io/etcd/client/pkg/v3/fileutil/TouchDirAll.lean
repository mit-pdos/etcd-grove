/-
`fileutil.TouchDirAll` and `CreateDirAll` over `fsExt`: proofs (W4/W13 of `notes/wal-fsext-plan.md`).
The callees' specs the `os` layer does not have yet (`os.MkdirAll`, `os.Stat` of a regular file,
`os.WriteFile`, `filepath.Abs`) are to be taken as hypotheses (the W4 implementation log lists them).
Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.CreateDirAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem fileutil.TouchDirAll.wp_proof : fileutil.TouchDirAll.spec (GF := GF) := by
  sorry

theorem fileutil.CreateDirAll.wp_proof (hT : fileutil.TouchDirAll.spec (GF := GF)) :
    fileutil.CreateDirAll.spec (GF := GF) := by
  sorry

end proof

end EtcdGrove
end Perennial
