/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/WithExt.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.WithExt

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

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.WithExt.wp_proof :
    go_etcd_io.etcd.client.pkg.v3.fileutil.WithExt.spec (GF := GF) (hG := hG) := by
  intro ext
  wp_start as -
  iapply wp_fupd
  wp_auto
  ipersist ext
  imodintro
  iapply HΦ
  unfold fileutil.withExtFn
  imodintro
  iintro %op %o %Ψ Hop HΨ
  wp_auto
  iapply HΨ $$ Hop

end proof

end EtcdGrove
end Perennial
