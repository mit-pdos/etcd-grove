/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/Exist.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Exist

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

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.wp_proof :
    go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG) := by
  intro name P Q hstat
  wp_start as HP
  wp_auto
  wp_apply hstat $$ HP as %fi %err HQ
  cases err with
  | nil =>
    wp_auto
    iapply HΦ
    iexists GoInterface.nil
    iframe
    ipureintro; simp
  | ok e =>
    wp_auto
    iapply HΦ
    iexists GoInterface.ok e
    iframe
    ipureintro; simp

end proof

end EtcdGrove
end Perennial
