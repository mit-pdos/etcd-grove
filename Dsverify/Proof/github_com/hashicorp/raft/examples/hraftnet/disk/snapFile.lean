/-
(hraft_robust R3) The proof of `disk.snapFile`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.snapFile

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

theorem github_com.hashicorp.raft.examples.hraftnet.disk.snapFile.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.disk.snapFile.spec (GF := GF) (hG := hG) := by
  intro dir
  wp_start as -
  wp_auto
  iapply HΦ
  itrivial

end sec

end Perennial
