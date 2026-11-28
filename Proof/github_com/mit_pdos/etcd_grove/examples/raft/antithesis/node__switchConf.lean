/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__switchConf.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__switchConf
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.switchConf.wp_proof (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG)) :
    node.switchConf.spec (GF := GF) (hG := hG) := by
  intro n p dq e hty
  wp_start as Hp
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetType.1 p dq e $$ [$Hpb $Hp] as Hp
  rw [hty]
  try wp_auto
  iapply HΦ
  iframe

end proof

end AntHarness
end EtcdGrove
end Perennial
