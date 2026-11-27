/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__sent.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__sent
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType

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

theorem node.sent.wp_proof (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)) :
    node.sent.spec (GF := GF) (hG := hG) := by
  intro n ml dq dqe cap st hsnap
  wp_start as Hml
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetType.1 ml _ _ _ st $$ [$Hpb $Hml] as Hml
  rw [decide_eq_false (show st.msg.Type' ≠ W32 7 from hsnap)]
  try wp_auto
  iapply HΦ
  iframe

end proof

end AntHarness
end EtcdGrove
end Perennial
