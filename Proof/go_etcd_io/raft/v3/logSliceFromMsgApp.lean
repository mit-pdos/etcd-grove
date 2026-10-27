/-
Port of election_proof/proof_logSliceFromMsgApp.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetEntries
public import Spec.go_etcd_io.raft.v3.logSliceFromMsgApp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem logSliceFromMsgApp.wp_proof
    (wp_Message_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_Message_GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG))
    (wp_Message_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Message_GetEntries : raftpb.Message.GetEntries.spec (GF := GF) (hG := hG)) :
    logSliceFromMsgApp.spec (GF := GF) (hG := hG) := by
  intro p dq dqe cap ms
  wp_start as Hm
  wp_auto
  wp_apply wp_Message_GetTerm.1 p dq dqe cap ms $$ [$Hm] as Hm
  wp_apply wp_Message_GetLogTerm.1 p dq dqe cap ms $$ [$Hm] as Hm
  wp_apply wp_Message_GetIndex.1 p dq dqe cap ms $$ [$Hm] as Hm
  wp_apply wp_Message_GetEntries.1 p dq dqe cap ms $$ [$Hm] as %es %els ⟨Hes, Hro, Hcap, Hback⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
