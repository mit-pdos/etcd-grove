/-
Lean-first (no Rocq counterpart). #33 parity B2: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/isRequest.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.isRequest
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
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem isRequest.wp_proof (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)) :
    isRequest.spec (GF := GF) (hG := hG) := by
  intro ml dq dqe cap st
  wp_start as Hm
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetType.1 ml dq dqe cap st $$ [$Hpb $Hm] as Hm
  wp_if_destruct
  · have h : isRequestTy st.msg.Type' = true := by rw [Hif]; decide
    rw [h]
    iapply HΦ
    iexact Hm
  · wp_apply wp_GetType.1 ml dq dqe cap st $$ [$Hpb $Hm] as Hm
    have h : isRequestTy st.msg.Type' = decide (st.msg.Type' = W32 8) := by
      unfold isRequestTy
      rw [show MsgApp = W32 3 from rfl, show MsgHeartbeat = W32 8 from rfl, decide_eq_false Hif,
        Bool.false_or]
    rw [h]
    iapply HΦ
    iexact Hm

end proof

end AntHarness
end EtcdGrove
end Perennial
