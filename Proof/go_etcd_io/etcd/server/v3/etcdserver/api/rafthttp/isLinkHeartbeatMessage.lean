/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/isLinkHeartbeatMessage.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isLinkHeartbeatMessage
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.isLinkHeartbeatMessage.wp_proof
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    rafthttp.isLinkHeartbeatMessage.spec (GF := GF) (hG := hG) := by
  intro ml dq dqe cap st
  wp_start as Hm
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_load
  wp_pures
  wp_apply wp_GetType.1 $$ [$Hm] as Hm
  (try wp_pures)
  by_cases h1 : st.msg.Type' = MsgHeartbeat
  · rw [decide_eq_true (p := st.msg.Type' = W32 8) h1]
    wp_pures
    (try wp_load)
    (try wp_pures)
    wp_apply wp_GetFrom.1 $$ [$Hm] as Hm
    (try wp_pures)
    by_cases h2 : st.msg.From' = 0
    · rw [decide_eq_true (p := st.msg.From' = W64 0) h2]
      wp_pures
      (try wp_load)
      (try wp_pures)
      wp_apply wp_GetTo.1 $$ [$Hm] as Hm
      (try wp_pures)
      have : decide (st.msg.To' = W64 0) = decide (isHB st.msg) := by
        simp [isHB, h1, h2]
      rw [this]
      wp_pures
      iapply HΦ; iexact Hm
    · rw [decide_eq_false (p := st.msg.From' = W64 0) h2,
        decide_eq_false (p := isHB st.msg) (fun h => h2 h.2.1)]
      wp_pures
      iapply HΦ; iexact Hm
  · rw [decide_eq_false (p := st.msg.Type' = W32 8) h1,
      decide_eq_false (p := isHB st.msg) (fun h => h1 h.1)]
    wp_pures
    iapply HΦ; iexact Hm

end proof

end EtcdGrove
end Perennial
