/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.IsLocalMsg
public import Spec.go_etcd_io.raft.v3.IsLocalMsgTarget
public import Spec.go_etcd_io.raft.v3.node__step
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Proof.go_etcd_io.raft.v3.LemmasNodeR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A local message from a remote sender is dropped; anything else goes to `step`. (Raft v3.7,
stage R5: `m` a pointer, not `nil` (`stepP`'s `msgIn`, so the `nil` check's error is
unreachable); its type and sender read by `m.GetType()`/`m.GetFrom()`, new callees, over the
message `stepP_split` opens. Stage R7a: any `nodeCtx`, the error `nodeErr`, `nil` for a dropped
message.) -/
theorem node.Step.wp_proof
    (wp_IsLocalMsg : IsLocalMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_node_step : node.step.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)) :
    node.Step.spec (GF := GF) (hG := hG) := by
  intro γ id n m ctx cd
  wp_start as ⟨#Hnode, #Hctx, Hstep⟩
  icases stepP_split γ id m $$ Hstep with ⟨%dqe, %st, Hm, %Hty, Hclose⟩
  icases msgPtsC_nonnull $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply wp_GetType.1 $$ [Hm] as Hm
  · iexact Hm
  wp_apply wp_IsLocalMsg st.msg.Type' Hty as %b -
  cases b
  · wp_auto
    wp_apply wp_node_step γ id n m ctx cd $$ [$Hnode $Hctx Hm Hclose]
    · iapply Hclose $$ Hm
    iintro %err #Herr
    wp_auto
    iapply HΦ
    iexact Herr
  · wp_auto
    wp_apply wp_GetFrom.1 $$ [Hm] as Hm
    · iexact Hm
    wp_apply wp_IsLocalMsgTarget st.msg.From'
    wp_if_destruct
    · wp_apply wp_node_step γ id n m ctx cd $$ [$Hnode $Hctx Hm Hclose]
      · iapply Hclose $$ Hm
      iintro %err #Herr
      wp_auto
      iapply HΦ
      iexact Herr
    · iapply HΦ
      iapply nodeErr_nil

end proof

end EtcdGrove
end Perennial
