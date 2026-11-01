/- Lean-first (no Rocq counterpart).

**Raft v3.7 (2026-10-16, stage R5 of the retarget).** Ported from the old proof. What changed:
the proposal from `propc` is a message pointer, owned (`propP`: `msgIn`), stamped by `run`
(`m.From = new(r.id)`: `cellRO_alloc`, `msgPtsC_store_From`) before `r.Step(m)`; a `recvc`
message is a pointer (`netP`: `msgIn ml □ st`) whose type and sender `run` reads through the
getters (`GetType`, `GetFrom`); `confc` carries a `*pb.ConfChangeV2` (`ownConfChangeV2 v □ ccm`) and
`applyConfChange` returns a fresh `*pb.ConfState` (`csPts cs 1 c true`), whose `Voters` and
`VotersOutgoing` fields the removed-node check reads directly, and which goes to `confstatec`
whole (`confstateP`); a `Ready`'s messages are handed out (`QMsg`, D8).

(D22 S-d4, 2026-10-21) A `MsgSnap` from `recvc` at a node that takes snapshots (`netP`,
`headRest_snapIn`); a `Ready` with a snapshot (the loan `L`): `readyc`'s payload `readySnapData`
(the storage lent, the snapshot's certificate), `run`'s record with the loan, and at `advancec` the
loan's receipt (`advRet`'s `loanRet`) for `RawNode.Advance`, the committed log handed out the
loan's (`advRS`). -/
module

public import Proof.go_etcd_io.raft.v3.InvAdvance
public import Spec.go_etcd_io.raft.v3.node__run
public import Spec.go_etcd_io.raft.v3.RawNode__HasReady
public import Spec.go_etcd_io.raft.v3.RawNode__readyWithoutAccept
public import Spec.go_etcd_io.raft.v3.RawNode__acceptReady
public import Spec.go_etcd_io.raft.v3.RawNode__Advance
public import Spec.go_etcd_io.raft.v3.RawNode__Tick
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raft__hasLeader
public import Spec.go_etcd_io.raft.v3.getStatus
public import Spec.go_etcd_io.raft.v3.IsResponseMsg
public import Spec.go_etcd_io.raft.v3.IsLocalMsgTarget
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvNodeRunHup
public import Proof.go_etcd_io.raft.v3.LemmasRunR
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [GooseInterp] [GooseSemantics] [StorageModel GF] in
/-- A loop condition `wp_if_destruct` left as the value equation (D22 S-d3a), peeled. -/
private theorem hif_pos {P : Prop} [Decidable P] (h : (#(decide P) : val) = #true) : P :=
  of_decide_eq_true (GoGlobalContext.intoVal_inj_bool h)

omit [GooseInterp] [GooseSemantics] [StorageModel GF] in
private theorem hif_neg {P : Prop} [Decidable P] (h : ¬ ((#(decide P) : val) = #true)) : ¬ P :=
  fun hp => h (by rw [decide_eq_true hp])

set_option hygiene false in
/-- Peel `Hif` if `wp_if_destruct` left it as the value equation. -/
local macro "peel_hif" : tactic => `(tactic| first
  | (replace Hif := hif_pos Hif
     try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false, decide_eq_true Hif,
       Bool.false_eq_true, ↓reduceIte]
     try wp_auto)
  | (replace Hif := hif_neg Hif
     try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false, decide_eq_false Hif,
       Bool.false_eq_true, ↓reduceIte]
     try wp_auto)
  | skip)

set_option maxHeartbeats 1000000 in
theorem node.run.wp_proof
    (wp_RawNode_HasReady : RawNode.HasReady.spec (GF := GF) (hG := hG))
    (wp_RawNode_readyWithoutAccept : RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG))
    (wp_RawNode_acceptReady : RawNode.acceptReady.spec (GF := GF) (hG := hG))
    (wp_RawNode_Advance : RawNode.Advance.spec (GF := GF) (hG := hG))
    (wp_RawNode_Tick : RawNode.Tick.spec (GF := GF) (hG := hG))
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_raft_hasLeader : raft.hasLeader.spec (GF := GF) (hG := hG))
    (wp_IsResponseMsg : IsResponseMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_getStatus : getStatus.spec (GF := GF) (hG := hG)) :
    node.run.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

end EtcdGrove
end Perennial
