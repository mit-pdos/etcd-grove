/-
Lean-first (no Rocq counterpart): the proof of `makeTracingMessage`
(`Spec/go_etcd_io/raft/v3/makeTracingMessage.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.makeTracingMessage
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetEntries
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__String
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetVote
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetRejectHint
public import Spec.strconv.FormatUint

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- The struct literal: every getter in turn, the three numbers formatted. -/
local macro "mtm_tail" : tactic => `(tactic| (
  wp_apply wp_GetType.1 $$ [Hm] as Hm
  (· iexact Hm)
  try wp_auto
  wp_apply wp_TypeString
  wp_apply wp_GetTerm.1 $$ [Hm] as Hm
  (· iexact Hm)
  wp_apply wp_GetFrom.1 $$ [Hm] as Hm
  (· iexact Hm)
  wp_apply wp_FormatUint
  · ipureintro; word
  iintro %sfr %Hsfr
  try wp_auto
  wp_apply wp_GetTo.1 $$ [Hm] as Hm
  (· iexact Hm)
  wp_apply wp_FormatUint
  · ipureintro; word
  iintro %sto %Hsto
  try wp_auto
  wp_apply wp_GetCommit.1 $$ [Hm] as Hm
  (· iexact Hm)
  wp_apply wp_GetVote.1 $$ [Hm] as Hm
  (· iexact Hm)
  wp_apply wp_FormatUint
  · ipureintro; word
  iintro %svo %Hsvo
  try wp_auto
  wp_apply wp_GetReject.1 $$ [Hm] as Hm
  (· iexact Hm)
  wp_apply +noauto wp_GetRejectHint.1 $$ [Hm] as Hm
  (· iexact Hm)
  iapply wp_fupd
  try wp_auto))

theorem makeTracingMessage.wp_proof
    (wp_GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG))
    (wp_GetEntries : raftpb.Message.GetEntries.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetSnapshot : raftpb.Message.GetSnapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_MdGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_TypeString : raftpb.MessageType.String.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.Message.GetCommit.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.Message.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG))
    (wp_GetRejectHint : raftpb.Message.GetRejectHint.spec (GF := GF) (hG := hG))
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    makeTracingMessage.spec (GF := GF) (hG := hG) := by
  constructor
  · wp_start
    wp_auto
    iapply HΦ
    itrivial
  intro l dq dqe cap ms
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_start as Hm
  ihave %Hnn : ⌜l ≠ null⌝ $$ [Hm]
  · iunfold msgPtsC at Hm; iNamed Hm; ipureintro; exact Hnn
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_GetLogTerm.1 $$ [$Hm] as Hm
  wp_apply wp_GetEntries.1 $$ [$Hm] as %es %els ⟨Hes, #Hents, Hcap, Hback⟩
  ihave %Hlen := ownSlice_len $$ Hes
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hents
  try wp_auto
  ihave Hm := Hback $$ %cap %els %ms.ents Hes Hents Hcap
  wp_apply wp_GetIndex.1 $$ [$Hm] as Hm
  wp_apply wp_GetType.1 $$ [$Hm] as Hm
  by_cases hs : ms.msg.Type' = W32 7
  · rw [decide_eq_true hs]
    wp_auto
    wp_apply wp_GetSnapshot.1 $$ [$Hm] as %ps ⟨Hsn, Hsback⟩
    generalize hsn : ms.snap = sn at *
    cases sn with
    | none =>
      simp only [snapOpt]
      icases Hsn with %Hps
      subst Hps
      wp_apply wp_GetMetadata.2
      wp_apply (wp_MdGetIndex null dq ⟨⟨[], [], [], [], false⟩, W64 0, W64 0⟩) $$ []
      · iunfold smOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
      iintro -
      ihave Hm := Hsback $$ []
      · ipureintro; trivial
      try wp_auto
      mtm_tail
      have hms : ({ msg := ms.msg, ents := ms.ents, snap := none, ctx := ms.ctx, resps := ms.resps } : MsgSt) = ms := by
        cases ms; simp_all
      rw [hms]
      ipersist «$r0»
      imodintro
      iapply HΦ
      iframe Hm
      simp only [tracingMsgRep]
      iexists _
      iframe «$r0»
      ipureintro
      simp only [traceMsgOf, hs, decStr, snapIdx, hsn, Hsfr, Hsto, Hsvo]
      trivial
    | some sv =>
      simp only [snapOpt]
      wp_apply wp_GetMetadata.1 $$ [$Hsn] as %pm ⟨Hmd, Hmdb⟩
      wp_apply wp_MdGetIndex $$ [$Hmd] as Hmd
      ihave Hsn := Hmdb $$ Hmd
      ihave Hm := Hsback $$ Hsn
      try wp_auto
      mtm_tail
      have hms : ({ msg := ms.msg, ents := ms.ents, snap := some sv, ctx := ms.ctx, resps := ms.resps } : MsgSt) = ms := by
        cases ms; simp_all
      rw [hms]
      ipersist «$r0»
      imodintro
      iapply HΦ
      iframe Hm
      simp only [tracingMsgRep]
      iexists _
      iframe «$r0»
      ipureintro
      simp only [traceMsgOf, hs, decStr, snapIdx, hsn, Hsfr, Hsto, Hsvo]
      trivial
  · rw [decide_eq_false hs]
    try wp_auto
    mtm_tail
    ipersist «$r0»
    imodintro
    iapply HΦ
    iframe Hm
    simp only [tracingMsgRep]
    iexists _
    iframe «$r0»
    ipureintro
    have hlen : es.len = W64 ms.ents.length := by word
    have hs' : ¬ ms.msg.Type' = MsgSnap := hs
    simp only [traceMsgOf, hs', ↓reduceIte, decStr, hlen, Hsfr, Hsto, Hsvo]
    trivial

end proof

end EtcdGrove
end Perennial
