/-
Port of election_proof/proof_logSliceFromMsgApp.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Proof.go_etcd_io.raft.v3.LemmasStepR
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
    (wp_Message_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG)) :
    logSliceFromMsgApp.spec (GF := GF) (hG := hG) := by
  intro p cap c Hcs
  simp only [MsgC.model, MsgFC.msgM]
  wp_start as Hm
  wp_auto
  have h := msgPtsCC_readE (GF := GF) p cap c Hcs DFrac.discard DFrac.discard
  rw [discard_op_discard] at h
  icases h $$ Hm with ⟨Hh, Hback⟩
  wp_apply wp_Message_GetTerm.1 p _ _ _ _ $$ [$Hh] as Hh
  wp_apply wp_Message_GetLogTerm.1 p _ _ _ _ $$ [$Hh] as Hh
  wp_apply wp_Message_GetIndex.1 p _ _ _ _ $$ [$Hh] as Hh
  ihave Hm := Hback $$ Hh
  icases msgPtsCC_acc_entries p _ _ _ c $$ Hm with ⟨%es, %els, %Hnn, HEs, Hes, #Hents, Hcap, Hclose⟩
  wp_apply wp_Message_GetEntries_field p _ es Hnn $$ [$HEs] as HEs
  iapply HΦ $$ %es %els
  iframe Hes Hents Hcap
  iintro Hes
  ihave Hm := Hclose $$ %els %c.f.entries %false HEs Hes Hents []
  · simp only [Bool.false_eq_true, ↓reduceIte]; iempintro
  obtain ⟨f, rs⟩ := c
  simp only [MsgC.f, MsgC.resps]
  iexact Hm

end proof

end EtcdGrove
end Perennial
