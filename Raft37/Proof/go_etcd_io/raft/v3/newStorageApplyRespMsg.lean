/-
Proof of `Spec/go_etcd_io/raft/v3/newStorageApplyRespMsg.lean`. Lean-first (stage R5: the old
proof inlined it in `RawNode.acceptReady`'s).
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.newStorageApplyRespMsg
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasRawnodeR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A fresh message, its scalar fields fresh cells, its `Entries` the slice `ents` itself. -/
theorem newStorageApplyRespMsg.wp_proof
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    newStorageApplyRespMsg.spec (GF := GF) (hG := hG) := by
  intro r id ents ce
  wp_start as ⟨#Hid, #Hents⟩
  wp_auto
  rw [show raftpb.MsgStorageApplyResp = #((W32 22 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 22) as %pty Hpty
  rw [show go_etcd_io.raft.v3.LocalApplyThread = #(W64 18446744073709551614) from rfl]
  wp_auto
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v1» with #cTo
  imod cellRO_alloc $$ «$v2» with #cFr
  imod cellRO_alloc $$ «$v3» with #cTe
  simp only [entsRO, entsPts]
  icases Hents with ⟨%els, #Hes, #Hel⟩
  ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  wp_alloc ml as Hml
  imod msgOwn_of_struct ml (⟨zero_val _, pty, «$v1_ptr», «$v2_ptr», «$v3_ptr», null, null, ents,
      null, null, null, null, null, slice.nil, slice.nil, slice.nil, 0⟩ : raftpb.Message) els
      ⟨applyAckM id, ce, none, [], []⟩ ⊤ rfl $$ [Hml] with Hm
  · iframe Hml Hes Hel Hnilb
    simp only [applyAckM, show MsgStorageApplyResp = W32 22 from rfl, snapOpt,
      show EtcdGrove.LocalApplyThread = W64 18446744073709551614 from rfl]
    iframe cTy cTo cFr cTe
    msg_nulls
    isplitl []; · ipureintro; trivial
    iapply ownSlice_nil
  ihave Hm := msgOwn_to_msgIn _ _ (by simp [applyAckM, MsgStorageApplyResp, MsgApp]) $$ Hm
  wp_auto
  iapply HΦ
  iexact Hm

end proof

end EtcdGrove
end Perennial
