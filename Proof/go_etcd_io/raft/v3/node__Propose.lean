/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Propose
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasSendR
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Spec.go_etcd_io.raft.v3.node__stepWait

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

/-- The one-entry batch `[]pb.Entry{{Data: data}}`, then `stepWait`. (Raft v3.7, stage R5: the
message is `&pb.Message{Type: pb.MsgProp.Enum(), Entries: []*pb.Entry{{Data: data}}}`, its entry
allocated by the slice literal (`wp_slice_literal_ex`, as `confChangeToMsg`), holding the frozen
bytes `data_sl ↦*□ data` (D6: `propEntryM data`, `data ≠ []` for `node_propose_ghost`), frozen
(`entOwn_freeze`); the message owned (`msgIn ml 1`); `MsgProp.Enum()` is a new callee. Stage R7a:
any `nodeCtx`, the error `propErr`.) -/
theorem node.Propose.wp_proof
    (wp_node_stepWait : node.stepWait.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.Propose.spec (GF := GF) (hG := hG) := by
  intro γ id n data_sl data Q fresh once ctx cd
  wp_start as ⟨#Hnode, #Hctx, #Hdata, %Hne, Harg⟩
  wp_auto
  -- the proposal's ghost work (2026-10-10): the update deposited
  imod node_propose_ghost γ id n data Q fresh once ⊤ CoPset.subseteq_top Hne $$ Hnode Harg
    with ⟨#Hent, Htk, Hres⟩
  rw [show raftpb.MsgProp = #((W32 2 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 2) as %pty Hpty
  wp_apply wp_slice_literal_ex (V := Loc)
  wp_alloc l0 as Hl0
  wp_auto
  iexists [l0]
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, Hsl_cap⟩
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue
      [KeyedElement (some (KeyField go!"Data")) (ElementExpression go.byte.SliceType #data_sl)])] = 1 := rfl
  simp only [Hsz]
  imod cellRO_alloc $$ Hpty with #cTy
  imod entOwn_of_struct l0 (⟨zero_val _, null, null, null, data_sl, slice.nil, 0⟩ : raftpb.Entry)
      (propEntryM data) ⊤ rfl $$ [Hl0] with He
  · iframe Hl0
    simp only [propEntryM]
    iframe Hdata
    msg_nulls
  imod entOwn_freeze $$ He with #He
  wp_auto
  ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  imod msgPtsC_of_struct «$a1_ptr» (⟨zero_val _, pty, null, null, null, null, null,
      slice.mk slp (W64 1) (W64 1), null, null, null, null, null, slice.nil, slice.nil, slice.nil,
      0⟩ : raftpb.Message) (DFrac.own 1) false [l0] ⟨propMsgM, [propEntryM data], none, [], []⟩ ⊤
      rfl $$ [«$a1» Hsl] with Hm
  · iframe «$a1» Hsl Hnilb
    simp only [propMsgM, show MsgProp = W32 2 from rfl]
    iframe cTy
    msg_nulls
    simp only [Bool.false_eq_true, ↓reduceIte, snapOpt]
    iframe He
    isplitl []; · iapply entsBig_nil
    isplitl []; · iempintro
    isplitl []; · ipureintro; trivial
    iapply ownSlice_nil
  wp_apply wp_node_stepWait γ id n «$a1_ptr» data ctx cd $$ [$Hnode $Hctx Hm $Hent $Htk]
  · simp only [msgIn, show needsCap propMsgM = false from rfl]
    iexact Hm
  iintro %err #Herr
  wp_auto
  iapply HΦ
  iframe Hres
  iexact Herr

end proof

end EtcdGrove
end Perennial
