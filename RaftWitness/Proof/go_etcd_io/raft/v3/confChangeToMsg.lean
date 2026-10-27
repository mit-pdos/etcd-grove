/-
Proof of `Spec/go_etcd_io/raft/v3/confChangeToMsg.lean`. Lean-first (no Rocq counterpart).

raft v3.7 (2026-10-16, stage R5): the message is a fresh `*pb.Message` whose one entry is
allocated by the slice literal (`wp_slice_literal_ex`), its data the frozen bytes
`MarshalConfChange` returned, its `Type` and the message's a fresh cell each (`.Enum()`).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.confChangeToMsg
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.MarshalConfChange
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.EntryType__Enum
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPbMsg
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasSendR
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasMemstorage

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

theorem confChangeToMsg.wp_proof
    (wp_raftpb_MarshalConfChange : raftpb.MarshalConfChange.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG))
    (wp_EntryType_Enum : raftpb.EntryType.Enum.spec (GF := GF) (hG := hG)) :
    confChangeToMsg.spec (GF := GF) (hG := hG) := by
  intro c o dq
  wp_start as Hc
  wp_auto
  wp_apply wp_raftpb_MarshalConfChange $$ [$Hc] as %data %bs ⟨Hc, Hdata, %Hbs⟩
  rw [show raftpb.MsgProp = #((W32 2 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 2) as %pty Hpty
  wp_method_call
  wp_auto
  wp_apply wp_EntryType_Enum as %pety Hpety
  wp_apply wp_slice_literal_ex (V := Loc)
  wp_alloc l0 as Hl0
  wp_auto
  iexists [l0]
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, Hsl_cap⟩
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue
      [KeyedElement (some (KeyField go!"Type")) (ElementExpression raftpb.EntryType.ty.PointerType #pety),
       KeyedElement (some (KeyField go!"Data")) (ElementExpression go.byte.SliceType #data)])] = 1 := rfl
  simp only [Hsz]
  imod cellRO_alloc $$ Hpety with #cY
  imod cellRO_alloc $$ Hpty with #cTy
  imod ownSlice_persist $$ Hdata with #Hdata
  imod entOwn_of_struct l0 (⟨zero_val _, null, null, pety, data, null, slice.nil, 0⟩ : raftpb.Entry)
      (ccEntryM o bs) ⊤ rfl $$ [Hl0] with He
  · iframe Hl0
    simp only [ccEntryM]
    iframe cY Hdata
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  imod entOwn_freeze $$ He with #He
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hml
  generalize «$r0_ptr» = ml at *
  ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  imod msgPtsC_of_struct ml (⟨zero_val _, pty, null, null, null, null, null,
      slice.mk slp (W64 1) (W64 1), null, null, null, null, null, slice.nil, slice.nil, slice.nil,
      0⟩ : raftpb.Message) (DFrac.own 1) false [l0] ⟨propMsgM, [ccEntryM o bs], none, [], []⟩ ⊤ rfl $$ [Hml Hsl] with Hm
  · iframe Hml Hsl Hnilb
    simp only [propMsgM, show MsgProp = W32 2 from rfl]
    iframe cTy
    msg_nulls
    simp only [Bool.false_eq_true, ↓reduceIte, snapOpt]
    iframe He
    isplitl []; · iapply entsBig_nil
    isplitl []; · iempintro
    isplitl []; · ipureintro; trivial
    iapply ownSlice_nil
  imodintro
  iapply HΦ $$ %ml %bs
  iframe Hc
  simp only [msgIn, show needsCap propMsgM = false from rfl]
  isplitl; · iexact Hm
  ipureintro; exact Hbs
end proof

end EtcdGrove
end Perennial
