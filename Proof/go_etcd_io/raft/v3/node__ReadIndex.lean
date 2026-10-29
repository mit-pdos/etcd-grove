/- Lean-first (no Rocq counterpart).

`node.ReadIndex` for a read already deposited (2026-10-27, the node API over an abstract log): as
`node.ReadIndex.spec`, with the read's record `readReq γ c Lc` in place of the fresh token, the update
and the committed log (the adapter deposits the read itself, `InvApi.lean`, and retries reuse
it). The proof is `node.ReadIndex.wp_proof`'s without the deposit. -/
module

public import Spec.go_etcd_io.raft.v3.node__ReadIndex
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasSendR
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Spec.go_etcd_io.raft.v3.node__step
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

What the proof over raft's internals shows, from which the wrapper (below) derives the spec. Its documentation, as when it was the spec (until 2026-10-28):
-/

/-! Lean-first (no Rocq counterpart).

`node.ReadIndex` for a read already deposited (2026-10-27, the node API over an abstract log): as
`node.ReadIndex.spec`, with the read's record `readReq γ c Lc` in place of the fresh token, the update
and the committed log (the adapter deposits the read itself, `InvApi.lean`, and retries reuse
it). The proof is `node.ReadIndex.wp_proof`'s without the deposit. -/



open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
private abbrev node.ReadIndex.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (rctx : GoSlice) (c : List w8) (Lc : List EntryM)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      nodeCtx ctx cd ∗ rctx ↦*□ c ∗ readReq γ.raft c Lc ∗ rdCred γ.raft 1 }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReadIndex"))
      (Val #(interface.ok ctx))) (Val #rctx))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The one-entry batch `[]pb.Entry{{Data: rctx}}`, read-only, then `step` of the request:
a message from the network (`netP`) as far as `run` is concerned. (Raft v3.7, stage R5: the
message is `&pb.Message{Type: pb.MsgReadIndex.Enum(), Entries: []*pb.Entry{{Data: rctx}}}`, its
entry allocated by the slice literal (`wp_slice_literal_ex`), holding the frozen bytes
`rctx ↦*□ c` (D6), frozen, the entries' slice frozen; the message `msgIn ml □`;
`MsgReadIndex.Enum()` is a new callee. Stage R7a: any `nodeCtx`, the error `nodeErr`.) -/
private theorem node.ReadIndex.wp_raw
    (wp_node_step : node.step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.ReadIndex.specRaw (GF := GF) (hG := hG) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  intro γ id n rctx c Lc ctx cd
  wp_start as ⟨#Hnode, #Hctx, #Hrctx, #Hrq, Hcred⟩
  wp_auto
  rw [show raftpb.MsgReadIndex = #((W32 15 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 15) as %pty Hpty
  wp_apply wp_slice_literal_ex (V := Loc)
  wp_alloc l0 as Hl0
  wp_auto
  iexists [l0]
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, Hsl_cap⟩
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue
      [KeyedElement (some (KeyField go!"Data")) (ElementExpression go.byte.SliceType #rctx)])] = 1 := rfl
  simp only [Hsz]
  imod cellRO_alloc $$ Hpty with #cTy
  imod entOwn_of_struct l0 (⟨zero_val _, null, null, null, rctx, slice.nil, 0⟩ : raftpb.Entry)
      (propEntryM c) ⊤ rfl $$ [Hl0] with He
  · iframe Hl0
    simp only [propEntryM]
    iframe Hrctx
    msg_nulls
  imod entOwn_freeze $$ He with #He
  imod ownSlice_persist $$ Hsl with #Hsl
  wp_auto
  ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  imod msgPtsC_of_struct «$a1_ptr» (⟨zero_val _, pty, null, null, null, null, null,
      slice.mk slp (W64 1) (W64 1), null, null, null, null, null, slice.nil, slice.nil, slice.nil,
      0⟩ : raftpb.Message) DFrac.discard false [l0]
      ⟨{ (zero_val MessageM) with Type' := W32 15 }, [propEntryM c], none, [], []⟩ ⊤
      rfl $$ [«$a1»] with Hm
  · iframe «$a1» Hsl Hnilb cTy
    msg_nulls
    simp only [Bool.false_eq_true, ↓reduceIte, snapOpt]
    iframe He
    isplitl []; · iapply entsBig_nil
    isplitl []; · iempintro
    isplitl []; · ipureintro; trivial
    iapply ownSlice_nil
  imod termLB_zero (GF := GF) γ.bud with #Hlb
  imod tickCred_zero (GF := GF) γ.bud with Hz
  have hR : (W32 15 : w32) = MsgReadIndex := rfl
  wp_apply wp_node_step γ id n _ ctx cd $$ [Hm Hcred Hz]
  · iframe Hnode Hctx
    unfold stepP
    ileft
    unfold netP
    ileft
    iexists ⟨{ (zero_val MessageM) with Type' := W32 15 }, [propEntryM c], none, [], []⟩
    isplitl [Hm]
    · simp only [msgIn, show needsCap { (zero_val MessageM) with Type' := W32 15 } = false from rfl]
      iexact Hm
    isplitr
    · ipureintro
      refine ⟨by simp [netStepTypes, MsgReadIndex], fun h => absurd (.inl hR) h, fun _ => rfl,
        fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, rfl⟩
      · exfalso
        rcases h with h | h | h | h | h <;>
          simp [MsgApp, MsgHeartbeat, MsgHeartbeatResp, MsgReadIndexResp, MsgSnap] at h
      · exfalso; simp [MsgAppResp] at h
      · exfalso; simp [MsgTransferLeader] at h
      · exfalso; simp [MsgPreVote] at h
    isplitr
    · ipureintro
      exact ⟨fun h => by exfalso; simp [MsgTransferLeader] at h,
        fun h => by exfalso; simp [MsgSnap] at h⟩
    isplitr
    · imodintro
      iintro %ty %Hty %_Hne
      rw [show mtypeOf (W32 15) = some .readIndex from rfl] at Hty
      cases Hty
      unfold isMessage absMsg absMsgFrom
      iexists propEntryM c, c, Lc
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; rfl
      iframe Hrq
    isplitr
    · imodintro
      iintro %h
      exfalso; simp [MsgSnap] at h
    isplitr
    · iExactEq Hlb; rfl
    rw [ite_eq_left hR]
    isplitl [Hcred]
    · iexact Hcred
    rw [ite_eq_right (show (W32 15 : w32) ≠ MsgTimeoutNow by simp [MsgTimeoutNow])]
    iexact Hz
  iintro %err #Herr
  wp_auto
  iapply HΦ
  iframe Herr
  -/

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `node.ReadIndex.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_ReadIndex_impl
    (hR : EtcdGrove.node.ReadIndex.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.ReadIndex.spec (GF := GF) (hG := hG) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  unfold EtcdGrove.node.ReadIndex.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.isReadCtx EtcdGrove.readCredit
  intro n γ N id rctx c Q ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx, #Hrctx, #Hrc, Hcred⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hf, #Hrn, #Hci⟩
  obtain ⟨Hγr, -⟩ := Hf
  imod api_read_ensure γ N c Q $$ Hci Hrc with ⟨%Lc, #Hrq⟩
  iapply (hR γn id n rctx c Lc ctx cd) $$ [Hcred]
  · iframe Hinit Hrn Hctx Hrctx
    rw [Hγr]
    iframe Hrq
    unfold readCredit readCredits
    iexact Hcred
  iintro !> %err #Herr
  iapply HΦ
  iexact Herr
  -/

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.ReadIndex.wp_proof
    (wp_node_step : node.step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.ReadIndex.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_ReadIndex_impl (node.ReadIndex.wp_raw wp_node_step wp_MessageType_Enum)

end proof

end EtcdGrove
end Perennial
