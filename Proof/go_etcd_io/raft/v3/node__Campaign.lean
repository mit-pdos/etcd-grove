/- Lean-first (no Rocq counterpart), 2026-10-29 (stage U7). -/
module

public import Spec.go_etcd_io.raft.v3.node__Campaign
public import Proof.ReceiptTactics
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasNodeR
public import Spec.go_etcd_io.raft.v3.node__step
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Perennial.Proof.context
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file) -/

/-! Lean-first (no Rocq counterpart).

## `node.Campaign(ctx)` (node.go:467), 2026-10-29, stage U7

From any goroutine: `step` of `pb.Message{Type: MsgHup}` (`netP_hup`: `netP`'s internal
disjunct, the message with a tick credit), which `run` steps as `RawNode.Campaign` does
(`wp_rn_raft_Step_hup`), the credit raising the term ceiling past the campaign's term. The credit
is a time receipt of `Campaign`'s own first method resolution (`MsgHup.Enum()`'s), as `Tick`'s.
The error says only whether the message reached `run` (`nodeErr`). -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the header above. -/
private abbrev node.Campaign.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗ nodeCtx ctx cd }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Campaign"))
      (Val #(interface.ok ctx)))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `step` of the literal message, with its tick credit (`netP_hup`). -/
private theorem node.Campaign.wp_raw
    (wp_node_step : node.step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.Campaign.specRaw (GF := GF) (hG := hG) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  intro γ id n ctx cd
  wp_start as ⟨#Hnode, #Hctx⟩
  -- the campaign's tick credit, a time receipt of a Go step of its own (`MsgHup.Enum()`'s
  -- resolution)
  rw [show raftpb.MsgHup = #((W32 0 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_take_receipt as Htc
  wp_apply wp_MessageType_Enum (W32 0)
  iintro %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_auto
  imod msgIn_of_scalar_struct «$a1_ptr» pty null null null null null null null null null
      { (zero_val MessageM) with Type' := W32 0 } ⊤ $$ [«$a1»] with Hmsg
  · iframe «$a1» cTy
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_node_step γ id n _ ctx cd $$ [Hmsg Htc]
  · iframe Hnode Hctx
    unfold stepP
    ileft
    iapply netP_hup γ id _ $$ [Hmsg] [Htc]
    · iExactEq Hmsg
      rfl
    unfold tickCred
    iexact Htc
  iintro %err #Herr
  wp_auto
  iapply HΦ
  iexact Herr
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

/-- `node.Campaign.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_Campaign_impl
    (hS : EtcdGrove.node.Campaign.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.Campaign.spec (GF := GF) (hG := hG) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  unfold EtcdGrove.node.Campaign.spec EtcdGrove.Cluster EtcdGrove.isNode
  intro n γ N id ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, -, #Hrn, -⟩
  iapply (hS γn id n ctx cd) $$ []
  · iframe Hinit Hrn Hctx
  iexact HΦ
  -/

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.Campaign.wp_proof
    (wp_node_step : node.step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.Campaign.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_Campaign_impl (node.Campaign.wp_raw wp_node_step wp_MessageType_Enum)

end proof

end EtcdGrove
end Perennial
