/- Lean-first (no Rocq counterpart).

#33 S4: **`cloneMsg.law` from `proto.Clone`'s trust boundary** (`proto.ClonePb.spec`, at the
registered `*raftpb.Message` type `pbMessageC`, `pbMessageC_reg`), as rafthttp's
`streamWriter.run` clones its heartbeat: a frozen message without responses is read-only at its
content (`msgPtsCC_msgRoC`), and its clone is exactly that content, since a message without
responses marshals (`MsgMarshals`). The Antithesis Link passes `cloneMsg_law_of proto.wp_ClonePb`
to `Cluster.send`'s and `node.sendMsg`'s proofs.

#33 parity B1: `cloneMsg.law` is stated here (S4's `DrainSendWp`, where it was, is gone), with the
ownership steps around a clone: a sent message frozen read-only (`msgPtsCC_send_freeze`, the form
`cloneMsg.law` takes), and a clone as an in-flight message (`msgPtsCC_clone_net`, `netMsg_of_clone`,
`netXMsg_of_clone`); a read credit for a time receipt (`rdCred_of_receipt`, a `MsgReadIndex`'s
receiver's).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun
public import Proof.go_etcd_io.raft.v3.MsgOwnZ
public import Proof.go_etcd_io.raft.v3.MsgRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PerTypeMessage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Spec.google_golang_org.protobuf.proto.ClonePb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section law
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`proto.Clone` of a `raftpb.Message`** (the registered instance's `proto.ClonePb.spec`: with
`pbMessageC_reg`, a frozen message with no responses, `msgPtsCC_msgRoC`, is cloned exactly, as it
marshals): a fresh message owned at the same content, with its capacity. -/
abbrev cloneMsg.law : Prop :=
  ∀ (l : Loc) (c : MsgC), c.resps = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
      msgPtsCC l DFrac.discard DFrac.discard false c }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l)))
  {{ (l' : Loc), RET #(interface.mkOk (go.GoType.PointerType raftpb.Message.ty) #l');
      msgPtsCC l' (DFrac.own 1) (DFrac.own 1) true c }}

/-- **`cloneMsg.law`**, from `proto.Clone`'s spec at the registered message type. -/
theorem cloneMsg_law_of (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG)) :
    cloneMsg.law (GF := GF) (hG := hG) := by
  intro l c hr
  iintro %Φ ⟨#Hpkg, #Hl⟩ HΦ
  have wpC := wp_Clone pbMessageC pbMessageC_reg l c
  simp only [pbMessageC_ty, pbMessageC_roC, pbMessageC_decC, pbMessageC_eqv, pbMessageC_modelOf,
    pbMessageC_C, pbMessageC_marshals] at wpC
  ihave #Hro := msgPtsCC_msgRoC l c hr $$ Hl
  wp_apply wpC $$ [] as %l' ⟨%c', Hl', %Heqv⟩
  · iexact Hro
  have hm : MsgMarshals c.model := by
    simp only [MsgMarshals, MsgC.model, hr, List.map_nil]
  rw [Heqv.2.2 hm]
  iapply HΦ $$ Hl'

end law

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A sent message, frozen** (`sendMsg`'s ownership to `cloneMsg.law`'s): its entries slice
frozen, its capacity dropped, then read-only. -/
theorem msgPtsCC_send_freeze (l : Loc) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l (DFrac.own 1) DFrac.discard cap c ⊢
      |==> msgPtsCC l DFrac.discard DFrac.discard false c := by
  iintro H
  imod msgPtsCC_freeze l _ _ cap c $$ H with H
  iapply msgPtsCC_persist l _ c $$ H

/-- **A clone as an in-flight message's ownership**: its entries slice frozen, the capacity flag
any (here the network's `needsCap`). -/
theorem msgPtsCC_clone_net (l : Loc) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l (DFrac.own 1) (DFrac.own 1) true c ⊢
      |==> msgPtsCC l (DFrac.own 1) DFrac.discard cap c := by
  iintro H
  imod msgPtsCC_persist_els l _ _ true c $$ H with H
  imodintro
  iapply msgPtsCC_cap_any l _ _ cap c $$ H

end own

section net
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A stepped message's read credit** (`RawNode.Step`'s `Hcred`): for a `MsgReadIndex`, one for a
time receipt (`rdMinter`); otherwise none. -/
theorem rdCred_of_receipt (γ : AntNames) (st : MsgSt) :
    ⊢ rdMinter (GF := GF) γ -∗ ⧗ 1 ={⊤}=∗
      rdCred γ.raft.raftNames (if st.msg.Type' = MsgReadIndex then 1 else 0) := by
  iintro Hm H1
  by_cases h : st.msg.Type' = MsgReadIndex
  · rw [if_pos h]
    iunfold rdMinter at Hm
    iapply Hm $$ H1
  · rw [if_neg h]
    iclear H1 Hm
    imod rdCred_zero_upd (GF := GF) γ.raft.raftNames with H0
    imodintro; iexact H0

/-- **A clone of an in-flight protocol message is one** (`netMsg`), with the original's facts. -/
theorem netMsg_of_clone (γ : AntNames) (l : Loc) (st : MsgSt) (m : Msg) (c : MsgC)
    (hc : c.model = st ∧ c.csUfNil) (hf : NetFacts γ.R st m) :
    msgPtsCC (GF := GF) l (DFrac.own 1) (DFrac.own 1) true c ∗ □ isMessage γ.raft.raftNames m ∗
        rnTermLB γ.raft st.msg.Term' ∗ sentW γ m ⊢ |==> netMsg γ l st m := by
  iintro ⟨H, #Hism, Htlb, Hsent⟩
  imod msgPtsCC_clone_net l (needsCap st.msg) c $$ H with H
  imodintro
  iunfold netMsg
  iframe Htlb Hsent Hism
  isplitl [H]
  · iexists c; iframe H; ipureintro; exact hc
  ipureintro; exact hf

/-- **A clone of an in-flight transfer message is one** (`netXMsg`), with the original's facts
(a stamped `MsgTransferLeader`'s destination its term's leader, a `MsgTimeoutNow`'s an
acknowledgement at its term). -/
theorem netXMsg_of_clone (γ : AntNames) (l : Loc) (st : MsgSt) (x : XMsg) (c : MsgC)
    (hc : c.model = st ∧ c.csUfNil) (hf : XNetFacts γ.R st x) :
    msgPtsCC (GF := GF) l (DFrac.own 1) (DFrac.own 1) true c ∗
        rnTermLB γ.raft st.msg.Term' ∗ xsentW γ x ∗
        □ (⌜st.msg.Type' = MsgTransferLeader ∧ st.msg.Term' ≠ W64 0⌝ -∗
          isLeader γ.raft.raftNames st.msg.To' st.msg.Term') ∗
        □ (⌜st.msg.Type' = MsgTimeoutNow⌝ -∗
          ∃ i : w64, ⌜uint.Z i ≠ 0⌝ ∗ isAcked γ.raft.raftNames st.msg.To' st.msg.Term' i) ⊢
      |==> netXMsg γ l st x := by
  iintro ⟨H, Htlb, Hsent, #Hld, #Hack⟩
  imod msgPtsCC_clone_net l (needsCap st.msg) c $$ H with H
  imodintro
  iunfold netXMsg
  iframe Htlb Hsent Hld Hack
  isplitl [H]
  · iexists c; iframe H; ipureintro; exact hc
  ipureintro; exact hf

end net

end AntHarness
end EtcdGrove
end Perennial
