/-
# Raft's implementation of its signature (prototype, 2026-10-26)

`raftSigImpl : RaftSig GF` (`Spec/go_etcd_io/raft/v3/Sig.lean`): the signature's types and
predicates defined by raft's proof (the committed log `rLog` is the client's half of the
invariant's ghost variable, its lower bound `rLogLb` the committed log's `isCommitted`, the node
`isNode`, ...), the laws proved from the protocol's lemmas, and the specs stated over the
signature proved from raft's at this instance. A proof outside raft does not import this module;
a closed theorem does, to apply its client's results to the instance.
-/
module

public import Spec.go_etcd_io.raft.v3.Sig
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Spec.go_etcd_io.raft.v3.node__Propose
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
-- the definitions behind the API's sealed predicates (`isNode`), which the instance's laws open
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section impl
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Raft's implementation of `RaftSig`. -/
instance raftSigImpl : RaftSig GF where
  Names := RaftNames
  NodeNames := NodeNames
  raft γ := γ.raft
  N := raftN
  inv := raftCommitInv
  inv_persistent _ := inferInstance
  isNode := isNode
  isNode_persistent _ _ _ := inferInstance
  isNode_inv γ id n := by
    iintro #Hnode
    open_node Hnode
    iexact Hcinv
  rLog := rLog
  rLog_timeless _ _ := inferInstance
  rLogLb := isCommitted
  rLogLb_persistent _ _ := inferInstance
  rLogLb_mono γ l1 l2 h := by
    iintro H
    iapply isCommitted_mono γ l1 l2 h $$ H
  rLogLb_agree γ l1 l2 := by
    iintro ⟨H1, H2⟩
    iapply isCommitted_agree γ l1 l2 $$ H1 H2
  rLog_lb γ L E HE := by
    iintro ⟨#Hi, H⟩
    iapply rLog_committed γ L E (raftLogN_of HE) $$ Hi H
  entData := entDataIs
  entData_persistent _ _ _ := inferInstance
  propFresh := propFresh
  propReg := propIs
  propReg_persistent _ _ _ := inferInstance
  prop_register γ d Q E HE := by
    iintro ⟨#Hi, H⟩
    iapply prop_register γ E d Q HE $$ Hi H
  prop_collect γ d Q L m e E HE Hm := by
    iintro ⟨#Hi, #Hp, #Hc, #Hd⟩
    iapply prop_collect γ E d Q L m e HE Hm $$ Hi Hp Hc Hd
  isReadyChan := isReadyChan
  isReadyChan_persistent _ _ := inferInstance
  nodeDriver := nodeDriver
  nodeDriverBusy γ id n ds es p' := nodeDriverBusy γ id n ds es p'
  readyData γ rd d ce es p p' := iprop(∃ ms, _root_.Perennial.EtcdGrove.readyData γ rd d ce es ms p p')
  readyData_committed γ rd d ce es p p' := by
    iintro ⟨%ms, Hd⟩
    unfold _root_.Perennial.EtcdGrove.readyData
    icases Hd with ⟨Hce, #Hcom, Hrest⟩
    isplitl [Hce Hrest]
    · iexists ms
      iframe Hce Hcom Hrest
    · iexact Hcom
  noSnap γ := γ.raft.reNoSnap = true ∨ γ.mode.isDyn = true ∨ γ.snapIn = false

/-! ## The specs over the signature, at raft's instance, from raft's specs -/

theorem node.Propose.wp_specS (H : node.Propose.spec (GF := GF) (hG := hG)) :
    node.Propose.specS (S := raftSigImpl (GF := GF)) := by
  intro γ id n data_sl data Q ctx cd
  exact H γ id n data_sl data Q ctx cd

theorem node.Ready.wp_specS (H : node.Ready.spec (GF := GF) (hG := hG)) :
    node.Ready.specS (S := raftSigImpl (GF := GF)) := by
  intro γ id n
  exact H γ id n

/-- The instance's `readyData` from raft's (its messages hidden). -/
theorem raftSigImpl_readyData (γ : NodeNames) (rd : Ready) (d ce es : List EntryM)
    (ms : List QMsg) (p p' : HardStateM) :
    _root_.Perennial.EtcdGrove.readyData (GF := GF) γ rd d ce es ms p p' ⊢
      RaftSig.readyData (self := raftSigImpl (GF := GF)) γ rd d ce es p p' :=
  (by iintro H; iexists ms; iexact H :
    _root_.Perennial.EtcdGrove.readyData (GF := GF) γ rd d ce es ms p p' ⊢
      iprop(∃ ms', _root_.Perennial.EtcdGrove.readyData γ rd d ce es ms' p p'))

theorem node.readyRecv.wp_specS : node.readyRecv.specS (S := raftSigImpl (GF := GF)) := by
  intro γ id n ch ds p Hns
  iintro %Φ Hpre HΦ
  iapply node_ready_receive_ns γ id n ch ds p Hns $$ Hpre
  iintro !> %rd ⟨%ce, %es, %ms, %p', Hd, Hb⟩
  iapply HΦ
  iexists ce, es, p'
  iframe Hb
  iapply raftSigImpl_readyData $$ Hd

end impl

end EtcdGrove
end Perennial
