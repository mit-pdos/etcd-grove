/- Proof of `Spec/go_etcd_io/raft/v3/node__ProposeConfChange.lean`, Lean-first (2026-10-13). -/
module

public import Spec.go_etcd_io.raft.v3.node__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.confChangeToMsg
public import Spec.go_etcd_io.raft.v3.node__Step
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

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `confChangeToMsg`, then `Step` of the proposal, forwarded (`fwdP`). (Raft v3.7, stage R5, D6:
the message `msgIn ml 1` from `confChangeToMsg`, its entry `ccEntryM (some o) bs` holding the
bytes, so no recording of the data is needed. 2026-10-27: the proposal tracked under its key,
`cc_propose_ghost`. Stage R7a: any `nodeCtx`, the error
`nodeErr`.) -/
theorem node.ProposeConfChange.wp_proof
    (wp_confChangeToMsg : confChangeToMsg.spec (GF := GF) (hG := hG))
    (wp_node_Step : node.Step.spec (GF := GF) (hG := hG)) :
    node.ProposeConfChange.spec (GF := GF) (hG := hG) := by
  intro γ id n c o dq ctx cd
  wp_start as ⟨#Hnode, #Hctx, Hc, Harg⟩
  wp_auto
  wp_apply wp_confChangeToMsg c (some o) dq $$ [$Hc] as %ml %bs ⟨Hc, Hm, %Hbs⟩
  -- (2026-10-27) the proposal's ghost work: tracked under its key, its ticket on the entry
  ihave #Hcinv := isNode_commitInv γ id n $$ Hnode
  imod cc_propose_ghost γ.raft o bs Hbs $$ Hcinv Harg with ⟨#Hent, Htk⟩
  wp_apply wp_node_Step γ id n ml ctx cd $$ [$Hnode $Hctx Hm Htk]
  · unfold stepP
    iright
    unfold fwdP
    iexists ⟨propMsgM, [ccEntryM (some o) bs], none, [], []⟩
    iframe Hm
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · unfold isMessage absMsg absMsgFrom
      isplitr
      · ipureintro
        exact ⟨rfl, List.cons_ne_nil _ _, by simp⟩
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => propData (GF := GF) γ.raft e)).2
      iexact Hent
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entTk (GF := GF) γ.raft e)).2
    iexact Htk
  iintro %err #Herr
  wp_auto
  iapply HΦ
  iframe Hc
  iexact Herr

end proof

end EtcdGrove
end Perennial
