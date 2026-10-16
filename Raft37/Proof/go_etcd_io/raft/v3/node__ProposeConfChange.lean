/- Proof of `Raft37/Spec/go_etcd_io/raft/v3/node__ProposeConfChange.lean`, Lean-first (2026-10-13). -/
module

public import Raft37.Spec.go_etcd_io.raft.v3.node__ProposeConfChange
public import Raft37.Spec.go_etcd_io.raft.v3.confChangeToMsg
public import Raft37.Spec.go_etcd_io.raft.v3.node__Step

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

/-- `confChangeToMsg`, then `Step` of the proposal, forwarded (`fwdP`). (Raft v3.7, stage R5, D6:
the message `msgIn ml 1` from `confChangeToMsg`, its entry `ccEntryM (some o) bs` holding the
bytes, so no recording of the data is needed (`entData_cc`).) -/
theorem node.ProposeConfChange.wp_proof
    (wp_confChangeToMsg : confChangeToMsg.spec (GF := GF) (hG := hG))
    (wp_node_Step : node.Step.spec (GF := GF) (hG := hG)) :
    node.ProposeConfChange.spec (GF := GF) (hG := hG) := by
  intro γ id n c o dq Hok
  wp_start as ⟨#Hnode, Hc⟩
  wp_auto
  wp_apply wp_confChangeToMsg c (some o) dq $$ [$Hc] as %ml %bs ⟨Hc, Hm, %Hbs⟩
  ihave #Hent := entData_cc γ.raft o bs Hbs (Hok bs Hbs)
  wp_apply wp_node_Step γ id n ml $$ [$Hnode Hm]
  · unfold stepP
    iright
    unfold fwdP
    iexists ⟨propMsgM, [ccEntryM (some o) bs], none, [], []⟩
    iframe Hm
    isplitr
    · ipureintro; rfl
    unfold isMessage absMsg absMsgFrom
    isplitr
    · ipureintro
      exact ⟨rfl, List.cons_ne_nil _ _, by simp⟩
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entData (GF := GF) γ.raft e)).2
    iexact Hent
  iintro %err -
  wp_auto
  iapply HΦ
  iexact Hc

end proof

end EtcdGrove
end Perennial
