/- Proof of `Spec/go_etcd_io/raft/v3/node__ProposeConfChange.lean`, Lean-first (2026-10-13). -/
module

public import Spec.go_etcd_io.raft.v3.node__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.confChangeToMsg
public import Spec.go_etcd_io.raft.v3.node__Step

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

theorem node.ProposeConfChange.wp_proof
    (wp_confChangeToMsg : confChangeToMsg.spec (GF := GF) (hG := hG))
    (wp_node_Step : node.Step.spec (GF := GF) (hG := hG)) :
    node.ProposeConfChange.spec (GF := GF) (hG := hG) := by
  intro γ id n c o dq
  wp_start as ⟨#Hnode, Hc⟩
  wp_auto
  wp_apply wp_confChangeToMsg c (some o) dq $$ [$Hc] as %esl %data %bs ⟨Hc, Hes, Hcap, Hdata, %Hbs⟩
  ipersist Hdata
  imod node_read_register γ id n data bs ⊤ CoPset.subseteq_top $$ Hnode Hdata with #Hpd
  ihave #Hent := entData_cc γ.raft o data bs Hbs $$ Hpd
  wp_apply wp_node_Step γ id n (ccPropMsg esl) $$ [$Hnode Hes Hcap]
  · unfold stepP
    iright
    unfold fwdP
    isplitr
    · ipureintro; rfl
    iexists [ccEntry (some o) data], []
    ihave Hes : (ccPropMsg esl).Entries' ↦* [ccEntry (some o) data] $$ [Hes]
    · rw [show (ccPropMsg esl).Entries' = esl from rfl]; iexact Hes
    ihave Hcap : ownSliceCap raftpb.Entry (ccPropMsg esl).Entries' (DFrac.own 1) $$ [Hcap]
    · rw [show (ccPropMsg esl).Entries' = esl from rfl]; iexact Hcap
    iframe Hes Hcap
    isplitr
    · simp only [ccPropMsg]; iapply ownSlice_nil
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
