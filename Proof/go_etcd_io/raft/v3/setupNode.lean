/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.setupNode

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

/-- `len(peers) == 0` dead (`ps ≠ []`); `NewRawNode` (no error); `Bootstrap` (no error, so no
warning); `newNode`. -/
theorem setupNode.wp_proof
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_RawNode_Bootstrap : RawNode.Bootstrap.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG)) :
    setupNode.spec (GF := GF) (hG := hG) := by
  intro γ c cv lok si σ hs csm R peers dq pv ps ctxs bootLog P1 P2 P3 P4 P5 P6 P7 P8 P9 P11
    P12 P13 P14 P15 P16 Q1 Q2 Q3 Q4 Q5 R1 R2 R3 R4 R5 R6 R7 R8 R9 Hfl0
  wp_start as ⟨Hc, #Hlg, #Hsto, Hown, Hinit, Hpeers, #Hctx, #Hmarshal, Hghost, #Hcommitted⟩
  ihave %Hplen := ownSlice_len $$ Hpeers
  have Hpslen : ps.length = pv.length := by rw [R1, List.length_map]
  have Hpvne : pv ≠ [] := by
    intro h; apply R2; rw [R1, h]; rfl
  wp_auto
  wp_if_destruct
  · exfalso
    have h0 : pv.length = 0 := by
      have := Hplen.1; rw [this]; word
    exact Hpvne (List.eq_nil_of_length_eq_zero h0)
  wp_apply wp_NewRawNode c cv lok si σ hs csm R P1 P2 P3 P4 P5 P6 P7 P8 P9 P11 P12 P13 P14
    P15 P16 (by rw [Q1]; exact List.nodup_nil) (by rw [Q1]; exact List.not_mem_nil)
    (by rw [Q1]; decide) Q2 Q3 Q4 Q5 Hfl0
    $$ [$Hc $Hlg $Hsto $Hown $Hinit] as %rn %err ⟨HR, %s, Hfresh, %Herr⟩
  subst Herr
  wp_auto
  have Hfresh0 : GMap.listToSet csm.Voters' = ∅ := by rw [Q1]; rfl
  ihave Hfresh' : rawNodeFresh rn cv.ID' si ∅ cv.StepDownOnRemoval' cv.PreVote' s $$ [Hfresh]
  · rw [← Hfresh0]; iexact Hfresh
  wp_apply wp_RawNode_Bootstrap γ rn cv.ID' si cv.StepDownOnRemoval' cv.PreVote' s peers dq pv ps ctxs
    bootLog R1 R2 R3 R4 R5 R6 R7 R8 R9
    $$ [$Hfresh' $Hpeers $Hctx $Hmarshal $Hghost $Hcommitted] as %err2 ⟨%Herr2, Hrn, Hpeers⟩
  subst Herr2
  wp_auto
  wp_apply wp_newNode rn as %nv ⟨%Hnvrn, Hchans⟩
  iapply HΦ
  iframe HR
  iexists nv, rn
  iframe n Hchans Hrn Hpeers
  ipureintro; exact Hnvrn

end proof

end EtcdGrove
end Perennial
