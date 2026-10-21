/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__witnessDeliver.lean`. Lean-first
(2026-10-20, witness support; the witness case 2026-10-20, W4).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__witnessDeliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.deliverable
public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.witness__Process
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Cluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [StorageModel GF]

theorem KV.witnessDeliver.wp_proof
    (wp_Process : witness.Process.spec (GF := GF) (hG := hG))
    (wp_deliverable : deliverable.spec (GF := GF) (hG := hG))
    (wp_node_Step : node.Step.spec (GF := GF) (hG := hG)) :
    KV.witnessDeliver.spec (GF := GF) (hG := hG) := by
  intro r rd wi γn id n
  wp_start as ⟨#Hw, Hres, #Hnode, #HisNode, Hrw⟩
  iunfold kvWitRes at Hres
  icases Hres with (%Hnil | ⟨%Hf, Hwit⟩)
  · subst Hnil
    wp_auto
    iapply HΦ; unfold kvWitRes; ileft; ipureintro; rfl
  obtain ⟨Hst, Hwnz, Hidw, Hid0⟩ := Hf
  iunfold ownWitnessIT at Hwit
  icases Hwit with ⟨%w, %s, %cq, %pv, %c, %h, %Hwi, Hw0, #Hs, #Hc, #Ht⟩
  subst Hwi
  ihave Hwit := ownWitnessIT_intro γn.raft kvWitN (termLB γn.bud) w s cq pv c h $$ Hw0 Hs Hc Ht
  ihave #Hcinv : raftCommitInv γn.raft $$ []
  · iunfold isNode at HisNode
    icases HisNode with ⟨%nv, %r', %lok, #H⟩
    iNamed H
    iexact Hcinv
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  iunfold readyWit at Hrw
  icases Hrw with ⟨%wms, %μh, Hsl, #Hwm, #Hok⟩
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hwm
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (k : w64) (mv : WitnessMessage),
      "i" ∷ i_ptr ↦ k ∗ "m" ∷ m_ptr ↦ mv ∗ "Hsl" ∷ rd.WitnessMessages' ↦* wms ∗
      "Hwit" ∷ ownWitnessIT γn.raft kvWitN (termLB γn.bud)
        (interface.mkOk (go.GoType.PointerType witness.ty) #w) ∗
      "r" ∷ r_ptr ↦ r ∗ "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (wms.length : Int)⌝)
    $$ [i m Hsl Hwit r]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < wms.length := by word
    obtain ⟨mv0, Hmv0⟩ : ∃ x, wms[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨μ, Hμ⟩ : ∃ x, μh[sint.nat k]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hl2]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rd.WitnessMessages'.len := ⟨Hk.1, by word⟩
    simp only [Hbnd, and_self]
    wp_apply wp_load_slice_index _ (sint.Z k) wms (DFrac.own 1) mv0 Hk.1 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact Hmv0
    ihave #Hm := BigSepL2.bigSepL2_lookup (Φ := fun _ wm μ => ownWMsg (GF := GF) wm μ) Hmv0 Hμ $$ Hwm
    ihave #Hμok := BigSepL.bigSepL_lookup
      (Φ := fun _ μ => iprop(isMessage (GF := GF) γn.raft (wAbs μ) ∗ wReqOk γn id μ)) Hμ $$ Hok
    icases Hμok with ⟨#Hμm, #Hμr⟩
    iunfold wReqOk at Hμr
    icases Hμr with ⟨%Hμf, #Hμt⟩
    try wp_auto
    have Hto : μ.to = γn.raft.reWit := Hμf.2 Hst
    have Hfr : μ.frm ≠ W64 0 := by rw [Hμf.1]; exact Hid0
    ihave #Hreq := isMessage_wAbsReq γn.raft μ $$ Hμm
    ihave #Hreqt : wReqTerm (GF := GF) (termLB γn.bud) μ $$ []
    · unfold wReqTerm; iexact Hμt
    wp_apply Witness.wp_ProcessT wp_Process γn.raft kvWitN (termLB γn.bud)
        ⟨go.GoType.PointerType witness.ty, #w⟩ mv0 μ raftLogN_kvWitN Hwnz Hto Hfr
      $$ [$Hraftinit $Hwit $Hm $Hcinv $Hreq $Hreqt] as %ml %err ⟨Hwit, Hres⟩
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    icases Hres with (⟨%He, %rr, Hro, #Hrok, #Hrt, %Hra⟩ | ⟨%He, %Hn⟩)
    · subst He
      try wp_auto
      cases rr with
      | none =>
        iunfold respOpt at Hro
        icases Hro with %Hml
        subst Hml
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, mv0
        iframe
        ipureintro; constructor <;> word
      | some rr =>
        iunfold respOpt at Hro
        icases msgPtsC_nn $$ Hro with ⟨%Hnn, Hro⟩
        try rw [decide_eq_false Hnn]
        try wp_auto
        wp_apply wp_deliverable ml (DFrac.own 1) DFrac.discard false ⟨rr.1, [], none, rr.2, []⟩
          $$ [$Hro] as %b ⟨Hro, %Hb⟩
        cases b
        · try wp_auto
          wp_for_post
          iframe
          iexists k + W64 1, mv0
          iframe
          ipureintro; constructor <;> word
        try wp_auto
        wp_apply context.wp_Background
        ihave #Hbg := nodeCtx_background (GF := GF) bgCd
        imod stepP_witResp γn id ml rr μ γn.raft.reWit (Hb rfl) Hra Hμf.1 $$ Hrok Hrt Hro with Hstep
        try wp_auto
        wp_apply +noauto wp_node_Step γn id n ml context.backgroundCtxVal bgCd $$ [Hstep] as %err' -
        · iframe
          iframe HisNode Hbg
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, mv0
        iframe
        ipureintro; constructor <;> word
    · cases err with
      | nil => exact absurd rfl He
      | ok ei =>
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, mv0
        iframe
        ipureintro; constructor <;> word
  · iapply HΦ
    unfold kvWitRes
    iright
    iframe Hwit
    ipureintro; exact ⟨Hst, Hwnz, Hidw, Hid0⟩

end proof

end kv
end EtcdGrove
end Perennial
