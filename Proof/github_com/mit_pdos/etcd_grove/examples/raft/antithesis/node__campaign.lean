/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__campaign.lean`: the term ceiling
raised by a receipt (`rnBudget_spend`, the receipt of `Campaign`'s resolution), `RawNode.Campaign`
(`CampaignEndR`; its error, `nil`, dropped), the view noted (`view_input`), the drain from its loop head (`Reach.input`, through
`input`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__campaign
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__input
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput
public import Proof.ReceiptTactics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem node.campaign.wp_proof
    (wp_Campaign : RawNode.Campaign.apiSpec (GF := GF) (hG := hG))
    (wp_input : node.input.spec (GF := GF) (hG := hG))
    (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (h_tc : rawNode_term_tc.law (GF := GF) (hG := hG))
    (h_raise : rawNode_raise_tc.law (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_spend : rnBudget_spend.law (GF := GF) (hG := hG))
    (h_vu : view_update.law (GF := GF) (hG := hG))
    (h_lo : nodeLive_over.law (GF := GF) (hG := hG))
    (msk : AntSim.SimMask) (h_quiet : antSim_quiet_in.law msk) (h_mask : runInMask.law msk)
    (h_camp : msk.campaign = true) :
    node.campaign.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v q
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok, %Hb1⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  icases nodeOwn_idle_open h_bp c γ j n v $$ Hown with
    ⟨%rn, %rs, Hrnf, Hraw, Htc, #Hb, %Hst, Hcause, Hv, Hl, %Hpr, Hclose⟩
  obtain ⟨hrv, hI, hP, hN, hk⟩ := Hpr
  icases h_wf _ _ _ _ _ _ _ $$ Hraw with ⟨%Hwf, Hraw⟩
  icases h_tc _ _ _ _ _ _ _ $$ Hraw with ⟨%Htcle, Hraw⟩
  wp_take_receipt as Hrc
  imod h_spend γ.raft rs.tc ⊤ (by solve_ndisj) $$ Hb Hrc Htc with ⟨%Hbd, Htc⟩
  ihave Hraw := h_raise _ _ _ _ _ _ _ (rs.tc + W64 1) (by word) $$ Hraw
  wp_apply wp_Campaign γ.raft.raftNames rn (AntSim.nodeId j) { rs with tc := rs.tc + W64 1 } v.r []
      v.r.p.log.length (by simp only; rw [← Hwf.2.2]; word) hrv.2.2.2.2.2
      Hst.1 $$ [$Hrpkg $Hraw] as %err %t %r' %ip' ⟨Hraw, %Ht, %Herr, %Hend⟩
  obtain ⟨hTE, hip⟩ := Hend {} rfl
  rw [show ({ rs with tc := rs.tc + W64 1 } : RNState).k = γ.R.k j from hk] at hTE
  ihave #Hsw : □ (∀ m, ⌜AntSim.Input.campaign = .recv m⌝ -∗ sentW (GF := GF) γ m) $$ []
  · imodintro; iintro %m %h; cases h
  ihave #Hsx : □ (∀ x, ⌜AntSim.Input.campaign = .recvX x⌝ -∗ xsentW (GF := GF) γ x) $$ []
  · imodintro; iintro %x %h; cases h
  imod view_input h_vu h_lo msk h_quiet h_mask γ j v .campaign Hmode Hb1 h_camp hI (fun m h => by cases h) (fun x h => by cases h)
      $$ [Hv Hl] with ⟨%net₀, %xnet₀, Hv, Hl, #Hlb, #Hxlb, -⟩
  · iframe Hinv Hsw Hsx Hv Hl
  ihave Hco := causeOwn_noRecv (GF := GF) γ j v .campaign (by simp only [AntSim.Input.byE]; decide)
  have hR : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j (v.noteInput .campaign) r' :=
    AntSim.Reach.input _ .campaign r' hI rfl rfl rfl (fun m h => by cases h) (fun x h => by cases h)
      hTE
  have hip' : ip' = lcpLen v.r.p.log r'.p.log := by
    rw [hip]; exact Nat.min_eq_right (lcpLen_le_left _ _)
  ihave Hown := Hclose $$ %_ %r' %ip' %.campaign %net₀ %xnet₀ %([] : List XMsg) %null Hrnf Hraw
    %(⟨rfl, rfl, rfl, rsView_noteInput .campaign hrv rfl rfl rfl rfl rfl rfl, hR, hip', .inr (.inr (.inr (.inr (.inr (.inl rfl))))),
      viewNormal_noteInput hN (fun _ h => by cases h)⟩)
    Htc Hcause Hv Hl Hlb Hxlb Hco
  try wp_auto
  have hin := wp_input c γ n j (v.noteInput .campaign) net₀ xnet₀ r' [] q slice.nil
  rw [show (v.noteInput .campaign).byE = go!"campaign" from rfl] at hin
  wp_apply hin $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v' ⟨Hown, Had, Htok, %Hby⟩
  · ipureintro; exact Hb1
  try wp_auto
  iapply HΦ
  iframe Hown Had Htok
  ipureintro; exact Hby

end proof

end AntHarness
end EtcdGrove
end Perennial
