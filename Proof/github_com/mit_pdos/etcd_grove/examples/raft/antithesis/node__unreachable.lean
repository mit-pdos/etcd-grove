/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__unreachable.lean`:
`RawNode.ReportUnreachable` (the node's state unchanged: the Sim's `InputStep .unreachable`), the
view noted (`view_input`, an input the mask admits with `msk.unreachable`), the drain from its loop
head (`Reach.input`, through `input`, by `tick`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__unreachable
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__input
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessStep

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

theorem node.unreachable.wp_proof
    (wp_RU : RawNode.ReportUnreachable.apiSpec (GF := GF) (hG := hG))
    (wp_input : node.input.spec (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_vu : view_update.law (GF := GF) (hG := hG))
    (h_lo : nodeLive_over.law (GF := GF) (hG := hG))
    (msk : AntSim.SimMask) (h_quiet : antSim_quiet_in.law msk) (h_mask : runInMask.law msk)
    (h_unr : msk.unreachable = true) :
    node.unreachable.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v q id
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
  obtain ⟨hs, hcc, hfw, has⟩ := rMd_flags Hmode.2 Hb1
  try wp_auto
  wp_apply wp_RU γ.R.md hs hcc hfw has γ.raft.raftNames rn (AntSim.nodeId j) rs v.r [] v.r.p.log.length id
      Hst.1 $$ [$Hrpkg $Hraw] as Hraw
  ihave #Hsw : □ (∀ m, ⌜AntSim.Input.unreachable id = .recv m⌝ -∗ sentW (GF := GF) γ m) $$ []
  · imodintro; iintro %m %h; cases h
  ihave #Hsx : □ (∀ x, ⌜AntSim.Input.unreachable id = .recvX x⌝ -∗ xsentW (GF := GF) γ x) $$ []
  · imodintro; iintro %x %h; cases h
  imod view_input h_vu h_lo msk h_quiet h_mask γ j v (.unreachable id) Hmode Hb1 h_unr hI
      (fun m h => by cases h) (fun x h => by cases h)
      $$ [Hv Hl] with ⟨%net₀, %xnet₀, Hv, Hl, #Hlb, #Hxlb, -⟩
  · iframe Hinv Hsw Hsx Hv Hl
  ihave Hco := causeOwn_noRecv (GF := GF) γ j v (.unreachable id)
    (by simp only [AntSim.Input.byE]; decide)
  have hR : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j
      (v.noteInput (.unreachable id)) v.r :=
    AntSim.Reach.input _ (.unreachable id) v.r hI rfl rfl rfl (fun m h => by cases h)
      (fun x h => by cases h) rfl
  ihave Hown := Hclose $$ %rs %v.r %v.r.p.log.length %(.unreachable id) %net₀ %xnet₀
    %([] : List XMsg) %null Hrnf Hraw
    %(⟨rfl, rfl, rfl, rsView_noteInput (.unreachable id) hrv rfl rfl rfl rfl rfl rfl, hR,
      (lcpLen_self _).symm, .inr (.inr (.inl rfl)), viewNormal_noteInput hN (fun _ h => by cases h)⟩)
    Htc Hcause Hv Hl Hlb Hxlb Hco
  try wp_auto
  have hin := wp_input c γ n j (v.noteInput (.unreachable id)) net₀ xnet₀ v.r [] q slice.nil
  rw [show (v.noteInput (.unreachable id)).byE = go!"tick" from rfl] at hin
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
