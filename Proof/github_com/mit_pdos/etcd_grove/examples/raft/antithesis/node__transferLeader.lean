/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__transferLeader.lean`:
`RawNode.TransferLeader` at a run with transfers (`TransferEndR`: the Sim's `InputStep .transfer`, the
log kept), the view noted (`view_input`, an input the mask admits with `msk.md.transfer`), the drain
from its loop head (`Reach.input`, through `input`, by `transfer`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__transferLeader
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

theorem node.transferLeader.wp_proof
    (wp_TL : RawNode.TransferLeader.apiSpec (GF := GF) (hG := hG))
    (wp_input : node.input.spec (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_vu : view_update.law (GF := GF) (hG := hG))
    (h_lo : nodeLive_over.law (GF := GF) (hG := hG))
    (msk : AntSim.SimMask) (h_quiet : antSim_quiet_in.law msk) (h_mask : runInMask.law msk)
    (h_tr : msk.md.transfer = true) :
    node.transferLeader.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v q to
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok, %Hb1, %Htr⟩
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
  have htmd : γ.R.md.transfer = true := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hTr, -⟩ := Hmode.1
    rw [Hmode.2.2.2.2.2.1]; exact hTr Htr.1
  try wp_auto
  wp_apply wp_TL γ.R.md hs hcc hfw has γ.raft.raftNames rn (AntSim.nodeId j) rs v.r [] v.r.p.log.length to
      (fun md h => h ▸ htmd) Hst.1 $$ [$Hrpkg $Hraw] as %r' ⟨Hraw, %Hend⟩
  have hTE := Hend γ.R.md rfl
  ihave #Hsw : □ (∀ m, ⌜AntSim.Input.transfer to = .recv m⌝ -∗ sentW (GF := GF) γ m) $$ []
  · imodintro; iintro %m %h; cases h
  ihave #Hsx : □ (∀ x, ⌜AntSim.Input.transfer to = .recvX x⌝ -∗ xsentW (GF := GF) γ x) $$ []
  · imodintro; iintro %x %h; cases h
  imod view_input h_vu h_lo msk h_quiet h_mask γ j v (.transfer to) Hmode Hb1 h_tr hI
      (fun m h => by cases h) (fun x h => by cases h)
      $$ [Hv Hl] with ⟨%net₀, %xnet₀, Hv, Hl, #Hlb, #Hxlb, -⟩
  · iframe Hinv Hsw Hsx Hv Hl
  ihave Hco := causeOwn_noRecv (GF := GF) γ j v (.transfer to)
    (by simp only [AntSim.Input.byE]; decide)
  have hR : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j
      (v.noteInput (.transfer to)) r' :=
    AntSim.Reach.input _ (.transfer to) r' hI rfl rfl rfl (fun m h => by cases h)
      (fun x h => by cases h) hTE
  have hip' : v.r.p.log.length = lcpLen v.r.p.log r'.p.log := by
    rw [transferEndR_log hTE, lcpLen_self]
  ihave Hown := Hclose $$ %rs %r' %v.r.p.log.length %(.transfer to) %net₀ %xnet₀
    %([] : List XMsg) %null Hrnf Hraw
    %(⟨rfl, rfl, rfl, rsView_noteInput (.transfer to) hrv rfl rfl rfl rfl rfl rfl, hR,
      hip', .inr (.inr (.inr (.inr (.inr (.inr rfl))))),
      viewNormal_noteInput hN (fun _ h => by cases h)⟩)
    Htc Hcause Hv Hl Hlb Hxlb Hco
  try wp_auto
  have hin := wp_input c γ n j (v.noteInput (.transfer to)) net₀ xnet₀ r' [] q slice.nil
  rw [show (v.noteInput (.transfer to)).byE = go!"transfer" from rfl] at hin
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
