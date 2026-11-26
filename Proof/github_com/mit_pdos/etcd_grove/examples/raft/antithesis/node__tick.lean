/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__tick.lean`: the term ceiling
raised by a receipt (`rnBudget_spend`, the receipt of `Tick`'s resolution), `RawNode.Tick`
(`TickEndR`), the view noted (`view_input`), the drain from its loop head (`Reach.input`, through
`input`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__tick
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
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem node.tick.wp_proof
    (wp_Tick : RawNode.Tick.apiSpec (GF := GF) (hG := hG))
    (wp_input : node.input.spec (GF := GF) (hG := hG))
    (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (h_tc : rawNode_term_tc.law (GF := GF) (hG := hG))
    (h_raise : rawNode_raise_tc.law (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_spend : rnBudget_spend.law (GF := GF) (hG := hG))
    (h_vu : view_update.law (GF := GF) (hG := hG))
    (h_lo : nodeLive_over.law (GF := GF) (hG := hG))
    (msk : AntSim.SimMask) (h_quiet : antSim_quiet_in.law msk) (h_mask : runInMask.law msk) :
    node.tick.spec (GF := GF) (hG := hG) := by
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
  wp_apply wp_Tick γ.raft.raftNames rn (AntSim.nodeId j) { rs with tc := rs.tc + W64 1 } v.r []
      v.r.p.log.length (by simp only; rw [← Hwf.2.2]; word) hrv.2.2.2.2.2
      (fun h => absurd Hst.1 h) $$ [$Hrpkg $Hraw] as %t %r' %ip' ⟨Hraw, %Ht, %Hend⟩
  obtain ⟨hTE, hip⟩ := Hend {} rfl Hst.1
  rw [show ({ rs with tc := rs.tc + W64 1 } : RNState).k = γ.R.k j from hk] at hTE
  ihave #Hsw : □ (∀ m, ⌜AntSim.Input.tick = .recv m⌝ -∗ sentW (GF := GF) γ m) $$ []
  · imodintro; iintro %m %h; cases h
  ihave #Hsx : □ (∀ x, ⌜AntSim.Input.tick = .recvX x⌝ -∗ xsentW (GF := GF) γ x) $$ []
  · imodintro; iintro %x %h; cases h
  imod view_input h_vu h_lo msk h_quiet h_mask γ j v .tick Hmode Hb1 trivial hI (fun m h => by cases h) (fun x h => by cases h)
      $$ [Hv Hl] with ⟨%net₀, %xnet₀, Hv, Hl, #Hlb, #Hxlb, -⟩
  · iframe Hinv Hsw Hsx Hv Hl
  ihave Hco := causeOwn_noRecv (GF := GF) γ j v .tick (by simp only [AntSim.Input.byE]; decide)
  have hR : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j (v.noteInput .tick) r' [] :=
    AntSim.Reach.input _ .tick r' [] hI rfl rfl rfl (fun m h => by cases h) (fun x h => by cases h)
      ⟨hTE, rfl⟩
  have hip' : ip' = lcpLen v.r.p.log r'.p.log := by
    rw [hip]; exact Nat.min_eq_right (lcpLen_le_left _ _)
  ihave Hown := Hclose $$ %_ %r' %ip' %.tick %net₀ %xnet₀ %([] : List XMsg) %null Hrnf Hraw
    %(⟨rfl, rfl, rfl, rsView_noteInput .tick hrv rfl rfl rfl rfl rfl rfl, hR, hip', .inr (.inr (.inl rfl)),
      viewNormal_noteInput hN (fun _ h => by cases h)⟩)
    Htc Hcause Hv Hl Hlb Hxlb Hco
  try wp_auto
  have hin := wp_input c γ n j (v.noteInput .tick) net₀ xnet₀ r' [] q slice.nil
  rw [show (v.noteInput .tick).byE = go!"tick" from rfl] at hin
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
