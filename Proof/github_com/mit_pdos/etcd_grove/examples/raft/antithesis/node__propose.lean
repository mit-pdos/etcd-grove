/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__propose.lean`: `RawNode.Propose`
with the proposal's raft resources (`propOk`; `RecvEndR` at `propMsg`, a dropped proposal its
`r' = r` arm), the view noted (`view_input`), the entries of an accepted proposal built (unread
without batching), the drain from its loop head (`Reach.input`, through `input`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__propose
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__input
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput
public import Proof.go_etcd_io.raft.v3.LemmasEnts

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

/-- `RawNode.Propose`'s message is `AntSim.propMsg`. -/
theorem absMsg_propose (id : w64) (data : List w8) :
    absMsg .propose { propMsgM with From' := id } [propEntryM data] = AntSim.propMsg id data := by
  rfl

theorem node.propose.wp_proof
    (wp_Propose : RawNode.Propose.apiSpec (GF := GF) (hG := hG))
    (wp_input : node.input.spec (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_vu : view_update.law (GF := GF) (hG := hG))
    (h_lo : nodeLive_over.law (GF := GF) (hG := hG))
    (msk : AntSim.SimMask) (h_quiet : antSim_quiet_in.law msk) (h_mask : runInMask.law msk) :
    node.propose.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v q sl data
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok, %Hb1, #Hdata, Hprop⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm⟩
  icases nodeOwn_idle_open h_bp c γ j n v $$ Hown with
    ⟨%rn, %rs, Hrnf, Hraw, Htc, #Hb, %Hst, Hcause, Hv, Hl, %Hpr, Hclose⟩
  obtain ⟨hrv, hI, hP, hN, hk⟩ := Hpr
  iunfold propOk at Hprop
  icases Hprop with ⟨#Hpd, Htk, %Hmd⟩
  wp_auto
  wp_apply wp_Propose γ.raft.raftNames rn (AntSim.nodeId j) rs v.r [] v.r.p.log.length sl data
      Hst.1 $$ [$Hrpkg $Hraw $Hdata $Hpd $Htk] as %err %r' %ip' ⟨Hraw, Herr, %Hend⟩
  · ipureintro; exact Hmd
  obtain ⟨hPE, hip⟩ := Hend {} rfl
  have hPE' := hPE (AdmFold γ.dec γ.R.c0)
  rw [absMsg_propose, hk] at hPE'
  ihave #Hsw : □ (∀ m, ⌜AntSim.Input.propose data = .recv m⌝ -∗ sentW (GF := GF) γ m) $$ []
  · imodintro; iintro %m %h; cases h
  ihave #Hsx : □ (∀ x, ⌜AntSim.Input.propose data = .recvX x⌝ -∗ xsentW (GF := GF) γ x) $$ []
  · imodintro; iintro %x %h; cases h
  imod view_input h_vu h_lo msk h_quiet h_mask γ j v (.propose data) Hmode Hb1 trivial hI (fun m h => by cases h)
      (fun x h => by cases h) $$ [Hv Hl] with ⟨%net₀, %xnet₀, Hv, Hl, #Hlb, #Hxlb, -⟩
  · iframe Hinv Hsw Hsx Hv Hl
  ihave Hco := causeOwn_noRecv (GF := GF) γ j v (.propose data)
    (by simp only [AntSim.Input.byE]; decide)
  have hR : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j (v.noteInput (.propose data))
      r' :=
    AntSim.Reach.input _ (.propose data) r' hI rfl rfl rfl (fun m h => by cases h)
      (fun x h => by cases h) hPE'
  have hip' : ip' = lcpLen v.r.p.log r'.p.log := by
    rw [hip]; exact Nat.min_eq_right (lcpLen_le_left _ _)
  ihave Hown := Hclose $$ %rs %r' %ip' %(.propose data) %net₀ %xnet₀ %([] : List XMsg) %null Hrnf Hraw
    %(⟨rfl, rfl, rfl, rsView_noteInput (.propose data) hrv rfl rfl rfl rfl rfl rfl, hR, hip',
      .inr (.inr (.inr (.inl rfl))), viewNormal_noteInput hN (fun _ h => by cases h)⟩)
    Htc Hcause Hv Hl Hlb Hxlb Hco
  iclear Herr
  have hin : ∀ sl', _ := fun sl' => wp_input c γ n j (v.noteInput (.propose data)) net₀ xnet₀ r' [] q sl'
  rw [show (v.noteInput (.propose data)).byE = go!"propose" from rfl] at hin
  cases err with
  | nil =>
    try wp_auto
    wp_apply wp_slice_literal_ex (V := Loc)
    wp_alloc l0 as Hl0
    wp_auto
    iexists [l0]
    isplitr
    · ipureintro; rfl
    iintro %slp ⟨Hsl, Hsl_cap⟩
    try wp_auto
    wp_apply hin _ $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v' ⟨Hown, Had, Htok, %Hby⟩
    · ipureintro; exact Hb1
    try wp_auto
    iapply HΦ
    iframe Hown Had Htok
    ipureintro; exact Hby
  | ok ei =>
    try wp_auto
    wp_apply hin _ $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v' ⟨Hown, Had, Htok, %Hby⟩
    · ipureintro; exact Hb1
    try wp_auto
    iapply HΦ
    iframe Hown Had Htok
    ipureintro; exact Hby

end proof

end AntHarness
end EtcdGrove
end Perennial
