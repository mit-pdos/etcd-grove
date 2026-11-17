/- Lean-first (no Rocq counterpart). Both modes (2026-11-12, trace-check cleanup, step-4 review F3): the
untraced proof (the ticks' untraced instances, `TracedUntracedTick.lean`) and the traced one (slice 26n,
until then `RawNode.Tick.traced` in `TracedRawNode.lean`: the ticks' traced instances at the capability
`rnTrace` holds, which comes back idle at the end state), after a common prefix. -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Tick
public import Spec.go_etcd_io.raft.v3.raft__tickHeartbeat
-- (Q8 stage 1 slice 12) the ticks' untraced instances
public import Proof.go_etcd_io.raft.v3.TracedUntracedTick
-- the traced instances (`raft.tickElection.traced`, `raft.tickHeartbeat.traced`) and `rnTrace_some`
public import Proof.go_etcd_io.raft.v3.TracedRawNode
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.tick` is one of the two tick functions (`TickFnOk`, since `r.tick` is set:
`NStateWf`); either one's `TickStep` keeps `ownRawNode` but for the term. Untraced, over the ticks'
untraced instances; traced, over their traced instances (at any role since Q25 (a): `r.tick` is either
function whatever the role) at the capability `rnTrace` holds, which comes back idle at the end state. -/
theorem RawNode.Tick.wp_proof
    (wp_tickElection : raft.tickElection.spec (GF := GF) (hG := hG))
    (wp_tickHeartbeat : raft.tickHeartbeat.spec (GF := GF) (hG := hG)) :
    RawNode.Tick.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs Hterm Hflw Htrb
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto
  have Htc1 : uint.Z s.term + 1 ≤ uint.Z s.gh.tc := by rw [← Htrm, ← Hpvoff.2.1]; exact Hterm
  wp_apply raft.wp_load_tickC cf rnv.raft' id s Hwf.2 $$ Hphys as %f ⟨Hphys, %Hf⟩
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  obtain HtrG | ⟨γd, HtrG⟩ : γ.reTrace = none ∨ ∃ γd, γ.reTrace = some γd := by
    cases γ.reTrace <;> simp
  · -- untraced: the ticks' untraced instances (`TracedUntracedTick.lean`)
    clear Htrb
    have wp_tickElection := raft.tickElection.untraced wp_tickElection
    have wp_tickHeartbeat := raft.tickHeartbeat.untraced wp_tickHeartbeat
    have Hnw : uint.Z s.term + 1 < 2 ^ 64 := by
      have : uint.Z s.gh.tc < 2 ^ 64 := by word
      omega
    rcases Hf with rfl | rfl
    all_goals first
      | wp_apply wp_tickElection cf _ γ rnv.raft' id s
          Hnw (fun _ => Htc1) Hwf (Hrnfl.1 Hflw)
          Hpf.1
          (by tr_none) $$ [$Hphys $Hghost] as %s' ⟨Hphys, Hghost, %Hwf', %Hcv, %Htk⟩
      | wp_apply wp_tickHeartbeat cf _ γ rnv.raft' id s Hwf Hpf.1
          (by tr_none) $$ [$Hphys $Hghost] as %s' ⟨Hphys, Hghost, %Hwf', %Hcv, %Htk⟩
    all_goals (
      have Hc := Hcv.1
      obtain ⟨⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩, Ht1, Ht2, Hip4, Htpc, Hgd, Hsrb, -⟩ := Htk
      icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
      ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) Hip4 $$ Hstrecs
      iapply HΦ $$ %s'.term
      isplitl
      ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
      · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps
          Hwf' Hin
          Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
          (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) rfl (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hgh, ← Hns0.2]; exact Hstor.2⟩) ⟨fun h => Hgd fp (Hpvoff.1 h), by rw [Hgh]; exact Hpvoff.2.1,
            by rw [Hgh]; omega, fun hp => by rw [Hgh, Htpc hp]; exact Htc1, Hpvoff.2.2.2.2.step Hsrb⟩
          (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
          (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
          (Hsdt.ofRec Hsn Hsd) Hrole
          (Hphs.keep rfl rfl rfl (HsLe.of_step Hcv.2 Hc) Hsn (.inl Hip4)) $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' [Hdur]
        · -- (durability stage II (i)) the step keeps `durTie`'s fields
          iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
      ipureintro
      rw [Htrm]
      exact ⟨Ht1, Ht2⟩)
  · -- traced: the ticks' traced instances, the capability opened from `rnTrace` and closed at the end
    obtain ⟨Htcb, Hfit⟩ := Htrb (by rw [HtrG]; simp)
    replace Hfit := Hfit.le
    have wp_tickElection := raft.tickElection.traced wp_tickElection
    have wp_tickHeartbeat := raft.tickHeartbeat.traced wp_tickHeartbeat
    have HT : uint.Z s.term + 1 < traceNumBound := by rw [← Htrm]; omega
    -- the capability, open; the ticks' premises from the node's state
    have Htr : s.gh.tr = some γd := Hgtr.trans HtrG
    icases (rnTrace_some γ rnv.raft' id cf rs.delivered s γd Htr).1 $$ Hrntr with
          ⟨%Hscope, %Hpure, #Hcqf, #Hnosnap, %bt, %Hbt, Hcap⟩
    imod trNoSnap_prev0 s.gh.tr s.logst (by rw [Htr]; simp) $$ Hnosnap with %Hprev0
    icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq, Hphys⟩
    icombine Hcqf Hcq gives %Hcqe
    rcases Hf with rfl | rfl
    all_goals first
      | wp_apply wp_tickElection cf _ γ rnv.raft' id s γd (fun _ => True) bt Hwf Hpf.1 (Hrnfl.1 Hflw)
          Htr Hscope.1 Hcqe.symm HT Hfit Hscope.2
          $$ [$Hphys $Hghost $Hcap $Hnosnap] as %s' ⟨Hphys, Hghost, %Hwf', %Hcv, %Htk, %Houtty, Hcap⟩
      | wp_apply wp_tickHeartbeat cf _ γ rnv.raft' id s γd (fun _ => True) bt Hwf Hpf.1
          Htr Hscope.1 Hcqe.symm HT Hfit Hscope.2
          $$ [$Hphys $Hghost $Hcap $Hnosnap] as %s' ⟨Hphys, Hghost, %Hwf', %Hcv, %Htk, %Houtty, Hcap⟩
    all_goals (
      have Hc := Hcv.1
      obtain ⟨⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩, Ht1, Ht2, Hip4, Htpc, Hgd, Hsrb, Hru⟩ := Htk
      icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
      ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) Hip4 $$ Hstrecs
      -- the capability back, idle at the end state
      have Htr' : s'.gh.tr = some γd := by rw [Hgh]; exact Htr
      -- (2026-11-12, implementation step 3) the leader exclusion's clause at the end state
      icases ownStepGhost_bootCommit γ _ cf id s' $$ Hghost with ⟨%Hbc', Hghost⟩
      icases ownStepGhost_bootPrefix γ _ cf id s' $$ Hghost with ⟨%Hbp', Hghost⟩
      ihave #Hnosnap' := trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst (by rw [Htr', Htr])
        Hpv.symm Hsg.symm $$ Hnosnap
      have Hprev' : uint.Z s'.logst.prev.index' = 0 := by rw [Hpv]; exact Hprev0
      have Hboot' := RnTrBoot.step Hpure.2.2.2 Hru Hap' Hprev' (Hbp' Hprev') Hbc'
      ihave Hrntr : rnTrace γ rnv.raft' id cf rs.delivered s' $$ [Hcap]
      · iapply (rnTrace_some γ rnv.raft' id cf rs.delivered s' γd Htr').2
        isplitr
        · ipureintro; exact ⟨Hpre.trans Hscope.1, Hscope.2⟩
        isplitr
        · ipureintro; exact Hpure.step (by rw [Htr]; rfl) Houtty Hboot'
        isplitr
        · iexact Hcqf
        isplitr
        · iapply trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst (by rw [Htr', Htr]) Hpv.symm Hsg.symm
            $$ Hnosnap
        icases Hcap with ⟨%bt', %Hmono, Hcap⟩
        iexists bt'
        isplitr
        · ipureintro; exact fun h => Hmono (Hbt h)
        rw [show s'.gh.tr = s.gh.tr by rw [Htr', Htr]]
        iapply trCapB_monoΛ _ γ rnv.raft' id cf bt' _ _ _ (fun _ _ => trivial) $$ Hcap
      iapply HΦ $$ %s'.term
      isplitl
      ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
      · iapply ownRawNode_intro_tr γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps
          Hwf' Hin
          Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
          (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) rfl
          (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hgh, ← Hns0.2]; exact Hstor.2⟩)
          ⟨fun h => Hgd fp (Hpvoff.1 h), by rw [Hgh]; exact Hpvoff.2.1,
            by rw [Hgh]; omega, fun hp => by rw [Hgh, Htpc hp]; exact Htc1, Hpvoff.2.2.2.2.step Hsrb⟩
          (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
          (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
          (Hsdt.ofRec Hsn Hsd) Hrole
          (Hphs.keep rfl rfl rfl (HsLe.of_step Hcv.2 Hc) Hsn (.inl Hip4))
          (by rw [Hgh]; exact Hgtr) (by rw [Hgh]; exact Hglq)
          $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' [Hdur] Hrntr
        · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
      ipureintro
      rw [Htrm]
      exact ⟨Ht1, Ht2⟩)

end proof

end EtcdGrove
end Perennial
