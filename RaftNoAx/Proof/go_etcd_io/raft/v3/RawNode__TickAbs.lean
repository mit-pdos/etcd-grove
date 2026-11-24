-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/RawNode__TickAbs.lean` (etc/copy-part.py; rerun it, do not edit).
/-
#33 S4 (P-raft-3), `notes/antithesis-rawnode-design.md` §2.2, §2.7. **`RawNode.Tick`, the
strengthened triple** (`RawNode.Tick.absSpec`, `RawNodeAbsSpecs.lean`); the old spec is its corollary
(`RawNode.Tick.spec_of_abs`, `RawNodeSpecOfAbs.lean`). The proof is `RawNode__Tick.lean`'s, over
`ownRawNodeAt`, after the same prefix:
- untraced, over the ticks' untraced instances that keep their `Step`s' end states
  (`raft.tickElection.untracedEnd`, `raft.tickHeartbeat.untracedEnd`, `UntracedStepEnd.lean`); in the
  scope these are, through `toPState`, `TickEnd` at the harness's configuration (`tickElEnd_lift`,
  `tickHbEnd_lift`, over `InputEndLift.lean`'s `tickEnd_of_stepEnd_hup`/`_beat`; the node's
  configuration static, so its voters `rnCfg`'s), with the log's state kept
  (`logst_of_stepEnd_hup`/`_beat`), so the in-progress boundary too (`ip_eq_min_of_eq`);
- traced, over the traced instances, as before; the exact effect is not claimed there (the form's
  `γ.reTrace = none` guard).
The scope is kept: a tick changes neither the log's state nor pre-vote and check-quorum, and queues
votes and heartbeats only (`tickEnd_rd_out`; traced, `RnTrPure`'s `TrOutMsg`s and read state).

A sibling of the function's proof file, which `RawNode__Tick.lean` applies.
-/
module

public import RaftNoAx.Spec.go_etcd_io.raft.v3.RawNode__Tick
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raft__tickHeartbeat
public import RaftNoAx.Proof.go_etcd_io.raft.v3.RawNodeAtScope
public import RaftNoAx.Proof.go_etcd_io.raft.v3.UntracedStepEnd
public import RaftNoAx.Proof.go_etcd_io.raft.v3.InputEndIp
-- the traced instances (`raft.tickElection.traced`, `raft.tickHeartbeat.traced`) and `rnTrace_some`
public import RaftNoAx.Proof.go_etcd_io.raft.v3.TracedRawNode
-- `Step.commit_mono`
public import RaftNoAx.Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **`tickElection`'s end state, at the protocol level** (in the lifting lemmas' scope): `TickEnd`,
the log's state kept. -/
theorem tickElEnd_lift {c : CfgM} {id : w64} {s s' : NState} (hsc : LiftScope id s)
    (h : TickElEnd c id s s') :
    TickEnd c id (toPState s) (toPState s') ∧ s'.logst = s.logst := by
  rcases h with rfl | ⟨he, -⟩
  · exact ⟨Or.inl rfl, rfl⟩
  · exact ⟨tickEnd_of_stepEnd_hup hsc rfl rfl he, logst_of_stepEnd_hup rfl rfl he⟩

/-- **`tickHeartbeat`'s end state, at the protocol level** (in the lifting lemmas' scope, so with
check-quorum off: no quorum check): `TickEnd`, the log's state kept; the transfer abort is invisible
to `toPState`. -/
theorem tickHbEnd_lift {c : CfgM} {id : w64} {s s' : NState} (hsc : LiftScope id s)
    (hro : (toPState s).rd.ro.pending = []) (h : TickHbEnd c id s s') :
    TickEnd c id (toPState s) (toPState s') ∧ s'.logst = s.logst := by
  have hcq := hsc.2.1
  rcases h with ⟨s1, h1, h2⟩ | ⟨s1, s2, h1, -, -, h3, he⟩
  · rw [TickCqEnd.of_cq hcq h1] at h2
    rcases h2 with rfl | rfl
    · exact ⟨Or.inl rfl, rfl⟩
    · exact ⟨Or.inl rfl, rfl⟩
  · rw [TickCqEnd.of_cq hcq h1] at h3
    have hs2 : toPState s2 = toPState s ∧ s2.logst = s.logst ∧ LiftScope id s2 := by
      rcases h3 with rfl | rfl
      · exact ⟨rfl, rfl, hsc⟩
      · exact ⟨rfl, rfl, hsc⟩
    obtain ⟨hp, hl, hsc2⟩ := hs2
    refine ⟨?_, (logst_of_stepEnd_beat hsc2 rfl rfl he.1).trans hl⟩
    rw [← hp]; exact tickEnd_of_stepEnd_beat hsc2 rfl rfl (by rw [hp]; exact hro) he.1

/-- A message a traced node may hand out is no `MsgSnap`. -/
theorem TrOutMsg.not_snap {m : Msg} (h : TrOutMsg m) : m.ty ≠ .snap := by
  intro e
  rcases h with h | ⟨h, -⟩
  · rw [e] at h; simp [MsgType.traced] at h
  · rw [e] at h; cases h

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`RawNode.Tick`, strengthened** (`RawNode.Tick.absSpec`). -/
theorem RawNode.Tick.wp_absProof
    (wp_tickElection : raft.tickElection.spec (GF := GF) (hG := hG))
    (wp_tickHeartbeat : raft.tickHeartbeat.spec (GF := GF) (hG := hG)) :
    RawNode.Tick.absSpec (GF := GF) (hG := hG) := by
  intro sc γ rn id rs ps qs ip Hterm Hflw Htrb
  wp_start as H
  iNamed H
  iNamed Hrn
  -- the scope's facts at the start state
  icases rnScopeAt_scope sc rs s $$ Hsc with ⟨%Hscope, Hsc⟩
  icases ownRaftPhysC_precand cf rnv.raft' id s $$ Hphys with ⟨%Hpre0, Hphys⟩
  icases ownRaftPhysC_ipFacts cf rnv.raft' id s $$ Hphys with ⟨%Hipf, Hphys⟩
  icases ownRaftPhysC_trkDoms cf rnv.raft' id s $$ Hphys with ⟨%Hdom, Hphys⟩
  icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq0, Hphys⟩
  icases ownStepGhost_followerVotes γ _ cf id s $$ Hghost with ⟨%Hfv, Hghost⟩
  icases rnScopeAt_cfgIn sc rs s $$ Hsc with ⟨%Hcin, Hsc⟩
  icases ownStepGhost_cfgScope γ rs fp _ cf id s $$ Hghost with ⟨%Hcfm, Hghost⟩
  -- in the scope: the lifting lemmas' scope, the configuration's voters the harness's, the
  -- in-progress boundary within the log
  have Hlift : sc = true → LiftScope id s ∧ cf.voters = (rnCfg γ).voters := fun h => by
    have Hs := Hscope h
    obtain ⟨HC, Hid⟩ := cfgScope_of Hs (Hcin h) Hcfm
    have Hv : cf.voters = γ.reCfg := HC.voters
    exact ⟨liftScope_of Hs Hpre0 Hfv Hdom.1 Hdom.2 (by rw [Hv]; exact Hid),
      by rw [Hv, rnCfg_voters]⟩
  have Hipl : sc = true → ip ≤ ps.log.length := fun h => by
    rw [← Hps]
    exact ip_le_log Hip (by rw [(Hscope h).2.2.2.2.2.1]; rfl) Hipf.1.2
  wp_auto
  have Htc1 : uint.Z s.term + 1 ≤ uint.Z s.gh.tc := by rw [← Htrm, ← Hpvoff.2.1]; exact Hterm
  wp_apply raft.wp_load_tickC cf rnv.raft' id s Hwf.2 $$ Hphys as %f ⟨Hphys, %Hf⟩
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  obtain HtrG | ⟨γd, HtrG⟩ : γ.reTrace = none ∨ ∃ γd, γ.reTrace = some γd := by
    cases γ.reTrace <;> simp
  · -- untraced: the ticks' untraced instances (`TracedUntracedTick.lean`)
    clear Htrb
    have wp_tickElection := raft.tickElection.untracedEnd wp_tickElection
    have wp_tickHeartbeat := raft.tickHeartbeat.untracedEnd wp_tickHeartbeat
    have Hnw : uint.Z s.term + 1 < 2 ^ 64 := by
      have : uint.Z s.gh.tc < 2 ^ 64 := by word
      omega
    rcases Hf with rfl | rfl
    all_goals first
      | wp_apply wp_tickElection cf _ γ rnv.raft' id s
          Hnw (fun _ => Htc1) Hwf (Hrnfl.1 Hflw)
          Hpf.1
          (by tr_none) $$ [$Hphys $Hghost] as %s' ⟨Hphys, Hghost, %Hwf', %Hcv, %Htk, %Hend⟩
      | wp_apply wp_tickHeartbeat cf _ γ rnv.raft' id s Hwf Hpf.1
          (by tr_none) $$ [$Hphys $Hghost] as %s' ⟨Hphys, Hghost, %Hwf', %Hcv, %Htk, %Hend⟩
    all_goals (
      have Hc := Hcv.1
      obtain ⟨⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩, Ht1, Ht2, Hip4, Htpc, Hgd, Hsrb, -⟩ := Htk
      icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
      icases ownRaftPhysC_inprogress_pos cf rnv.raft' id s' $$ Hphys with ⟨%Hip1, Hphys⟩
      icases ownRaftPhysC_cq cf rnv.raft' id s' $$ Hphys with ⟨#Hcq1, Hphys⟩
      icombine Hcq0 Hcq1 gives %Hcqe
      have Hcq' : s'.cq = s.cq := by first | exact Hcqe.symm | exact Hcqe
      ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) Hip4 $$ Hstrecs
      -- in the scope, the tick's exact effect, the log's state kept
      have Hlifted : sc = true →
          TickEnd (rnCfg γ) id (toPState s) (toPState s') ∧ s'.logst = s.logst := fun h => by
        obtain ⟨hl, hv⟩ := Hlift h
        first
          | exact ⟨(tickElEnd_lift hl Hend).1.of_voters hv, (tickElEnd_lift hl Hend).2⟩
          | exact ⟨(tickHbEnd_lift hl ((roEmpty_iff s).1 (Hscope h).2.2.2.2.2.2.2.2.1) Hend).1.of_voters hv,
              (tickHbEnd_lift hl ((roEmpty_iff s).1 (Hscope h).2.2.2.2.2.2.2.2.1) Hend).2⟩
      ihave Hsc := rnScopeAt_keepIf sc rs { rs with term := s'.term } s s'
        (fun h Hs => by
          have hro := tickEnd_rd_out (Hlifted h).1
          exact RnScope.keep Hs rfl rfl Hpre Hcq' hro.1 Hpv Hsn hro.2
            (tickEnd_ro (Hlifted h).1)) Hsg $$ Hsc
      ihave Hrntr := rnTrace_none (GF := GF) γ rnv.raft' id cf rs.delivered s'
        (by rw [Hgh]; exact Hgtr.trans HtrG)
      iapply HΦ $$ %s'.term %(toPState s') %(uint.nat s'.logst.inprogress - 1)
      isplitl
      ihave #Hhist' := restoredSnapHistory_keep γ id Hsd $$ Hhist
      ihave Hledger' := restoreLedger_keep γ id rs.sn (s := s) (s' := s')
        (by first | exact Href.voteLe.1 | exact Hcv.1.voteLe.1 | exact Hvr.1 | omega)
        (logStoreRec_ksn Hsd) Hcv.commit Hcv.queue $$ Hledger
      ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
      · iapply ownRawNodeAt_intro γ rn id { rs with term := s'.term } (toPState s') qs
          (uint.nat s'.logst.inprogress - 1) sc s' cf fp rnv sv hprev steps
          Hwf' Hin
          Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
          (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) rfl (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hgh, ← Hns0.2]; exact Hstor.2⟩) ⟨fun h => Hgd fp (Hpvoff.1 h), by rw [Hgh]; exact Hpvoff.2.1,
            by rw [Hgh]; omega, fun hp => by rw [Hgh, Htpc hp]; exact Htc1, Hpvoff.2.2.2.2.step Hsrb⟩
          (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
          (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
          (Hsdt.ofRec Hsn Hsd) Hrole
          (Hphs.keep rfl rfl rfl (HsLe.of_step Hcv.2 Hc) Hsn (.inl Hip4)) rfl (by omega)
          (by rw [Hgh]; exact Hgtr) (by rw [Hgh]; exact Hglq)
          $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' Hhist' Hledger' [Hdur] Hrntr Hsc
        · -- (durability stage II (i)) the step keeps `durTie`'s fields
          iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
      isplitr
      · ipureintro
        rw [Htrm]
        exact ⟨Ht1, Ht2⟩
      ipureintro
      intro h _
      have hl := (Hlifted h).2
      have hlog : (toPState s').log = ps.log := by
        rw [← Hps]
        show s'.logst.sents ++ s'.logst.uents = s.logst.sents ++ s.logst.uents
        rw [hl]
      refine ⟨by rw [← Hps]; exact (Hlifted h).1, ?_⟩
      rw [hl, Hip, Nat.add_sub_cancel]
      exact ip_eq_min_of_eq (Hipl h) hlog)
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
      have Hpure' := Hpure.step (by rw [Htr]; rfl) Houtty Hboot'
      icases ownRaftPhysC_inprogress_pos cf rnv.raft' id s' $$ Hphys with ⟨%Hip1, Hphys⟩
      icases ownRaftPhysC_cq cf rnv.raft' id s' $$ Hphys with ⟨#Hcq1, Hphys⟩
      icombine Hcq0 Hcq1 gives %Hcqe
      have Hcq' : s'.cq = s.cq := by first | exact Hcqe.symm | exact Hcqe
      ihave Hsc := rnScopeAt_keepIf sc rs { rs with term := s'.term } s s'
        -- (2026-11-24) the scope's cluster is untraced (`RnCfgIn`): this branch is outside it
        (fun h _ => by have := (Hcin h).2.2; rw [HtrG] at this; cases this) Hsg $$ Hsc
      ihave Hrntr : rnTrace γ rnv.raft' id cf rs.delivered s' $$ [Hcap]
      · iapply (rnTrace_some γ rnv.raft' id cf rs.delivered s' γd Htr').2
        isplitr
        · ipureintro; exact ⟨Hpre.trans Hscope.1, Hscope.2⟩
        isplitr
        · ipureintro; exact Hpure'
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
      iapply HΦ $$ %s'.term %(toPState s') %(uint.nat s'.logst.inprogress - 1)
      isplitl
      ihave #Hhist' := restoredSnapHistory_keep γ id Hsd $$ Hhist
      ihave Hledger' := restoreLedger_keep γ id rs.sn (s := s) (s' := s')
        (by first | exact Href.voteLe.1 | exact Hcv.1.voteLe.1 | exact Hvr.1 | omega)
        (logStoreRec_ksn Hsd) Hcv.commit Hcv.queue $$ Hledger
      ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
      · iapply ownRawNodeAt_intro γ rn id { rs with term := s'.term } (toPState s') qs
          (uint.nat s'.logst.inprogress - 1) sc s' cf fp rnv sv hprev steps
          Hwf' Hin
          Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
          (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) rfl
          (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hgh, ← Hns0.2]; exact Hstor.2⟩)
          ⟨fun h => Hgd fp (Hpvoff.1 h), by rw [Hgh]; exact Hpvoff.2.1,
            by rw [Hgh]; omega, fun hp => by rw [Hgh, Htpc hp]; exact Htc1, Hpvoff.2.2.2.2.step Hsrb⟩
          (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
          (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
          (Hsdt.ofRec Hsn Hsd) Hrole
          (Hphs.keep rfl rfl rfl (HsLe.of_step Hcv.2 Hc) Hsn (.inl Hip4)) rfl (by omega)
          (by rw [Hgh]; exact Hgtr) (by rw [Hgh]; exact Hglq)
          $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' Hhist' Hledger' [Hdur] Hrntr Hsc
        · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
      isplitr
      · ipureintro
        rw [Htrm]
        exact ⟨Ht1, Ht2⟩
      -- the exact effect is claimed at an untraced node only
      ipureintro
      intro _ hn
      rw [HtrG] at hn; cases hn)

end proof

end EtcdGrove
end Perennial
