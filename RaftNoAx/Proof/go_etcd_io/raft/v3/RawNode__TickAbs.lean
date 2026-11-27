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
public import RaftNoAx.Proof.go_etcd_io.raft.v3.StepEndIp
public import RaftNoAx.Proof.go_etcd_io.raft.v3.StepEndRole
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
variable {k : NodeK}
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- (antithesis parity B1) `BkStep` of no step. -/
theorem BkStep.refl (s : NState) : BkStep s s := ⟨rfl, fun h => .inl ⟨h, rfl⟩⟩

/-- (antithesis parity B1) `BkStep` from a state agreeing with `s` on what it reads. -/
theorem BkStep.congr_left {s s2 s' : NState} (h : BkStep s2 s') (ha : s2.logst = s.logst)
    (hr : s2.role = s.role) (hp : s2.pci = s.pci) : BkStep s s' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.trans (by rw [ha]), fun hl => ?_⟩
  rcases h2 hl with ⟨a, b⟩ | ⟨a, b⟩
  · exact .inl ⟨by rw [← hr]; exact a, b.trans hp⟩
  · exact .inr ⟨by rw [← hr]; exact a, by rw [b, ha]⟩

/-- `BkStep` to a state agreeing with `s1` on what it reads. -/
theorem BkStep.congr_right {s s1 s' : NState} (h : BkStep s s1) (ha : s'.logst = s1.logst)
    (hr : s'.role = s1.role) (hp : s'.pci = s1.pci) : BkStep s s' :=
  ⟨by rw [ha]; exact h.1, fun hl => by rw [hp]; exact h.2 (by rw [← hr]; exact hl)⟩

/-- **`tickElection`'s end state, at the protocol level**: `TickEnd`, the log's state kept. -/
theorem tickElEnd_lift {c : CfgM} {id : w64} {s s' : NState}
    (hk : k.prevote = s.prevote) (h : TickElEnd c id s s') :
    TickEnd k c id (toPState s) (toPState s') ∧ s'.logst = s.logst ∧ BkStep s s' := by
  rcases h with rfl | ⟨he, -⟩
  · exact ⟨Or.inl rfl, rfl, BkStep.refl _⟩
  · exact ⟨tickEnd_of_stepEnd_hup hk rfl rfl he, logst_of_stepEnd_hup rfl rfl he,
      bk_of_stepEnd_hup rfl rfl he⟩

/-- (antithesis parity B1, step C2) **`tickHeartbeat`'s quorum check** at the `NState`: nothing, a leader's
`Progress` values replaced, or (check-quorum on) a leader's step-down. -/
theorem tickCq_cases {c : CfgM} {id : w64} {s s1 : NState} (h : TickCqEnd c id s s1) :
    s1 = s ∨ (s.role = .leader ∧ ∃ pvs, s1 = { s with prvals := pvs } ∧ toPState s1 = toPState s) ∨
    (s.role = .leader ∧ s.cq = true ∧ toPState s1 = pbecomeFollower (toPState s) (toPState s).term (W64 0) ∧
      s1.role = .follower ∧ s1.logst = s.logst) := by
  rcases h with rfl | ⟨hc, he⟩
  · exact .inl rfl
  · rcases cqEndN_of_stepEnd rfl rfl he.1 with ⟨-, rfl⟩ | h | ⟨hr, h⟩
    · exact .inl rfl
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨hr, hc, h⟩)

/-- **`tickHeartbeat`'s end state, at the protocol level** (antithesis parity B1, step C2: at any flags): the
quorum check's (nothing, or a leader's step-down: `TickEnd`'s last arm), then the transfer abort (invisible
to `toPState`), then a leader's heartbeats; the log's state kept. -/
theorem tickHbEnd_lift {c : CfgM} {id : w64} {s s' : NState} (hk : k.cq = s.cq)
    (hpc : domSet s.progress = c.ids) (h : TickHbEnd c id s s') :
    TickEnd k c id (toPState s) (toPState s') ∧ s'.logst = s.logst ∧ BkStep s s' := by
  rcases h with ⟨s1, h1, h2⟩ | ⟨s1, s2, h1, -, hr2, h3, he⟩
  · have e2 : toPState s' = toPState s1 ∧ s'.logst = s1.logst ∧ s'.role = s1.role ∧ s'.pci = s1.pci := by
      rcases h2 with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
    rcases tickCq_cases h1 with rfl | ⟨-, pvs, rfl, hp⟩ | ⟨hr, hc, hp, hf1, hl⟩
    · exact ⟨Or.inl e2.1, e2.2.1, BkStep.congr_left (BkStep.refl _) e2.2.1 e2.2.2.1 e2.2.2.2⟩
    · exact ⟨Or.inl (e2.1.trans hp), e2.2.1,
        BkStep.congr_left (BkStep.refl _) e2.2.1 e2.2.2.1 e2.2.2.2⟩
    · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [toPState_role, hr]; rfl, by rw [hk]; exact hc,
        e2.1.trans hp⟩))), e2.2.1.trans hl, ⟨by rw [e2.2.1, hl], fun hl' => ?_⟩⟩
      have := e2.2.2.1.symm.trans hl'
      rw [hf1] at this; cases this
  · have hs1 : toPState s1 = toPState s ∧ s1.logst = s.logst ∧ s1.role = s.role ∧ s1.pci = s.pci ∧
        s1.progress = s.progress := by
      rcases tickCq_cases h1 with rfl | ⟨-, pvs, rfl, hp⟩ | ⟨-, -, -, hf, -⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨hp, rfl, rfl, rfl, rfl⟩
      · exfalso
        have : s2.role = s1.role := by rcases h3 with rfl | rfl <;> rfl
        rw [this, hf] at hr2; cases hr2
    have hs2 : toPState s2 = toPState s ∧ s2.logst = s.logst ∧ s2.role = s.role ∧ s2.pci = s.pci ∧
        s2.progress = s.progress := by
      rcases h3 with rfl | rfl
      · exact hs1
      · exact hs1
    obtain ⟨hp, hl, hr, hpc2, hpg⟩ := hs2
    refine ⟨?_, (logst_of_stepEnd_beat (by rw [hr2]; decide) rfl rfl he.1).trans hl,
      (bk_of_stepEnd_beat (by rw [hr2]; decide) rfl rfl he.1).congr_left hl hr hpc2⟩
    rw [← hp]; exact tickEnd_of_stepEnd_beat (by rw [hr2]; decide) (by rw [hpg]; exact hpc) rfl rfl he.1

/-- (antithesis parity B1, step C2) **A tick's role facts**: a pre-candidate after was one before (its leader
and tally kept) or just pre-campaigned (no leader, an empty tally, no quorum); a follower leaves the follower
role only as a voter (`hup`'s promotability). -/
theorem tick_role {c : CfgM} {id : w64} {s s' : NState} (hin : id ∈ c.voters → id ∈ c.incoming)
    (h : TickElEnd c id s s' ∨ TickHbEnd c id s s') :
    (s'.role = .preCandidate →
      (s.role = .preCandidate ∧ s'.lead = s.lead ∧ (s'.votes = s.votes ∨ ¬ JQuorum c (granted s'.votes))) ∨
      (s'.lead = W64 0 ∧ ¬ JQuorum c (granted s'.votes))) ∧
    (s.role = .follower → s'.role ≠ .follower → id ∈ c.voters) := by
  rcases h with h | h
  · rcases h with rfl | ⟨he, -⟩
    · exact ⟨fun hr => .inl ⟨hr, rfl, .inl rfl⟩, fun h1 h2 => absurd h1 h2⟩
    · rcases hupRole_of_stepEnd rfl rfl he with rfl | ⟨hv, -, hp⟩
      · exact ⟨fun hr => .inl ⟨hr, rfl, .inl rfl⟩, fun h1 h2 => absurd h1 h2⟩
      · exact ⟨fun hr => .inr ⟨(hp hr).1, by rw [(hp hr).2]; exact not_jquorum_granted_empty (hin hv)⟩,
          fun _ _ => hv⟩
  · have hq : (s'.role = s.role ∧ s'.lead = s.lead ∧ s'.votes = s.votes) ∨ s'.role = .follower ∨
        (s'.role = .leader ∧ s.role = .leader) := by
      rcases h with ⟨s1, h1, h2⟩ | ⟨s1, s2, h1, -, hr2, h3, he⟩
      · have e : s'.role = s1.role ∧ s'.lead = s1.lead ∧ s'.votes = s1.votes := by
          rcases h2 with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
        rcases tickCq_cases h1 with rfl | ⟨-, pvs, rfl, -⟩ | ⟨-, -, -, hf, -⟩
        · exact .inl e
        · exact .inl e
        · exact .inr (.inl (e.1.trans hf))
      · have e : s2.role = s1.role := by rcases h3 with rfl | rfl <;> rfl
        refine .inr (.inr ⟨role_of_stepEnd_beat hr2 rfl rfl he.1, ?_⟩)
        rcases tickCq_cases h1 with rfl | ⟨-, pvs, rfl, -⟩ | ⟨-, -, -, hf, -⟩
        · rw [← e]; exact hr2
        · rw [← e]; exact hr2
        · rw [e, hf] at hr2; cases hr2
    rcases hq with ⟨a, b, v⟩ | hf | ⟨hl, hl0⟩
    · exact ⟨fun hr => .inl ⟨a.symm.trans hr, b, .inl v⟩, fun h1 h2 => absurd (a.trans h1) h2⟩
    · exact ⟨(fun hr => by rw [hf] at hr; cases hr), fun _ h2 => absurd hf h2⟩
    · exact ⟨(fun hr => by rw [hl] at hr; cases hr), (fun h1 _ => by rw [hl0] at h1; cases h1)⟩

/-- A message a traced node may hand out is no `MsgSnap`. -/
theorem TrOutMsg.not_snap {m : Msg} (h : TrOutMsg m) : m.ty ≠ .snap := by
  intro e
  rcases h with h | ⟨h, -⟩
  · rw [e] at h; simp [MsgType.traced] at h
  · rw [e] at h; cases h

end pure

section proof
variable {k : NodeK}
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
  intro sc hsc0 γ rn id rs ps qs ip Hterm Hflw Htrb
  wp_start as H
  iNamed H
  iNamed Hrn
  -- the scope's facts at the start state
  icases rnScopeAt_pureOpt sc rs s $$ Hsc with ⟨%Hscope, Hsc⟩
  icases ownRaftPhysC_ipFacts cf rnv.raft' id s $$ Hphys with ⟨%Hipf, Hphys⟩
  icases ownRaftPhysC_trkDoms cf rnv.raft' id s $$ Hphys with ⟨%Hdom, Hphys⟩
  icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq0, Hphys⟩
  icases ownRaftPhysC_sdr cf rnv.raft' id s $$ Hphys with ⟨#Hsd0, Hphys⟩
  icases ownStepGhost_cfgScope γ rs fp _ cf id s $$ Hghost with ⟨%Hcfm, Hghost⟩
  -- in the scope: the configuration the harness's, the in-progress boundary within the log
  have HCf : ∀ md, sc = some md → CfgScope γ cf ∧ cf.learners = ∅ ∧ rs.cfg.cfg = cf := fun md h =>
    cfgScope_ofMd (hsc0 md h).2.1 (Hscope md h).1 (Hscope md h).2.1 Hcfm
  have Hipl : ∀ md, sc = some md → ip ≤ ps.p.log.length := fun md h => by
    rw [← Hps]
    exact ip_le_log Hip (by rw [((Hscope md h).1.2.2.2.2.1 (hsc0 md h).1).2.1]; rfl) Hipf.1.2
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
      have Hlifted : ∀ md, sc = some md →
          TickEnd rs.k cf id (toPState s) (toPState s') ∧ s'.logst = s.logst ∧ BkStep s s' := fun md h => by
        have Hkt := (Hscope md h).2.2.1
        first
          | exact tickElEnd_lift (k := rs.k) (by rw [← Hkt]) Hend
          | exact tickHbEnd_lift (k := rs.k) (by rw [← Hkt]) Hdom.2 Hend
      have HroleT : ∀ md, sc = some md →
          (s'.role = .preCandidate →
            (s.role = .preCandidate ∧ s'.lead = s.lead ∧ (s'.votes = s.votes ∨ ¬ JQuorum cf (granted s'.votes))) ∨
            (s'.lead = W64 0 ∧ ¬ JQuorum cf (granted s'.votes))) ∧
          (s.role = .follower → s'.role ≠ .follower → id ∈ cf.voters) := fun md h =>
        tick_role (fun hv => by rw [CfgM.voters_of_out (HCf md h).1.2.1] at hv; exact hv)
          (by first | exact .inl Hend | exact .inr Hend)
      icases ownRaftPhysC_trkDoms cf rnv.raft' id s' $$ Hphys with ⟨%Hdom1, Hphys⟩
      icases ownRaftPhysC_sdr cf rnv.raft' id s' $$ Hphys with ⟨#Hsd1, Hphys⟩
      icombine Hsd0 Hsd1 gives %Hsde
      have Hsdr' : s'.sdr = s.sdr := by first | exact Hsde.symm | exact Hsde
      ihave Hsc := rnScopeAt_keepOpt sc rs { rs with term := s'.term } s s'
        (fun md h Hs0 => by
          have hT := (Hlifted md h).1
          have hro := tickEnd_rd_out hT
          exact RnScope.stepG (hsc0 md h).2.1 Hs0 (Hscope md h).2.1 (HCf md h).1 (HCf md h).2.1
            (HCf md h).2.2 ⟨rfl, rfl, rfl⟩ Hpre Hcq' (fun _ => ⟨hro.1, tickEnd_ro hT⟩)
            (fun hsn => ⟨Hpv, Hsn, fun x hx =>
              (hro.2 x hx).elim (fun hm => (Hs0.2.2.2.2.1 hsn).2.2.2 x hm) (fun h => h)⟩)
            (fun _ => by rw [Hgh]) (HroleT md h).1 (HroleT md h).2 Hdom Hdom1)
        Hsg (hfl := ⟨Hpre, Hcq', Hsdr'⟩)
        (hx := fun md h _ HX0 => by
          obtain ⟨hl0, hw0, ht0, hs0⟩ := HX0
          rcases tickEnd_lead (Hlifted md h).1 with e | e
          · refine ⟨(fun hnv => by rw [e]; exact hl0 hnv), fun p hp => hw0 p (by rw [Hgh] at hp; exact hp),
              fun hne => ?_, fun f hf => hs0 f (by rw [Hgh] at hf; exact hf)⟩
            have h1 := ht0 (by rw [← e]; exact hne)
            intro e0; apply h1; rw [e0] at Ht1; word
          · exact ⟨fun _ => .inl e, fun p hp => hw0 p (by rw [Hgh] at hp; exact hp), fun hne => absurd e hne,
          fun f hf => hs0 f (by rw [Hgh] at hf; exact hf)⟩) $$ Hsc
      ihave Hrntr := rnTrace_none (GF := GF) γ rnv.raft' id cf rs.delivered s'
        (by rw [Hgh]; exact Hgtr.trans HtrG)
      iapply HΦ $$ %s'.term %(toRState { rs with term := s'.term } fp s') %(uint.nat s'.logst.inprogress - 1)
      isplitl
      ihave #Hhist' := restoredSnapHistory_keep γ id Hsd $$ Hhist
      ihave Hledger' := restoreLedger_keep γ id rs.sn (s := s) (s' := s')
        (by first | exact Href.voteLe.1 | exact Hcv.1.voteLe.1 | exact Hvr.1 | omega)
        (logStoreRec_ksn Hsd) Hcv.commit Hcv.queue $$ Hledger
      ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
      · iapply ownRawNodeAt_intro γ rn id { rs with term := s'.term } (toRState { rs with term := s'.term } fp s') qs
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
      intro md hmd _
      have hl := (Hlifted md hmd).2.1
      have hlog : (toPState s').log = ps.p.log := by
        rw [← Hps]
        show s'.logst.sents ++ s'.logst.uents = s.logst.sents ++ s.logst.uents
        rw [hl]
      refine ⟨by
        rw [← Hps]
        exact tickEndR_of_bk (by rw [(HCf md hmd).2.2]; exact (Hlifted md hmd).1) (Hlifted md hmd).2.2
          Hsn ⟨rfl, rfl⟩, ?_⟩
      show uint.nat s'.logst.inprogress - 1 = min ip (lcpLen ps.p.log (toPState s').log)
      rw [hl, Hip, Nat.add_sub_cancel]
      exact ip_eq_min_of_eq (Hipl md hmd) hlog)
  · -- traced: the ticks' traced instances, the capability opened from `rnTrace` and closed at the end
    -- (2026-11-24) the scope's cluster is untraced (`RnCfgIn`): this branch is outside it
    obtain rfl : sc = none := by
      cases sc with
      | none => rfl
      | some md => exact absurd ((Hscope md rfl).2.1.2.2.1.symm.trans HtrG) (by simp)
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
      have Hboot' := RnTrBoot.step Hpure.2.2.2 Hru Hap' Hprev' (Hbp' Hprev') (Hbc' (by rw [Htr']; rfl))
      have Hpure' := Hpure.step (by rw [Htr]; rfl) Houtty Hboot'
      icases ownRaftPhysC_inprogress_pos cf rnv.raft' id s' $$ Hphys with ⟨%Hip1, Hphys⟩
      icases ownRaftPhysC_cq cf rnv.raft' id s' $$ Hphys with ⟨#Hcq1, Hphys⟩
      icombine Hcq0 Hcq1 gives %Hcqe
      have Hcq' : s'.cq = s.cq := by first | exact Hcqe.symm | exact Hcqe
      iclear Hsc
      ihave Hsc : rnScopeAt (GF := GF) γ id none { rs with term := s'.term } s' $$ []
      · unfold rnScopeAt; iempintro
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
      iapply HΦ $$ %s'.term %(toRState { rs with term := s'.term } fp s') %(uint.nat s'.logst.inprogress - 1)
      isplitl
      ihave #Hhist' := restoredSnapHistory_keep γ id Hsd $$ Hhist
      ihave Hledger' := restoreLedger_keep γ id rs.sn (s := s) (s' := s')
        (by first | exact Href.voteLe.1 | exact Hcv.1.voteLe.1 | exact Hvr.1 | omega)
        (logStoreRec_ksn Hsd) Hcv.commit Hcv.queue $$ Hledger
      ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
      · iapply ownRawNodeAt_intro γ rn id { rs with term := s'.term } (toRState { rs with term := s'.term } fp s') qs
          (uint.nat s'.logst.inprogress - 1) none s' cf fp rnv sv hprev steps
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
      intro _ _ hn
      rw [HtrG] at hn; cases hn)

end proof

end EtcdGrove
end Perennial
