/-
Port of election_proof/proof_newRaft.v.

raft v3.7 (stage R4, 2026-10-16): ported from the old tree's proof. `Storage.InitialState` returns
the hard state `hsOpt hp hs` and the conf state read-only, its `AutoLeave` set or not (2026-10-16, stage R6b: `csPts cs □ csm al`, weakened at once; until then `csPts cs □
csm true`, D7) beside the storage; `confchange.Restore` and `assertConfStatesEquivalent` read the
conf state at `□`; `IsEmptyHardState` reads `hsOpt`, and `loadState`, reached only for a non-empty
hard state, its `hsRO` (a `nil` pointer holds the empty one).
-/
module

public import Spec.go_etcd_io.raft.v3.newRaft
public import Spec.go_etcd_io.raft.v3.Config__validate
public import Spec.go_etcd_io.raft.v3.newLogWithSize
public import Spec.go_etcd_io.raft.v3.tracker.MakeProgressTracker
public import Spec.go_etcd_io.raft.v3.newReadOnly
public import Spec.go_etcd_io.raft.v3.traceInitState
public import Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.raft__switchToConfig
public import Spec.go_etcd_io.raft.v3.assertConfStatesEquivalent
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.raft__loadState
public import Spec.go_etcd_io.raft.v3.raftLog__appliedTo
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__VoterNodes
public import Spec.fmt.Sprintf
public import Spec.strings.Join

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A set's domain (`domSet`) of the empty map. -/
theorem domSet_empty_loc : domSet (∅ : GMap w64 Loc) = ∅ := by
  apply GMap.map_eq; intro k; rfl

/-- `confchange.Restore` on the empty tracker `MakeProgressTracker` built, for a voters-only
conf state -- possibly with **no** voter (2026-10-16, stage R8b: a new cluster's, before
`RawNode.Bootstrap` installs the peers): the configuration `switchToConfig` takes (`ownConfig` at
the voters): fresh maps when there is a voter (the general `spec`), the tracker's own `v0` and
(read-only) progress map when there is none (`spec_empty`: no op runs). -/
theorem wp_Restore_voters (H : confchange.Restore.spec (GF := GF) (hG := hG))
    (chg : confchange.Changer) (cs : Loc) (c : ConfStateM) (dq : DFrac) (v0 : Loc)
    (Hvnd : c.Voters'.Nodup) (Hv0n : W64 0 ∉ c.Voters') (Hvlen : (c.Voters'.length : Int) ≤ 2 ^ 62)
    (Hcvo : c.VotersOutgoing' = []) (Hcl : c.Learners' = []) (Hcln : c.LearnersNext' = [])
    (Hmi : 0 ≤ sint.Z chg.Tracker'.MaxInflight' ∧ sint.Z chg.Tracker'.MaxInflight' < 2 ^ 62)
    (Harr : chg.Tracker'.Config'.Voters'.arr = [v0, map.nil])
    (Hl : chg.Tracker'.Config'.Learners' = map.nil)
    (Hln : chg.Tracker'.Config'.LearnersNext' = map.nil)
    (Hal : chg.Tracker'.Config'.AutoLeave' = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗
        ownCSM cs dq c ∗ v0 ↦$ (∅ : GMap w64 Unit) ∗
        chg.Tracker'.Progress' ↦$□ (∅ : GMap w64 Loc) }}
      (App (App (Val #(functions confchange.Restore [])) (Val #chg)) (Val #cs))
    {{ (cfgv : tracker.Config) (prsm : Loc), RET (PairV (PairV #cfgv #prsm) #interface.nil);
        |==> (ownCSM cs dq c ∗
          ∃ prs : GMap w64 Loc, ownConfig (GMap.listToSet c.Voters') cfgv prsm prs ∗
            ⌜domSet prs = GMap.listToSet c.Voters'⌝) }} := by
  iintro %Φ ⟨#Hpkg, Hcs, Hv0, #Hpm⟩ HΦ
  have Hcsz : (GMap.size (GMap.listToSet c.Voters') : Int) ≤ 2 ^ 62 := by
    rw [GMap.size_list_to_set _ Hvnd]; exact Hvlen
  by_cases Hvne : c.Voters' = []
  · -- no voter: no op, the tracker's own maps
    wp_apply (confchange.Restore.spec_empty H) chg cs c dq v0 Hvne Hcvo Hcl Hcln Hmi Harr Hl Hln Hal
      $$ [$Hcs $Hv0 $Hpm] as %cfgv %prsm ⟨%Hcp, Hcs, Hv0, -⟩
    obtain ⟨Hcfgv, Hprsm⟩ := Hcp
    subst Hcfgv Hprsm
    iapply HΦ
    imodintro
    iframe Hcs
    iexists ∅
    have Hv0' : GMap.listToSet c.Voters' = ∅ := by rw [Hvne]; rfl
    rw [Hv0']
    isplitl [Hv0]
    · iapply ownConfig_restore ∅ ∅ chg.Tracker'.Config' chg.Tracker'.Progress' ∅ v0 ∅ Harr Hln Hal
        (domSet_gset _) (by rw [GMap.map_union_empty]; exact domSet_empty_loc)
        (fun k hk => absurd hk (GMap.not_elem_of_empty _))
        (by rw [GMap.map_union_empty, GMap.size_empty]; decide)
        $$ Hv0 [] Hpm []
      · rw [Hl]; iapply ownIdsetC_nil
      · iapply BigSepM.bigSepM_empty.2; iempintro
    · ipureintro; exact domSet_empty_loc
  · -- a voter: fresh maps; with no outgoing voter and no learner the model's answer is the
    -- voters (`simpleFold_restoreIn`)
    have Hm : restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' =
        some (cfgState (GMap.listToSet c.Voters') (GMap.listToSet c.Learners')) := by
      rw [Hcvo, Hcln]
      unfold restoreM restoreSimpleOps
      simp only [↓reduceIte]
      exact simpleFold_restoreIn c.Voters' c.Learners' Hvne
        (fun x hx => hx.elim (fun h e => Hv0n (e ▸ h)) (fun h _ => by rw [Hcl] at h; cases h))
        (fun x hx => by rw [Hcl] at hx; cases hx)
    wp_apply H chg cs c dq v0 _ Hm Hmi Harr Hl Hln Hal $$ [$Hcs $Hv0 $Hpm]
      as %cfgv %prsm %prs ⟨Hcs, -, -, (⟨%Hops, -⟩ | ⟨-, Hc, Hprsm, %Hdom, Hprogs⟩)⟩
    · exfalso; exact restoreSimpleOps_ne_nil_of_voters _ _ _ _ Hvne Hops
    icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vref, %vout, %Harr1, Hvref, Hout, Hlm, Hln1, %Hal1⟩
    icases ownIdsetC_nil_of _ _ (cfgState _ _).cfg.outgoing rfl $$ Hout with %Hvout
    icases ownIdsetC_nil_of _ _ (cfgState _ _).cfg.learnersNext rfl $$ Hln1 with %Hcfgln
    have Hcfgarr : cfgv.Voters'.arr = [vref, map.nil] := by rw [Harr1, Hvout]
    have Hcfgal := Hal1
    ihave Hlm := (show ownIdsetC (GF := GF) cfgv.Learners' (DFrac.own 1)
      (cfgState (GMap.listToSet c.Voters') (GMap.listToSet c.Learners')).cfg.learners ⊢
      ownIdsetC cfgv.Learners' (DFrac.own 1) (GMap.listToSet c.Learners') from .rfl) $$ Hlm
    ihave Hvref := (show (vref ↦$ (cfgState (GMap.listToSet c.Voters')
      (GMap.listToSet c.Learners')).cfg.incoming : IProp GF) ⊢
      vref ↦$ GMap.listToSet c.Voters' from .rfl) $$ Hvref
    have Hvm := domSet_gset (GMap.listToSet c.Voters')
    have Hprs : domSet prs = GMap.listToSet c.Voters' ∪ GMap.listToSet c.Learners' := by
      rw [Hdom]
      apply GMap.set_eq; intro k
      rw [GMap.elem_of_dom', cfgState, cfgFlags_mem, GMap.elem_of_union]
    have Hprs' : domSet prs = GMap.listToSet c.Voters' := by
      rw [Hprs, Hcl]; exact GMap.map_union_empty _
    ihave Hprogs : [∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗
        ⌜p.learner = !decide (k ∈ GMap.listToSet c.Voters')⌝ $$ [Hprogs]
    · iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
      intro k pr _
      iintro ⟨%p, Hp, %Hpl⟩
      iexists p
      iframe Hp
      ipureintro
      simp only [cfgState] at Hpl
      rw [cfgFlags_lookup] at Hpl
      by_cases hv : k ∈ GMap.listToSet c.Voters'
      · rw [ite_eq_left hv] at Hpl; rw [← Option.some.inj Hpl]; simp [hv]
      · rw [ite_eq_right hv] at Hpl
        by_cases hl : k ∈ GMap.listToSet c.Learners'
        · rw [ite_eq_left hl] at Hpl; rw [← Option.some.inj Hpl]; simp [hv]
        · rw [ite_eq_right hl] at Hpl; cases Hpl
    iapply HΦ
    ipersist Hprsm
    imodintro
    iframe Hcs
    iexists prs
    isplitl [Hvref Hlm Hprogs]
    · iapply ownConfig_restore (GMap.listToSet c.Voters') (GMap.listToSet c.Learners') cfgv prsm prs
        vref _ Hcfgarr Hcfgln Hcfgal Hvm Hprs
        (fun k hk => by rw [Hcl] at hk; exact absurd hk (GMap.not_elem_of_empty _))
        (by rw [Hcl, show GMap.listToSet ([] : List w64) = ∅ from rfl, GMap.map_union_empty]; exact Hcsz)
        $$ Hvref Hlm Hprsm Hprogs
    · ipureintro; exact Hprs'

/-- `switchToConfig` at a follower, from the struct sealed at any configuration `cfg0` and the
new configuration as `confchange.Restore` builds it (`ownConfig`), with no learners
(`domSet prs = cfg`): its `spec` at the simple configuration `cfg`. (Until 2026-10-21
`raft.switchToConfig.spec_nonleader_open`, through the simple-configuration `specS`.) -/
theorem wp_switchToConfig_follower (H : raft.switchToConfig.spec (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (tv : tracker.ProgressTracker)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (Hrole : s.role = .follower)
    (Hdom : domSet prs = cfg)
    (Hmi : 0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        r.[raft, go!"trk"] ↦ tv ∗
        (∀ tv' prs' pvs', r.[raft, go!"trk"] ↦ tv' -∗
           ownTrackerC (CfgM.simple cfg (domSet prs' \ cfg)) tv' ⟨s.votes, prs', pvs'⟩ -∗
           ⌜PrvalsOk { s with progress := prs', prvals := pvs' }⌝ -∗
           ownRaftPhys cfg r id { s with progress := prs', prvals := pvs' }) ∗
        tv.Votes' ↦$ s.votes ∗
        ownConfig cfg cfgv prsm prs }}
      (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
        (Val #cfgv)) (Val #prsm))
    {{ (cs : Loc) (xs : List w64)
        (pvs : GMap w64 Progress), RET #cs;
        ownRaftPhys cfg r id { s with progress := prs, prvals := pvs, isLearner := false } ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs [] [] [] false) true ∗ ⌜xs ≡ₚ elements cfg⌝ }} := by
  iintro %Φ ⟨#Hpkg, Htrkf, Hback, Hvotes, Hcfg⟩ HΦ
  icases ownConfig_values $$ Hcfg with ⟨%pvs, Hcfg⟩
  ihave Hcfg := ownConfigV_toC _ _ _ _ _ $$ Hcfg
  have Hnl : ¬ s.role = .leader := by rw [Hrole]; decide
  iapply H (CfgM.simple cfg (domSet prs \ cfg)) r id s tv cfgv prsm prs pvs
      (fun h => absurd h Hnl) (fun h => absurd h Hnl)
      (fun h => by rcases h with h | h <;> rw [Hrole] at h <;> cases h)
      (fun h => absurd h Hnl)
    $$ [$Hpkg $Htrkf Hback $Hvotes $Hcfg]
  · isplitl [Hback]
    · iintro %tv' %prs' %pvs' Hf Ht %Hok
      icases ownTrackerC_simple_resimple _ _ _ _ _ _ $$ Ht with ⟨Ht, %HL⟩
      ihave Hp := Hback $$ %tv' %prs' %pvs' Hf Ht %Hok
      ihave Hp := ownRaftPhys_toC' $$ Hp
      rw [HL]
      iapply ownRaftPhysCV_widen _ _ _ _ _ ?_ $$ Hp
      intro h hr hl
      exact GMap.elem_of_union_l _ (h hr hl)
    · ipureintro; exact Hmi
  inext
  iintro %cs %xs %os %ls %lns %s' ⟨Hphys, Hcs, %Hp, %Hsw⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  obtain ⟨H1, H2, H3, H4⟩ := Hp
  have Hos0 : os = [] := perm_elements_empty _ H2
  have Hlns0 : lns = [] := perm_elements_empty _ H4
  have Hl0 : domSet prs \ cfg = (∅ : GSet w64) := by
    rw [Hdom]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_difference]
    exact ⟨fun h => absurd h.1 h.2, fun h => absurd h (GMap.not_elem_of_empty _)⟩
  have Hls0 : ls = [] := perm_elements_empty _ (by simpa only [CfgM.simple, Hl0] using H3)
  subst Hos0 Hlns0 Hls0
  rw [learnerOfC_simple] at Hsw
  unfold SwitchOkC at Hsw
  rw [ite_eq_right Hnl] at Hsw
  subst Hsw
  have HL : learnerOf cfg prs id = false := by
    unfold learnerOf; rw [Hdom]; simp
  iapply HΦ $$ %cs %xs %pvs
  rw [HL]
  iframe Hphys
  isplitl [Hcs]
  · simp only [CfgM.simple]; iexact Hcs
  ipureintro; exact H1

theorem newRaft.wp_proof
    (wp_Config_validate : Config.validate.spec (GF := GF) (hG := hG))
    (wp_newLogWithSize : newLogWithSize.spec (GF := GF) (hG := hG))
    (wp_MakeProgressTracker : tracker.MakeProgressTracker.spec (GF := GF) (hG := hG))
    (wp_newReadOnly : newReadOnly.spec (GF := GF) (hG := hG))
    (wp_traceInitState : traceInitState.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_confchange_Restore : confchange.Restore.spec (GF := GF) (hG := hG))
    (wp_raft_switchToConfig : raft.switchToConfig.spec (GF := GF) (hG := hG))
    (wp_assertConfStatesEquivalent : assertConfStatesEquivalent.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_raft_loadState : raft.loadState.spec (GF := GF) (hG := hG))
    (wp_raftLog_appliedTo : raftLog.appliedTo.spec (GF := GF) (hG := hG))
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_VoterNodes : tracker.ProgressTracker.VoterNodes.spec (GF := GF) (hG := hG))
    (wp_fmt_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_strings_Join : strings.Join.spec (GF := GF) (hG := hG)) :
    newRaft.spec (GF := GF) (hG := hG) := by
  intro c cv lok si sn σ hs csm R R'
    Hvalid Hlok Hsto HmaxInfl Hdpf Hros Hdccv Hmcs Happ Hhs Hpe Hents Hpend Hfr0 Hsg0 Hdt0 Hfl0
    Hvnd Hv0 Hvlen62 Hcs1 Hcs2 Hcs3 Hal
  -- (raft-final) the boot bundle's view: a fresh storage
  have Hσ : σ = ({ prev := entryID.mk (W64 0) (W64 0), ents := [], pend := [] } : StorState) := by
    cases σ; simp_all
  subst Hσ
  obtain ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩ := Hvalid
  wp_start as ⟨Hc, #Hlg0, HR, #HFI, #HLI, #HInit⟩
  wp_auto
  wp_apply wp_Config_validate _ _ ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩
    $$ [$Hc] as %cv' ⟨Hc, %Hpres⟩
  obtain ⟨HpID, HpET, HpHT, HpSt, HpAp, HpMI, HpCQ, HpPV, HpDPF, HpLg, HpMC, HpAW, HpRO, HpDCC,
    HpSDR⟩ :=
    Hpres
  rw [HpSt, Hsto, HpLg, Hlok]
  have Hmcs' : 0 < uint.Z cv'.MaxCommittedSizePerReady' := by
    rw [HpMC]
    split
    · rename_i Hz
      rcases Hmcs with Hc | Hc
      · exact absurd Hz Hc
      · have : uint.Z cv.MaxSizePerMsg' ≠ 0 := fun H0 => Hc (by word)
        word
    · rename_i Hz
      have : uint.Z cv.MaxCommittedSizePerReady' ≠ 0 := fun H0 => Hz (by word)
      word
  wp_apply wp_newLogWithSize _ _ _ sn lok R rfl Hmcs' $$ [$HR $HFI $HLI $Hlg0]
    as %l %ip ⟨HR, %Hip0, HLback⟩
  rw [HpSt, Hsto]
  wp_apply HInit $$ [$HR] as %hp %cs %al ⟨#Hhsp, #Hcs, Hup⟩
  imod Hup with ⟨#HisSto, HSto, HR⟩
  ihave HL := HLback $$ HisSto HSto
  wp_apply wp_MakeProgressTracker as %tv0 %v0 ⟨%Htv0, Hv0, Hvotes, Hprs0⟩
  obtain ⟨Htv0mi, Htv0mb, Htv0arr, Htv0l, Htv0ln, Htv0al⟩ := Htv0
  wp_apply wp_newReadOnly _ (HpRO.trans Hros) as %ro Hro
  wp_apply wp_traceInitState
  wp_apply wp_raftLog_lastEntryID $$ [$HL] as %lastID ⟨HL, -⟩
  have Hmi : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62 := by
    rw [Htv0mi, HpMI]; omega
  ipersist Hprs0
  ihave Hcsw := csPts_weaken $$ Hcs
  -- `confchange.Restore` on the empty tracker: the configuration `switchToConfig` installs
  -- (fresh maps, or with no voter the tracker's own: `wp_Restore_voters`, 2026-10-16, stage R8b)
  wp_apply wp_Restore_voters wp_confchange_Restore ⟨tv0, lastID.index'⟩ cs csm DFrac.discard v0
    Hvnd Hv0 Hvlen62 Hcs1 Hcs2 Hcs3 Hmi Htv0arr Htv0l Htv0ln Htv0al
    $$ [$Hcsw $Hv0 $Hprs0]
    as %cfgv %prsm Hres
  imod Hres with ⟨-, %prs, Hcfg, %Hprs'⟩
  -- the struct, over the empty configuration: its tracker is the empty
  -- one `MakeProgressTracker` built, and its log is at the state
  -- `newLogWithSize` built. It holds no `Progress` yet, so `prvals` is
  -- empty.
  let ls0 : LogState :=
    { prev := entryID.mk (W64 0) (W64 0), sents := [], uents := [], committed := W64 0,
      applied := W64 0, snap := none, inprogress := ip,
      applying := W64 0, unpersisted := [], stored := [], apsize := W64 0,
      apmax := cv'.MaxCommittedSizePerReady', storage := interface.ok si, ksn := [], sn := sn }
  let s0 : NState := ⟨W64 0, W64 0, W64 0, .follower, ∅, [], func.nil, false, ∅, l, ls0, ∅,
    cv.PreVote', { sn := sn }, {}, W64 0, W64 0, false, cv'.StepDownOnRemoval', cv.CheckQuorum'⟩
  ihave Hmisc : ownRaftMisc (GF := GF) slice.nil ro slice.nil ({} : RdState) $$ [Hro]
  · unfold ownRaftMisc
    simp only [named]
    isplitr
    · iunfold readStatesPts
      iexists []
      isplitr
      · iapply ownSlice_nil
      iapply BigSepL2.bigSepL2_nil.2; iempintro
    isplitr
    · iapply ownSliceCap_nil
    isplitl [Hro]
    · iexact Hro
    isplitr
    · iexists []
      isplitr
      · iapply ownSlice_nil
      iapply BigSepL2.bigSepL2_nil.2; iempintro
    iapply ownSliceCap_nil
  ihave Hnil1 : (slice.nil ↦* (([] : List QMsg).map QMsg.loc) : IProp GF) $$ []
  · rw [List.map_nil]; iapply ownSlice_nil
  ihave Hnil2 : (slice.nil ↦* (([] : List QMsg).map QMsg.loc) : IProp GF) $$ []
  · rw [List.map_nil]; iapply ownSlice_nil
  ihave Hcap1 := ownSliceCap_nil (V := Loc) (GF := GF)
  ihave Hcap2 := ownSliceCap_nil (V := Loc) (GF := GF)
  ihave Hob := outboxRel_nil (GF := GF)
  imod raftOwn_of_pts «$r0_ptr» _ $$ «$r0» with «$r0»
  -- (D21 M3) not in the no-snapshot mode (set later, by the node's construction)
  ihave #Hns0 := NsCap.off (GF := GF) s0.logst.storage
  -- the struct, left open at its tracker (`ownRaftPhys_intro_trk`, 2026-10-16, stage R8b: the
  -- empty tracker's own maps may be what `switchToConfig` installs, so they cannot also seal the
  -- struct first); `switchToConfig` installs the configuration and seals it
  ihave #Hsc0 : qSrcs (GF := GF) s0.gh.sn ([] ++ []) $$ []
  · rw [List.append_nil]; iapply qSrcs_nil
  icases ownRaftPhys_intro_trk (GMap.listToSet csm.Voters') «$r0_ptr» cv.ID' s0 _ [] [] lok
    HpID rfl rfl rfl rfl rfl ⟨HpPV, fun h => absurd h (by simp only [s0]; decide)⟩ (by rw [HpDPF, Hdpf]) (by rw [HpDCC, Hdccv]) (by first | exact HpCQ | exact HpCQ.symm | rw [HpCQ]) rfl ⟨rfl, fun h => HvID h.symm⟩ rfl rfl HvID
    (by show 0 < sint.Z cv'.ElectionTick'; rw [HpET]; omega) (by rw [HpLg, Hlok]) rfl
    (fun h => absurd h (by simp only [s0]; decide)) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (Nat.zero_le _)
    ⟨fun h => absurd h Bool.false_ne_true, SnpOk.of_quiet rfl rfl rfl rfl (fun _ h => by cases h) (fun _ h => by cases h), rfl⟩
    (fun h => absurd rfl h) (LogNsOk.off rfl)
    -- the queues empty; a follower
    (XfOk.nil (fun h => absurd h (by simp only [s0]; decide)))
    $$ «$r0» Hlg0 HL Hnil1 Hcap1 Hnil2 Hcap2 Hmisc Hob Hns0 Hsc0 with ⟨Htrkf, Hback⟩
  wp_apply (wp_switchToConfig_follower wp_raft_switchToConfig) _ _ _ s0 tv0 cfgv prsm prs
    (by simp only [s0]) Hprs' Hmi $$ [$Htrkf $Hback $Hvotes $Hcfg]
    as %cs2 %xs2 %pvs1 ⟨Hphys, Hcs2v, %Hxs2⟩
  have Hpermv : csm.Voters' ≡ₚ xs2 := by
    refine List.Perm.trans ?_ Hxs2.symm
    refine (List.perm_ext_iff_of_nodup Hvnd (GMap.NoDup_elements _)).2 ?_
    intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]
  have Hperm : csm.lists.Perm (ConfStateM.mk xs2 [] [] [] false).lists := by
    simp only [CSLists.Perm, ConfStateM.lists, Hcs1, Hcs2, Hcs3]
    exact ⟨Hpermv, List.Perm.refl _, List.Perm.refl _, List.Perm.refl _⟩
  have Hbnd : csm.lists.Bounded := by
    simp only [CSLists.Bounded, ConfStateM.lists, Hcs1, Hcs2, Hcs3, List.length_nil]
    exact ⟨Hvlen62, by decide, by decide, by decide⟩
  ihave Hcs2v := csPts_weaken $$ Hcs2v
  ihave Hcsw := csPts_weaken $$ Hcs
  wp_apply wp_assertConfStatesEquivalent _ cs cs2 csm (ConfStateM.mk xs2 [] [] [] false)
    DFrac.discard (DFrac.own 1) Hperm Hbnd Hal $$ [$Hcsw $Hcs2v] as ⟨-, -⟩
  -- `if !IsEmptyHardState(hs) { r.loadState(hs) }`: both arms end at the
  -- same struct state `s1` and log state `ls1`, so the rest of the proof
  -- is done once, for both.
  let ls1 : LogState := { ls0 with committed := committedAfter (entryID.mk (W64 0) (W64 0)) hs }
  let s1 : NState :=
    { s0 with progress := prs, prvals := pvs1, term := hs.Term', vote := hs.Vote', logst := ls1 }
  wp_join iprop(ownRaftPhys (listToSet csm.Voters') «$r0_ptr» cv.ID' s1 ∗ hs_ptr ↦ hp ∗
      r_ptr ↦ «$r0_ptr») at next
    with [Hphys hs r] as ⟨Hphys, hs, r⟩
  · wp_apply wp_IsEmptyHardState hp hs $$ []
    · simp only [named]; iexact Hhsp
    by_cases Hemp : HsEmpty hs
    · have Hd : decide (hs.Term' = W64 0 ∧ hs.Vote' = W64 0 ∧ hs.Commit' = W64 0) = true :=
        decide_eq_true Hemp
      rw [Hd]
      wp_auto
      isplitr
      · ipureintro; rfl
      iframe hs r
      iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
      obtain ⟨HT, HV, _⟩ := Hemp
      simp only [s1, s0, ls1, ls0, committedAfter, (show HsEmpty hs from ⟨HT, HV, ‹_›⟩), ↓reduceIte,
        HT, HV]
    · exfalso; exact Hemp Hhs
  -- `if c.Applied > 0 { raftlog.appliedTo(c.Applied, 0) }`, likewise
  let ap : w64 := if cv.Applied' = W64 0 then (entryID.mk (W64 0) (W64 0)).index' else cv.Applied'
  let ls2 : LogState := { ls1 with applied := ap, applying := w64Max (entryID.mk (W64 0) (W64 0)).index' ap }
  let s2 : NState := { s1 with logst := ls2 }
  rw [HpAp]
  wp_join iprop(ownRaftPhys (listToSet csm.Voters') «$r0_ptr» cv.ID' s2 ∗ c_ptr ↦ c ∗ c ↦ cv' ∗
      raftlog_ptr ↦ l) with [Hphys c Hc raftlog] as ⟨Hphys, c, Hc, raftlog⟩
  · -- `raftlog` is `r.raftLog`: the log, through the accessor
    have Ha0 : cv.Applied' ≠ W64 0 := by intro h; rw [h] at Hif; exact absurd Hif (by decide)
    exfalso; exact Ha0 Happ
  · have Ha0 : cv.Applied' = W64 0 := by word
    iframe c Hc raftlog
    iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
    simp only [s2, ls2, ap, ls1, ls0, s1, Ha0, ↓reduceIte, w64Max, Int.lt_irrefl]
  -- `r.becomeFollower(r.Term, None)`
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  wp_apply wp_raft_becomeFollower _ _ _ s2 s2.term (W64 0) (Int.le_refl _) $$ [$Hphys]
    as %pvs3 Hphys
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  let s3 : NState := { becomeFollower s2 s2.term (W64 0) with prvals := pvs3 }
  -- `r.trk.VoterNodes()`
  icases ownRaftPhys_tracker_same _ _ _ s3 $$ Hphys with ⟨%tv3, Htrkf, Htrk3, Htrkback⟩
  wp_apply wp_ProgressTracker_VoterNodes $$ [$Htrkf $Htrk3] as %nsl %nxs ⟨Htrkf, Htrk3, Hnsl, %Hnxs⟩
  rw [CfgM.voters_simple] at Hnxs
  ihave Hphys := Htrkback $$ %tv3 Htrkf Htrk3
  -- the log line's `nodesStrs` loop; what it builds is never read
  ihave IH : iprop(∃ (k x : w64) (sl' : GoSlice) (strs : List GoString),
      "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ x ∗ "nodesStrs" ∷ nodesStrs_ptr ↦ sl' ∗
      "Hstrs" ∷ sl' ↦* strs ∗
      "Hstrs_cap" ∷ ownSliceCap GoString sl' (DFrac.own 1) ∗
      "Hnsl" ∷ nsl ↦* nxs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (nxs.length : Int)⌝) $$ [i n nodesStrs Hnsl]
  · iexists W64 0, _, slice.nil, []
    iframe i n nodesStrs Hnsl
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · ihave %Hnl := ownSlice_len $$ Hnsl
    have Hlt : (sint.Z k).toNat < nxs.length := by word
    list_elem nxs (sint.Z k).toNat as e
    rw [ite_eq_left (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z nsl.len by word)]
    wp_apply wp_load_slice_index nsl (sint.Z k) nxs (DFrac.own 1) e Hk.1 $$ [Hnsl] as Hnsl
    · iframe; ipureintro; exact He_lookup
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sla ⟨Hargs, -⟩
    wp_auto
    wp_apply wp_fmt_Sprintf $$ [$Hargs] as %str Hargs
    · ipureintro
      exact _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.uint64 _) _root_.Perennial.fmt.ArgsWf.nil
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hstrs $Hstrs_cap $Hsl2] as %sl3 ⟨Hstrs, Hstrs_cap, -⟩
    wp_for_post
    iframe
    iexists _, _, _, _
    iframe
    ipureintro; constructor <;> word
  -- the log line: `r.id`, `strings.Join(nodesStrs, ",")`, `r.Term`, then
  -- `r.raftLog.committed` and `r.raftLog.applied` through the log
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_apply wp_strings_Join $$ [$Hstrs] as %joined Hstrs
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same _ _ _ s3 $$ Hphys with ⟨Hlog3, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog3 with ⟨%lv3, Hl3, -, Hl3back⟩
  wp_auto
  ihave Hlog3 := Hl3back $$ Hl3
  ihave Hphys := Hlogback $$ Hlog3
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same _ _ _ s3 $$ Hphys with ⟨Hlog3, Hlogback⟩
  icases ownRaftLog_struct _ _ $$ Hlog3 with ⟨%lv4, Hl3, -, Hl3back⟩
  wp_auto
  ihave Hlog3 := Hl3back $$ Hl3
  ihave Hphys := Hlogback $$ Hlog3
  wp_raft_log
  iapply HΦ $$ %«$r0_ptr» %s3 %cv'
  iframe HR Hphys Hc
  isplitr
  · ipureintro; exact HpAW
  -- `becomeFollower(r.Term, None)` keeps the term, so `reset` keeps the
  -- vote: the state is the persisted `HardState`'s
  ipureintro
  refine ⟨⟨rfl, rfl⟩, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, HpSDR, Hprs', rfl⟩
  show (if s2.term = s2.term then s2.vote else W64 0) = hs.Vote'
  simp only [↓reduceIte]
  rfl

end proof

end EtcdGrove
end Perennial
