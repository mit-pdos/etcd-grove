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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
the voters): fresh maps when there is a voter (`spec_simple`), the tracker's own `v0` and
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
  · -- a voter: fresh maps
    wp_apply (confchange.Restore.spec_simple H) chg cs c dq v0 Hvne Hv0n (by rw [Hcl]; exact List.not_mem_nil)
      (by rw [Hcl]; intro k hk; cases hk) Hcvo Hcln Hmi Harr Hl Hln Hal
      $$ [$Hcs $Hv0 $Hpm]
      as %cfgv %prsm %prs %vref %vm ⟨Hcs, -, -, %Hcfgv, Hlm, Hvref, %Hvm, Hprsm, %Hprs, Hprogs⟩
    obtain ⟨Hcfgarr, Hcfgln, Hcfgal⟩ := Hcfgv
    have Hprs' : domSet prs = GMap.listToSet c.Voters' := by
      rw [Hprs, Hcl]; exact GMap.map_union_empty _
    iapply HΦ
    ipersist Hprsm
    imodintro
    iframe Hcs
    iexists prs
    isplitl [Hvref Hlm Hprogs]
    · iapply ownConfig_restore (GMap.listToSet c.Voters') (GMap.listToSet c.Learners') cfgv prsm prs
        vref vm Hcfgarr Hcfgln Hcfgal Hvm Hprs
        (fun k hk => by rw [Hcl] at hk; exact absurd hk (GMap.not_elem_of_empty _))
        (by rw [Hcl, show GMap.listToSet ([] : List w64) = ∅ from rfl, GMap.map_union_empty]; exact Hcsz)
        $$ Hvref Hlm Hprsm Hprogs
    · ipureintro; exact Hprs'

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
  intro c cv lok si σ hs csm
    Hvalid Hlok Hsto HmaxInfl Hdpf Hros Hdccv Hmcs Hidx Hss Hpe Hhs Happ Hvnd Hv0 Hvlen62 Hcs1 Hcs2 Hcs3 Hal
  obtain ⟨HvID, HvID1, HvID2, Hticks, HvSt, HvInfl, HvIB, HvLog, HvRO⟩ := Hvalid
  wp_start as ⟨Hc, #Hlg0, #HisSto, HSto, HInit⟩
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
  wp_apply wp_newLogWithSize _ _ _ _ lok Hidx Hss Hpe rfl Hmcs' $$ [$HisSto $HSto $Hlg0]
    as %l %ip ⟨%Hip0, HSto, HLback⟩
  rw [HpSt, Hsto]
  wp_apply HInit $$ [$HSto] as %hp %cs %al HSto #Hhsp #Hcs
  ihave HL := HLback $$ HSto
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
  let ls0 : LogState := ⟨σ.prev, σ.ents, [], σ.prev.index', σ.prev.index', none, ip, σ.prev.index', [], σ.ents,
    W64 0, cv'.MaxCommittedSizePerReady', interface.ok si, initKsn σ⟩
  let s0 : NState := ⟨W64 0, W64 0, W64 0, .follower, ∅, [], func.nil, false, ∅, l, ls0, ∅,
    cv.PreVote', {}, {}, W64 0, W64 0, false, cv'.StepDownOnRemoval', cv.CheckQuorum'⟩
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
  -- the struct, left open at its tracker (`ownRaftPhys_intro_trk`, 2026-10-16, stage R8b: the
  -- empty tracker's own maps may be what `switchToConfig` installs, so they cannot also seal the
  -- struct first); `switchToConfig` installs the configuration and seals it
  icases ownRaftPhys_intro_trk (GMap.listToSet csm.Voters') «$r0_ptr» cv.ID' s0 _ [] [] lok
    HpID rfl rfl rfl rfl rfl ⟨HpPV, fun h => absurd h (by simp only [s0]; decide)⟩ (by rw [HpDPF, Hdpf]) (by rw [HpDCC, Hdccv]) (by first | exact HpCQ | exact HpCQ.symm | rw [HpCQ]) rfl ⟨rfl, fun h => HvID h.symm⟩ rfl rfl HvID
    (by show 0 < sint.Z cv'.ElectionTick'; rw [HpET]; omega) (by rw [HpLg, Hlok]) rfl
    (fun h => absurd h (by simp only [s0]; decide)) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (Nat.zero_le _) (fun h => absurd h Bool.false_ne_true)
    (fun h => absurd rfl h)
    $$ «$r0» Hlg0 HL Hnil1 Hcap1 Hnil2 Hcap2 Hmisc Hob with ⟨Htrkf, Hback⟩
  wp_apply (raft.switchToConfig.spec_nonleader_open wp_raft_switchToConfig) _ _ _ s0 tv0 cfgv prsm prs
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
  let ls1 : LogState := ⟨σ.prev, σ.ents, [], committedAfter σ.prev hs, σ.prev.index', none, ip,
    σ.prev.index', [], σ.ents, W64 0, cv'.MaxCommittedSizePerReady',
    interface.ok si, initKsn σ⟩
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
    · have Hd : decide (hs.Term' = W64 0 ∧ hs.Vote' = W64 0 ∧ hs.Commit' = W64 0) = false :=
        decide_eq_false Hemp
      rw [Hd]
      wp_auto
      have Hll : uint.Z (logLast ls0) = uint.Z σ.prev.index' + (σ.ents.length : Int) := by
        simp only [logLast, ls0, List.length_nil]; word
      have Hpre : uint.Z ({ s0 with progress := prs, prvals := pvs1, isLearner := false } : NState).logst.committed
            ≤ uint.Z hs.Commit' ∧
          uint.Z hs.Commit' ≤ uint.Z (logLast ({ s0 with progress := prs, prvals := pvs1, isLearner := false } : NState).logst) := by
        have := Hhs Hemp
        show uint.Z σ.prev.index' ≤ _ ∧ _ ≤ uint.Z (logLast ls0)
        rw [Hll]; exact this
      -- a non-empty hard state: its pointer is not `nil` (`hsOpt`), read-only
      ihave #Hro : hsRO hp hs $$ []
      · iunfold hsOpt at Hhsp
        icases Hhsp with (⟨-, %Hz⟩ | #Hro)
        · exfalso; apply Hemp; rw [Hz]; exact ⟨rfl, rfl, rfl⟩
        · iexact Hro
      wp_apply wp_raft_loadState _ _ _
        { s0 with progress := prs, prvals := pvs1, isLearner := false } hp hs Hpre
        (by show uint.Z (W64 0) ≤ uint.Z hs.Term'; word) $$ [$Hphys] as Hphys
      · simp only [named]; iexact Hro
      isplitr
      · ipureintro; rfl
      iframe hs r
      iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
      simp only [s1, s0, ls1, ls0, committedAfter, Hemp, ↓reduceIte]
  -- `if c.Applied > 0 { raftlog.appliedTo(c.Applied, 0) }`, likewise
  let ap : w64 := if cv.Applied' = W64 0 then σ.prev.index' else cv.Applied'
  let ls2 : LogState := ⟨σ.prev, σ.ents, [], committedAfter σ.prev hs, ap, none, ip,
    w64Max σ.prev.index' ap, [], σ.ents, W64 0, cv'.MaxCommittedSizePerReady',
    interface.ok si, initKsn σ⟩
  let s2 : NState := { s1 with logst := ls2 }
  rw [HpAp]
  wp_join iprop(ownRaftPhys (listToSet csm.Voters') «$r0_ptr» cv.ID' s2 ∗ c_ptr ↦ c ∗ c ↦ cv' ∗
      raftlog_ptr ↦ l) with [Hphys c Hc raftlog] as ⟨Hphys, c, Hc, raftlog⟩
  · -- `raftlog` is `r.raftLog`: the log, through the accessor
    have Ha0 : cv.Applied' ≠ W64 0 := by intro h; rw [h] at Hif; exact absurd Hif (by decide)
    have Hrng : uint.Z ls1.applied ≤ uint.Z cv'.Applied' ∧ uint.Z cv'.Applied' ≤ uint.Z ls1.committed := by
      rw [HpAp]
      rcases Happ with h | h
      · exact absurd h Ha0
      · exact h
    icases ownRaftPhys_log_at _ «$r0_ptr» cv.ID' s1 $$ Hphys with ⟨HL, %Hgh0, Hlogback⟩
    wp_apply wp_raftLog_appliedTo l ls1 cv'.Applied' (W64 0) Hrng $$ [$HL] as HL
    ihave Hphys := Hlogback $$ %_ HL %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
      %(fun _ => logLast_le_of_fields rfl rfl rfl)
    isplitr
    · ipureintro; rfl
    iframe c Hc raftlog
    iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
    simp only [s2, ls2, ap, ls1, Ha0, ↓reduceIte, HpAp]
  · have Ha0 : cv.Applied' = W64 0 := by word
    iframe c Hc raftlog
    iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
    simp only [s2, ls2, ap, ls1, s1, Ha0, ↓reduceIte, w64Max, Int.lt_irrefl]
  -- `r.becomeFollower(r.Term, None)`
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_apply (raft.becomeFollower.spec_simple wp_raft_becomeFollower) _ _ _ s2 s2.term (W64 0) (Int.le_refl _) $$ [$Hphys]
    as %pvs3 Hphys
  let s3 : NState := { becomeFollower s2 s2.term (W64 0) with prvals := pvs3 }
  -- `r.trk.VoterNodes()`
  icases ownRaftPhys_tracker_same _ _ _ s3 $$ Hphys with ⟨%tv3, Htrkf, Htrk3, Htrkback⟩
  wp_apply (tracker.ProgressTracker.VoterNodes.spec_simple wp_ProgressTracker_VoterNodes) $$ [$Htrkf $Htrk3] as %nsl %nxs ⟨Htrkf, Htrk3, Hnsl, %Hnxs⟩
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
  iframe Hphys Hc
  isplitr
  · ipureintro; exact HpAW
  -- `becomeFollower(r.Term, None)` keeps the term, so `reset` keeps the
  -- vote: the state is the persisted `HardState`'s
  ipureintro
  refine ⟨⟨rfl, rfl⟩, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, HpSDR, Hprs'⟩
  show (if s2.term = s2.term then s2.vote else W64 0) = hs.Vote'
  simp only [↓reduceIte]
  rfl

end proof

end EtcdGrove
end Perennial
