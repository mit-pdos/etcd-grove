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
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import Spec.go_etcd_io.raft.v3.traceConfChangeEvent
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ConfState
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

/-! ### The window (2026-11-02, stage II (r))

From `InitialState` to `appliedTo` no `ownRaftLog` holds: raft's view has caught up with the attach
record (`storCaught`: its floor at the record's applied bound `max b A`, its certified terms up to the
restored commit), while the struct is still at the base (`committed = applied = applying = b`), so
`FlOk`'s `fl ≤ applying` and `DtOk`'s `≤ committed` fail. The log is the raw struct
(`newLogWithSize`'s `l ↦ lv0`) beside the caught-up view; the window's reads (`lastIndex`,
`lastEntryID`) and writes (`loadState`, `appliedTo`) are proved here on that, over their bodies, and
`newLogWithSize`'s wand seals `ownRaftLog` once `appliedTo` is done. -/

/-- `raftLog.lastIndex` in the window: nothing unstable, so the storage's `LastIndex`. -/
private theorem wp_lastIndex_w (l : Loc) (lv : raftLog) (si : GoInterfaceOk) (sn : StorNames)
    (σ : StorState) (Hst : lv.storage' = interface.ok si) (Hsn : lv.unstable'.snapshot' = null)
    (Hen : lv.unstable'.entries'.len = W64 0) (Hpend : σ.pend = []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ l ↦ lv ∗
        isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ }}
      (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"lastIndex")) (Val #()))
    {{ (li : w64), RET #li; l ↦ lv ∗ ownStorage sn (interface.ok si) σ ∗
        ⌜uint.Z li = uint.Z σ.prev.index' + (σ.ents.length : Int)⌝ }} := by
  wp_start as ⟨Hl, #HisSto, HSto⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  rw [Hen]
  wp_auto
  rw [Hsn]
  wp_auto
  ihave #Hsto : isStorageWith (ownStorage sn (interface.ok si)) (storCut (interface.ok si))
    (svCert sn) (interface.ok si) $$ [HisSto]
  · unfold isStorageD; iexact HisSto
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  rw [Hst]
  wp_auto
  cases Hstok
  wp_apply HLastIndex $$ [$HSto] as %li ⟨%Hli, HSto⟩
  · ipureintro; exact Hpend
  iapply HΦ
  iframe Hl HSto
  ipureintro; exact Hli

/-- `raftLog.firstIndex` in the window: no snapshot pending, so the storage's `FirstIndex`. -/
private theorem wp_firstIndex_w (l : Loc) (lv : raftLog) (si : GoInterfaceOk) (sn : StorNames)
    (σ : StorState) (Hst : lv.storage' = interface.ok si) (Hsn : lv.unstable'.snapshot' = null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ l ↦ lv ∗
        isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ }}
      (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"firstIndex")) (Val #()))
    {{ (fi : w64), RET #fi; l ↦ lv ∗ ownStorage sn (interface.ok si) σ ∗
        ⌜uint.Z σ.prev.index' + 1 ≤ uint.Z fi ∧
          uint.Z fi ≤ max (uint.Z σ.prev.index') (uint.Z σ.fl) + 1⌝ }} := by
  wp_start as ⟨Hl, #HisSto, HSto⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  rw [Hsn]
  wp_auto
  ihave #Hsto : isStorageWith (ownStorage sn (interface.ok si)) (storCut (interface.ok si))
    (svCert sn) (interface.ok si) $$ [HisSto]
  · unfold isStorageD; iexact HisSto
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  rw [Hst]
  wp_auto
  cases Hstok
  wp_apply HFirstIndex $$ [$HSto] as %fi ⟨%Hfi, -, HSto⟩
  iapply HΦ
  iframe Hl HSto
  ipureintro; exact Hfi

/-- `raftLog.lastEntryID` in the window: the storage's last index, and its term there, which the
storage holds (the client compacts at most to the floor, at most the last index). -/
private theorem wp_lastEntryID_w (l : Loc) (lv : raftLog) (si : GoInterfaceOk) (sn : StorNames)
    (σ : StorState) (Hst : lv.storage' = interface.ok si) (Hsn : lv.unstable'.snapshot' = null)
    (Hen : lv.unstable'.entries'.len = W64 0) (Hpend : σ.pend = [])
    (Hoff : uint.Z lv.unstable'.offset' = uint.Z σ.prev.index' + (σ.ents.length : Int) + 1)
    (Hfl : uint.Z σ.fl ≤ uint.Z σ.prev.index' + (σ.ents.length : Int))
    (Hnw : uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 < 2 ^ 64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ l ↦ lv ∗
        isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ }}
      (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"lastEntryID")) (Val #()))
    {{ (e : entryID), RET #e; l ↦ lv ∗ ownStorage sn (interface.ok si) σ }} := by
  wp_start as ⟨Hl, #HisSto, HSto⟩
  ihave #Hinit := isInitialized_access $$ Hpkg
  iNamed Hinit
  wp_auto
  wp_apply wp_lastIndex_w l lv si sn σ Hst Hsn Hen Hpend $$ [$Hl $HisSto $HSto]
    as %li ⟨Hl, HSto, %Hli⟩
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  rw [decide_eq_true (show uint.Z li < uint.Z lv.unstable'.offset' by omega)]
  wp_auto
  rw [Hsn]
  wp_auto
  ihave #Hsto : isStorageWith (ownStorage sn (interface.ok si)) (storCut (interface.ok si))
    (svCert sn) (interface.ok si) $$ [HisSto]
  · unfold isStorageD; iexact HisSto
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  cases Hstok
  wp_apply wp_firstIndex_w l lv si sn σ Hst Hsn $$ [$Hl $HisSto $HSto] as %fi ⟨Hl, HSto, %Hfi⟩
  rw [decide_eq_false (show ¬ uint.Z (li + W64 1) < uint.Z fi by
    have : uint.Z (li + W64 1) = uint.Z li + 1 := by word
    omega)]
  wp_auto
  wp_apply wp_lastIndex_w l lv si sn σ Hst Hsn Hen Hpend $$ [$Hl $HisSto $HSto]
    as %li2 ⟨Hl, HSto, %Hli2⟩
  rw [decide_eq_false (show ¬ uint.Z li2 < uint.Z li by omega)]
  wp_auto
  rw [Hst]
  wp_auto
  wp_apply HTerm $$ %σ %li %errCompacted [$HSto] as %t %err ⟨Ht, HSto⟩
  · isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; intro e0 He0; rw [Hpend] at He0; cases He0
    iexact ErrCompacted
  icases Ht with (%Ht | ⟨%Ht, -⟩)
  · obtain ⟨rfl, -⟩ := Ht
    wp_auto
    iapply HΦ
    iframe Hl HSto
  · exfalso; omega

/-- `raftLog.appliedTo(i, 0)` in the window, from `applying ≤ i` with nothing applying: `applied`
and `applying` move to `i`, the rest as it was. -/
private theorem wp_appliedTo_w (l : Loc) (lv : raftLog) (i : w64)
    (Hi : uint.Z lv.applied' ≤ uint.Z i ∧ uint.Z i ≤ uint.Z lv.committed')
    (Hapg : uint.Z lv.applying' ≤ uint.Z i) (Hasz : lv.applyingEntsSize' = W64 0)
    (Hamx : 0 < uint.Z lv.maxApplyingEntsSize') (Hpz : lv.applyingEntsPaused' = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ l ↦ lv }}
      (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"appliedTo")) (Val #i))
        (Val #(W64 0)))
    {{ RET #(); l ↦ { lv with applied' := i, applying' := i } }} := by
  wp_start as Hl
  wp_auto
  rw [decide_eq_false (show ¬ (uint.Z lv.committed' < uint.Z i) by omega)]
  wp_auto
  rw [decide_eq_false (show ¬ (uint.Z i < uint.Z lv.applied') by omega)]
  wp_auto
  wp_func_call
  wp_call
  wp_if_destruct
  · exfalso; omega
  rw [Hasz, decide_eq_false (show ¬ uint.Z (W64 0) < uint.Z (W64 0) by decide)]
  wp_auto
  iapply HΦ
  iExactEq Hl
  rw [decide_eq_false (show ¬ uint.Z lv.maxApplyingEntsSize' ≤ uint.Z (W64 0) by
    have : uint.Z (W64 0) = 0 := rfl
    omega), ← Hpz]

/-- `raft.loadState(hs)` in the window, on the raft struct's fields it touches: the commit index
within `[committed, lastIndex]` (the storage's last index), so no `Panicf`. -/
private theorem wp_loadState_w
    (wp_HardState_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_HardState_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_HardState_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (r l : Loc) (lv : raftLog) (t0 v0 : w64) (si : GoInterfaceOk) (sn : StorNames)
    (σ : StorState) (hp : Loc) (hs : HardStateM) (Hst : lv.storage' = interface.ok si)
    (Hsn : lv.unstable'.snapshot' = null) (Hen : lv.unstable'.entries'.len = W64 0)
    (Hpend : σ.pend = [])
    (Hc : uint.Z lv.committed' ≤ uint.Z hs.Commit' ∧
      uint.Z hs.Commit' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"raftLog"] ↦ l ∗
        r.[raft, go!"Term"] ↦ t0 ∗ r.[raft, go!"Vote"] ↦ v0 ∗ l ↦ lv ∗
        isStorageD sn (interface.ok si) ∗ ownStorage sn (interface.ok si) σ ∗ hsRO hp hs }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"loadState")) (Val #hp))
    {{ RET #(); r.[raft, go!"raftLog"] ↦ l ∗ r.[raft, go!"Term"] ↦ hs.Term' ∗
        r.[raft, go!"Vote"] ↦ hs.Vote' ∗ l ↦ { lv with committed' := hs.Commit' } ∗
        ownStorage sn (interface.ok si) σ }} := by
  wp_start as ⟨HrL, HrT, HrV, Hl, #HisSto, HSto, #Hhs⟩
  try wp_auto
  wp_apply wp_HardState_GetCommit.1 hp hs $$ [$Hhs]
  try wp_auto
  rw [decide_eq_false (show ¬ uint.Z hs.Commit' < uint.Z lv.committed' by omega)]
  try wp_auto
  wp_apply wp_HardState_GetCommit.1 hp hs $$ [$Hhs]
  wp_apply wp_lastIndex_w l lv si sn σ Hst Hsn Hen Hpend $$ [$Hl $HisSto $HSto]
    as %li ⟨Hl, HSto, %Hli⟩
  rw [decide_eq_false (show ¬ uint.Z li < uint.Z hs.Commit' by omega)]
  try wp_auto
  wp_apply wp_HardState_GetCommit.1 hp hs $$ [$Hhs]
  try wp_auto
  wp_apply wp_HardState_GetTerm.1 hp hs $$ [$Hhs]
  try wp_auto
  wp_apply wp_HardState_GetVote.1 hp hs $$ [$Hhs]
  try wp_auto
  iapply HΦ
  iframe

/-- `raft.switchToConfig(cfg, trk)` in the window, at a follower, on the raft struct's fields it
touches: the configuration installed, the conf state of it returned (the follower's arm: no
`becomeFollower`, no broadcast). -/
private theorem wp_switchToConfig_w
    (wp_traceConfChangeEvent : traceConfChangeEvent.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_ConfState : tracker.ProgressTracker.ConfState.spec (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (lok : GoInterfaceOk) (b0 : Bool)
    (tv0 : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (pvs : GMap w64 Progress)
    (Hmi : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"trk"] ↦ tv0 ∗
        r.[raft, go!"id"] ↦□ id ∗ r.[raft, go!"logger"] ↦□ interface.ok lok ∗ isLogger lok ∗
        r.[raft, go!"isLearner"] ↦ b0 ∗ r.[raft, go!"state"] ↦ StateFollower ∗
        tv0.Votes' ↦$ votes ∗ ownConfigC c cfgv prsm prs pvs }}
      (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
        (Val #cfgv)) (Val #prsm))
    {{ (cs : Loc) (xs os ls lns : List w64) (b : Bool), RET #cs;
        r.[raft, go!"trk"] ↦ { tv0 with Config' := cfgv, Progress' := prsm } ∗
        ownTrackerC c { tv0 with Config' := cfgv, Progress' := prsm } ⟨votes, prs, pvs⟩ ∗
        r.[raft, go!"isLearner"] ↦ b ∗ r.[raft, go!"state"] ↦ StateFollower ∗
        csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns c.autoLeave) true ∗
        ⌜xs ≡ₚ elements c.incoming ∧ os ≡ₚ elements c.outgoing ∧ ls ≡ₚ elements c.learners ∧
          lns ≡ₚ elements c.learnersNext⌝ }} := by
  wp_start as ⟨Htrkf, #Hid, #Hlgf, #Hlg, HiL, Hst, Hvotes, Hnew⟩
  wp_auto
  wp_apply wp_traceConfChangeEvent
  try wp_auto
  -- the log line
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  wp_apply Logger.wp_logf lok _ _ _ (by decide) $$ Hlg
  try wp_auto
  -- `cs := r.trk.ConfState()`
  ihave Htrk := ownTrackerC_reconfig c tv0 votes cfgv prsm prs pvs Hmi $$ Hvotes Hnew
  wp_apply wp_ProgressTracker_ConfState c _ _ _ $$ [$Htrkf $Htrk]
    as %cs %xs %os %ls %lns ⟨Htrkf, Htrk, Hcs, %Hcs0⟩
  -- `pr, ok := r.trk.Progress[r.id]`
  icases ownTrackerC_progress_map c _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  try wp_auto
  wp_apply wp_map_lookup2 $$ Hprs as -
  dsimp only
  cases Hlk : prs !! id with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    try wp_auto
    iapply HΦ
    iframe Htrkf Htrk HiL Hst Hcs
    ipureintro; exact Hcs0
  | some pr =>
    simp only [Option.getD_some, Option.isSome_some]
    try wp_auto
    icases ownTrackerC_lookup_same c _ _ id pr Hlk $$ Htrk with ⟨%p, %Hpv, Hpr, Hprback⟩
    iNamed Hpr
    wp_auto
    ihave Htrk := Hprback $$ [Hpv Hinfl]
    · iapply ownProgress_intro $$ Hpv Hinfl
      ipureintro; exact Habs
    cases pv.IsLearner'
    all_goals
      wp_auto
      iapply HΦ
      iframe Htrkf Htrk HiL Hst Hcs
      ipureintro; exact Hcs0

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
  -- PORT(durability stage II, the window; 2026-11-02, stage II (p): blocked, not attempted in full):
  -- from `InitialState` to `appliedTo` no `ownRaftLog` exists when `A > b` or the stored commit is
  -- above `b`: the client may compact up to `max b A` from the attach on (`raftBnd`'s attach
  -- reading), so the view needs its floor there (`storCaught`), while `ownRaftLog`'s `FlOk` wants the
  -- floor at most `applying`, which is `b` until `appliedTo`; and its `DtOk` wants the attach record's
  -- certified terms at most `committed`, `b` until `loadState`. The decision (coordinator, 2026-11-02):
  -- window variants of `lastEntryID`, `switchToConfig`, `loadState`, `appliedTo` over the raw log
  -- (`newLogWithSize`'s `l ↦ lv0`, closed by its wand at the end), or their bodies inlined. They
  -- cascade: `lastEntryID` reads through `raftLog.lastIndex`/`raftLog.term` (both over `ownRaftLog`,
  -- 90 + 273 lines), `switchToConfig` (589 lines) returns through a wand that must seal
  -- `ownRaftPhys` (so a struct variant over the raw log too). See
  -- `notes/raft-durability-proof-plan.md`, "Stage II (p)".
  sorry

end proof

end EtcdGrove
end Perennial
