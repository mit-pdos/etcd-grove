/-
Applying a configuration change (`raft.applyConfChange`, `RawNode.ApplyConfChange`),
Lean-first (2026-10-13, reconfiguration stage D): changes that leave the configuration
unchanged.

* The model of `applyConfChange`'s choice (`ccApplyM`: `LeaveJoint`, `EnterJoint` or
  `Simple`, on the `ConfChangeV2` that `AsV2` makes of the change, `ccV2Of`), and the state
  `confchange` sees of the node's configuration (`cfgState cfg`: the voters `cfg`, nothing
  else, every tracked `Progress` a non-learner). The scope of these specs is a change whose
  model answer is that same state (`ccApplyM ... (cfgState cfg) = some (cfgState cfg)`); only
  `Simple` can answer that (`ccApplyM_noop`), e.g. for a change with `NodeId = 0`, which
  `Changer.apply` skips (`ccApplyM_single_noop`).
* `ownTracker_toCC`: the node's tracker as the `Changer` reads it (`ownTrackerCC`), the old
  `Progress` objects' inflight rings set apart (`progRAt`).
* `ownResult_noop_transfer`: `Simple`'s result, with the rings moved to the new `Progress`
  objects (copies, or fresh ones), as `switchToConfig` takes it (`ownConfigV`), each new
  `Match` the old one or `0` (`MatchKept`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.InvConfchange
public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The model -/

section model
variable [FfiSyntax]

/-- Every voter of `cfg` tracked, as a non-learner. -/
def cfgFlags (cfg : GSet w64) : GMap w64 Bool := GMap.fmap (fun _ => false) cfg

/-- The configuration `cfg` as a `Config`: voters only. -/
def cfgM (cfg : GSet w64) : CfgM :=
  { incoming := cfg, outgoing := ∅, learners := ∅, learnersNext := ∅, autoLeave := false }

/-- What `confchange` sees of a node whose configuration is `cfg` (`ownTracker`). -/
def cfgState (cfg : GSet w64) : CCState := { cfg := cfgM cfg, prs := cfgFlags cfg }

/-- What `ConfChangeI.AsV2()` makes of a change: a `ConfChange` is one change with
transition `Auto` (`ConfChange.AsV2`'s spec); a `ConfChangeV2` is itself. -/
def ccV2Of : CCMsg → raftpb.ConfChangeTransition × List raftpb.ConfChangeSingle
  | .v1 m => (W32 0, [{ Type' := m.type, NodeId' := m.nodeId }])
  | .v2 m => (m.transition, m.changes)

/-- `raft.applyConfChange`'s choice (raft.go): `LeaveJoint` for an empty `Auto` change,
else `EnterJoint` when `ConfChangeV2.EnterJoint` says so, else `Simple`; `none` where
`EnterJoint` panics (an undefined transition with joint consensus). -/
def ccApplyM (t : raftpb.ConfChangeTransition) (ccs : List raftpb.ConfChangeSingle)
    (s : CCState) : Option CCState :=
  if t = W32 0 ∧ ccs = [] then leaveJointM s
  else match enterJointOf t ccs.length with
    | some (al, true) => enterJointM al ccs s
    | some (_, false) => simpleM ccs s
    | none => none

theorem cfgFlags_mem (cfg : GSet w64) (k : w64) : k ∈ cfgFlags cfg ↔ k ∈ cfg := by
  simp [cfgFlags, GMap.mem_iff, GMap.lookup_fmap]

theorem cfgInv_cfgState (cfg : GSet w64) : CfgInv (cfgState cfg) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun _ => ⟨rfl, rfl⟩⟩
  · rcases hk with hk | hk | hk | hk
    · exact (cfgFlags_mem cfg k).2 hk
    all_goals simp [cfgState, cfgM, GMap.mem_iff] at hk
  · simp [cfgState, cfgM, GMap.mem_iff] at hk
  · simp [cfgState, cfgM, GMap.mem_iff] at hk

theorem clearAutoLeave_cfgState (cfg : GSet w64) :
    clearAutoLeave (cfgState cfg) = cfgState cfg := rfl

theorem applyOne_outgoing (c : raftpb.ConfChangeSingle) (s s' : CCState)
    (h : applyOne c s = some s') : s'.cfg.outgoing = s.cfg.outgoing := by
  unfold applyOne at h
  by_cases h0 : c.NodeId' = W64 0
  · rw [if_pos h0] at h; cases h; rfl
  rw [if_neg h0] at h
  by_cases h1 : c.Type' = W32 0
  · rw [if_pos h1] at h; cases h
    unfold makeVoterM; split
    · rfl
    · simp [initProgressM]
  rw [if_neg h1] at h
  by_cases h3 : c.Type' = W32 3
  · rw [if_pos h3] at h; cases h
    unfold makeLearnerM
    split
    · simp [initProgressM]
    · rfl
    · split <;> rfl
  rw [if_neg h3] at h
  by_cases h4 : c.Type' = W32 1
  · rw [if_pos h4] at h; cases h
    unfold removeM; split <;> rfl
  rw [if_neg h4] at h
  by_cases h2 : c.Type' = W32 2
  · rw [if_pos h2] at h; cases h; rfl
  rw [if_neg h2] at h
  cases h

theorem applyAll_outgoing (ccs : List raftpb.ConfChangeSingle) (s s' : CCState)
    (h : applyAll ccs s = some s') : s'.cfg.outgoing = s.cfg.outgoing := by
  induction ccs generalizing s with
  | nil => simp only [applyAll, Option.some.injEq] at h; rw [h]
  | cons c ccs ih =>
    simp only [applyAll] at h
    cases h1 : applyOne c s with
    | none => rw [h1] at h; cases h
    | some s1 =>
      rw [h1, Option.bind_some] at h
      rw [ih s1 h, applyOne_outgoing c s s1 h1]

theorem applyM_outgoing (ccs : List raftpb.ConfChangeSingle) (s s' : CCState)
    (h : applyM ccs s = some s') : s'.cfg.outgoing = s.cfg.outgoing := by
  unfold applyM at h
  cases h1 : applyAll ccs s with
  | none => rw [h1] at h; cases h
  | some s1 =>
    rw [h1, Option.bind_some] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; exact applyAll_outgoing ccs s _ h1

/-- A change whose model answer is the configuration it started from is a `Simple` one:
`LeaveJoint` fails on a non-joint configuration, and `EnterJoint` answers a joint one. -/
theorem ccApplyM_noop (cfg : GSet w64) (t : raftpb.ConfChangeTransition)
    (ccs : List raftpb.ConfChangeSingle)
    (H : ccApplyM t ccs (cfgState cfg) = some (cfgState cfg)) :
    ¬ (t = W32 0 ∧ ccs = []) ∧ (∃ al, enterJointOf t ccs.length = some (al, false)) ∧
      simpleM ccs (cfgState cfg) = some (cfgState cfg) := by
  unfold ccApplyM at H
  by_cases Hl : t = W32 0 ∧ ccs = []
  · rw [if_pos Hl] at H
    unfold leaveJointM at H
    rw [if_neg (fun h => h (cfgInv_cfgState cfg)),
      if_pos (show (cfgState cfg).cfg.outgoing = ∅ from rfl)] at H
    cases H
  rw [if_neg Hl] at H
  refine ⟨Hl, ?_⟩
  rcases He : enterJointOf t ccs.length with _ | ⟨al, ok⟩
  · rw [He] at H; cases H
  rw [He] at H
  cases ok
  · exact ⟨⟨al, rfl⟩, H⟩
  · exfalso
    simp only at H
    unfold enterJointM at H
    rw [if_neg (fun h => h (cfgInv_cfgState cfg)), if_neg (fun h => h rfl)] at H
    by_cases Hin : (cfgState cfg).cfg.incoming = ∅
    · rw [if_pos Hin] at H; cases H
    rw [if_neg Hin] at H
    revert H
    generalize Happ : applyM ccs _ = r
    cases r with
    | none => intro H; cases H
    | some s1 =>
      intro H
      simp only [checkedM] at H
      split at H
      · simp only [Option.some.injEq] at H
        have Hout := applyM_outgoing ccs _ s1 Happ
        have h2 : s1.cfg.outgoing = (cfgState cfg).cfg.outgoing := by rw [← H]
        rw [h2] at Hout
        exact Hin Hout.symm
      · cases H

/-- A single change with `NodeId = 0` and transition `Auto` (what `ConfChange.AsV2` makes of
any `ConfChange` with `NodeId = 0`) leaves a non-empty configuration as it is:
`Changer.apply` skips it. -/
theorem ccApplyM_single_noop (cfg : GSet w64) (c : raftpb.ConfChangeSingle)
    (Hc : c.NodeId' = W64 0) (Hne : cfg ≠ ∅) :
    ccApplyM (W32 0) [c] (cfgState cfg) = some (cfgState cfg) := by
  have Happ : applyM [c] (cfgState cfg) = some (cfgState cfg) := by
    simp only [applyM, applyAll, applyOne, Hc, ↓reduceIte, Option.bind_some]
    rw [if_neg (by exact Hne)]
  have Hsd : ¬ SymdiffTooBig cfg cfg := by
    unfold SymdiffTooBig symdiffN
    rw [GMap.map_difference_diag, GMap.map_size_empty]
    decide
  have Hs : simpleM [c] (cfgState cfg) = some (cfgState cfg) := by
    unfold simpleM
    rw [clearAutoLeave_cfgState, if_neg (fun h => h (cfgInv_cfgState cfg)),
      if_neg (fun h => h rfl), Happ]
    simp only
    rw [if_neg (show ¬ SymdiffTooBig (cfgState cfg).cfg.incoming (cfgState cfg).cfg.incoming
      from Hsd)]
    simp [checkedM, cfgInv_cfgState]
  unfold ccApplyM
  rw [if_neg (by simp)]
  have He : enterJointOf (W32 0) [c].length = some (false, false) := by
    simp [enterJointOf]
  rw [He]
  exact Hs

/-- A `ConfChange` with `NodeId = 0`. -/
theorem ccApplyM_v1_noop (cfg : GSet w64) (m : CCV1M) (H : m.nodeId = W64 0) (Hne : cfg ≠ ∅) :
    ccApplyM (ccV2Of (.v1 m)).1 (ccV2Of (.v1 m)).2 (cfgState cfg) = some (cfgState cfg) :=
  ccApplyM_single_noop cfg _ H Hne

end model

/-! ## The tracker as a `Changer` reads it, and the result as `switchToConfig` takes it -/

section heap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `ownProgress pr p` holds besides the points-to, for the record `peers` holds at `k`:
the inflight ring and that the value is a non-learner `Progress` of the record. -/
def progRAt (peers : GMap w64 Progress) (k : w64) (pv : tracker.Progress) : IProp GF :=
  iprop(∃ p, ⌜peers !! k = some p⌝ ∗ ownInflights pv.Inflights' p.infl ∗
    ⌜progressAbs pv p.infl = some p⌝)

/-- A set is its own domain. -/
theorem domSet_gset (s : GSet w64) : domSet s = s := by
  apply GMap.map_eq; intro k
  simp only [domSet, GMap.lookup_fmap]
  cases s !! k <;> rfl

/-- The node's tracker as the `Changer` reads it: the configuration `cfgM cfg`, the
progress map (read-only) and the `Progress` objects with their values `pvs`, every one a
non-learner; the inflight rings set apart, and the tally. The old objects and voter map are
garbage once `switchToConfig` has installed the new ones; their rings go to the copies
(`ownResult_noop_transfer`). -/
theorem ownTracker_toCC (cfg : GSet w64) (tv : tracker.ProgressTracker) (t : Trk) :
    ownTracker (GF := GF) cfg tv t ⊢ ∃ (pvs : GMap w64 tracker.Progress),
      ownTrackerCC tv (DFrac.own 1) DFrac.discard (DFrac.own 1) (cfgM cfg) t.prs pvs ∗
      ([∗map] k ↦ pv ∈ pvs, progRAt t.peers k pv) ∗
      tv.Votes' ↦$ t.votes ∗
      ⌜flagsOf pvs = cfgFlags cfg⌝ ∗
      ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝ ∗
      ⌜(GMap.size cfg : Int) ≤ 2 ^ 62⌝ := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  obtain ⟨rfl, rfl⟩ := Hno_learners
  -- the values of the `Progress` objects, and their rings apart
  ihave H : ([∗map] k ↦ pr;p ∈ t.prs;t.peers, ∃ pv : tracker.Progress,
      (pr ↦ pv ∗ (⌜pv.IsLearner' = false⌝ ∗ (emp ∗ progRAt (GF := GF) t.peers k pv)) : IProp GF))
      $$ [Hprogs]
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr p} _ hp => ?_)) $$ Hprogs
    iintro Hp
    unfold ownProgress
    iNamed Hp
    iexists pv
    iframe Hpv
    isplitr
    · ipureintro; exact ((progressAbs_Some _ _ _).1 Habs).1
    isplitr
    · iempintro
    unfold progRAt
    iexists p
    iframe Hinfl
    ipureintro; exact ⟨hp, Habs⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ H
  have Hdom0' : ∀ k, (t.prs !! k).isSome ↔ (t.peers !! k).isSome := Hdom0
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun k pr => iprop(∃ pv : tracker.Progress,
      (pr ↦ pv ∗ (⌜pv.IsLearner' = false⌝ ∗ (emp ∗ progRAt (GF := GF) t.peers k pv)) : IProp GF)))
    (Φ2 := fun (_ : w64) (_ : Progress) => (emp : IProp GF)) Hdom0).1 $$ [H] with ⟨H, -⟩
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr p} _ _ => ?_)) $$ H
    iintro H; iframe H
  icases bigSepM_exist_sepM2 t.prs _ $$ H with ⟨%pvs, H⟩
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ H
  have Hdom' : ∀ k, (t.prs !! k).isSome ↔ (pvs !! k).isSome := Hdom
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hpt, H⟩
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hl, H⟩
  ihave %Hlf := BigSepM2.bigSepM2_pure_intro $$ Hl
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun k pv => progRAt (GF := GF) t.peers k pv) Hdom).1 $$ H with ⟨-, HR⟩
  iexists pvs
  iframe HR Hvotes
  isplitl [Hvoters Hpt Hlearners HlearnersNext]
  · unfold ownTrackerCC
    iframe Hpt
    isplitl [Hvoters Hlearners HlearnersNext]
    · have Hv : voters = cfg := by rw [← Hvoters_dom, domSet_gset]
      subst Hv
      iapply ownCfgCC_intro tv.Config' (DFrac.own 1) (cfgM voters) voters_ref map.nil
        Hvoters_arr Hautoleave $$ [Hvoters] [] [Hlearners] [HlearnersNext]
      · simp only [cfgM]; iexact Hvoters
      · simp only [cfgM]; iapply ownIdsetC_nil
      · simp only [cfgM]; iexact Hlearners
      · simp only [cfgM]; iexact HlearnersNext
    · iexact Hprs
  ipureintro
  refine ⟨?_, HmaxInfl, Hcfg_size⟩
  apply GMap.map_eq; intro k
  rw [flagsOf_lookup']
  simp only [cfgFlags, GMap.lookup_fmap]
  have Hk : (pvs !! k).isSome ↔ (cfg !! k).isSome := by
    rw [← Hdom' k]
    exact mem_of_domSet_eq (a := t.prs) (b := cfg) (by rw [Hprs_dom, domSet_gset]) k
  cases hpv : pvs !! k with
  | none =>
    rw [hpv] at Hk
    cases hc : cfg !! k with
    | none => rfl
    | some _ => rw [hc] at Hk; simp at Hk
  | some pv =>
    rw [hpv] at Hk
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom' k).2 (by rw [hpv]; rfl))
    have Hl0 := Hlf k pr pv hpr hpv
    obtain ⟨u, hc⟩ := Option.isSome_iff_exists.1 (Hk.1 rfl)
    rw [hc]
    simp [Hl0]

/-- What `Simple`'s result is, once the old objects' rings are moved to it: each new object
an `ownProgress` (`Q`), its record the old one or one with `Match = 0`. -/
private def newPrQ (peers : GMap w64 Progress) (k : w64) (pv : tracker.Progress) : IProp GF :=
  iprop(∃ p, ownInflights pv.Inflights' p.infl ∗
    ⌜pv.IsLearner' = false → progressAbs pv p.infl = some p ∧
      (uint.Z p.matched = 0 ∨ ∃ p0, peers !! k = some p0 ∧ p0.matched = p.matched)⌝)

/-- `Simple`'s result for an unchanged configuration (`cfgState cfg`), with the old objects'
inflight rings moved to the new ones (`ownNewPr_transfer`): the configuration and progress
map `switchToConfig` takes (`ownConfigV`, the progress map made read-only), each new `Match`
the old one or `0` (`MatchKept`). -/
theorem ownResult_noop_transfer (cfg : GSet w64) (chg : confchange.Changer)
    (base : GMap w64 tracker.Progress) (peers : GMap w64 Progress) (cfgv : tracker.Config)
    (trk : Loc) (Hsz : (GMap.size cfg : Int) ≤ 2 ^ 62) :
    ownCfgCC (GF := GF) cfgv (DFrac.own 1) (cfgM cfg) ∗
      ownPrsW chg base trk (cfgFlags cfg) ∗
      ([∗map] k ↦ pv ∈ base, progRAt peers k pv) ⊢
      |==> ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
        ownConfigV cfg cfgv trk prs pvs ∗ ⌜MatchKept peers pvs⌝ := by
  iintro ⟨Hc, Hw, HR⟩
  icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
  icases ownIdsetC_nil_of _ _ (cfgM cfg).outgoing rfl $$ Hout with %Hvout
  icases ownIdsetC_nil_of _ _ (cfgM cfg).learners rfl $$ Hl with %Hl
  icases ownIdsetC_nil_of _ _ (cfgM cfg).learnersNext rfl $$ Hln with %Hln
  subst Hvout
  unfold ownPrsW
  icases Hw with ⟨%prs, %pvs, Htrk, Hprs, %Hflags, Hnew⟩
  -- the rings, to the new objects
  ihave HQ := ownNewPr_transfer chg base (fun k pv => progRAt (GF := GF) peers k pv)
      (fun k pv => newPrQ (GF := GF) peers k pv) ?_ ?_ pvs $$ [$HR $Hnew]
  · -- a copy
    intro k pv0 pv _ h1
    unfold progRAt newPrQ
    iintro ⟨%p, %Hp, Hinfl, %Habs⟩
    iexists p
    have Hinf : pv.Inflights' = pv0.Inflights' := by rw [h1]
    rw [Hinf]
    iframe Hinfl
    ipureintro
    intro Hl
    have Hl0 := ((progressAbs_Some _ _ _).1 Habs).1
    have h2 : ({ pv0 with IsLearner' := false } : tracker.Progress) = pv0 := by
      cases pv0; simp only at Hl0; subst Hl0; rfl
    have Heq : pv = pv0 := by
      rw [h1]; rw [Hl]; exact h2
    subst Heq
    exact ⟨Habs, .inr ⟨p, Hp, rfl⟩⟩
  · -- a fresh one
    intro k pv Hf
    unfold newPrQ
    iintro Hinfl
    iexists progressOf pv .probe (inflightsNew chg.Tracker'.MaxInflight'
      chg.Tracker'.MaxInflightBytes')
    isplitl [Hinfl]
    · simp only [progressOf]; iexact Hinfl
    ipureintro
    intro Hl
    obtain ⟨Hm, -, -, Hst, -, -, -⟩ := Hf
    refine ⟨(progressAbs_Some _ _ _).2 ⟨Hl, Hst, rfl, rfl, rfl, rfl, rfl, rfl⟩, .inl ?_⟩
    simp only [progressOf, Hm]; rfl
  -- every new object a non-learner, the domain `cfg`
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdom : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome := Hdom0
  have Hlf : ∀ k pv, pvs !! k = some pv → pv.IsLearner' = false := by
    intro k pv h
    have h' := flagsOf_lookup pvs k pv h
    rw [Hflags] at h'
    simp only [cfgFlags, GMap.lookup_fmap] at h'
    cases hc : cfg !! k with
    | none => rw [hc] at h'; cases h'
    | some _ => rw [hc] at h'; simp at h'; exact h'
  have Hpdom : domSet prs = cfg := by
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom', GMap.mem_iff, Hdom k, ← flagsOf_mem, Hflags, cfgFlags_mem]
  -- the objects, as `ownProgress`es with their records
  ihave HQ2 := (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun k pv => newPrQ (GF := GF) peers k pv) (m1 := prs) (m2 := pvs) Hdom0).2 $$ [HQ]
  · isplitr
    · iapply (BigSepM.bigSepM_emp (m := prs)).2
      iempintro
    · iexact HQ
  ihave H := BigSepM2.bigSepM2_sep_eqv.2 $$ [$Hprs $HQ2]
  ihave H : ([∗map] k ↦ pr;pv ∈ prs;pvs, ((∃ p, ownProgress pr p ∗
      ⌜uint.Z p.matched = 0 ∨ ∃ p0, peers !! k = some p0 ∧ p0.matched = p.matched⌝) ∗ emp :
        IProp GF)) $$ [H]
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr pv} _ hpv => ?_)) $$ H
    iintro ⟨Hp, -, HQ⟩
    unfold newPrQ
    icases HQ with ⟨%p, Hinfl, %Hp⟩
    obtain ⟨Habs, Hm⟩ := Hp (Hlf k pv hpv)
    isplitl
    · iexists p
      isplitl
      · iapply ownProgress_intro _ _ p $$ Hp Hinfl
        ipureintro; exact Habs
      · ipureintro; exact Hm
    · iempintro
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun k pr => iprop(∃ p, ownProgress (GF := GF) pr p ∗
      ⌜uint.Z p.matched = 0 ∨ ∃ p0, peers !! k = some p0 ∧ p0.matched = p.matched⌝))
    (Φ2 := fun (_ : w64) (_ : tracker.Progress) => (emp : IProp GF)) (m1 := prs) (m2 := pvs)
    Hdom0).1 $$ H with ⟨H, -⟩
  icases bigSepM_exist_sepM2 prs _ $$ H with ⟨%ps, H⟩
  ihave %Hdom2 := BigSepM2.bigSepM2_lookup_iff $$ H
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hprogs, Hmk⟩
  ihave %Hmk := BigSepM2.bigSepM2_pure_intro $$ Hmk
  ihave Hin := (show (vin ↦$ (cfgM cfg).incoming : IProp GF) ⊢ vin ↦$ cfg from .rfl) $$ Hin
  have Hdom2' : ∀ k, (prs !! k).isSome ↔ (ps !! k).isSome := Hdom2
  imod ownMap_persist $$ Htrk with #Htrk
  imodintro
  iexists prs, ps
  isplitl
  · unfold ownConfigV
    iexists vin, cfg
    simp only [named]
    iframe Hin Htrk Hprogs
    ipureintro
    exact ⟨Harr, Hl, Hln, Hal, domSet_gset cfg, Hpdom, Hsz⟩
  · ipureintro
    intro k p' hp'
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp']; rfl))
    exact Hmk k pr p' hpr hp'

end heap

end EtcdGrove
end Perennial
