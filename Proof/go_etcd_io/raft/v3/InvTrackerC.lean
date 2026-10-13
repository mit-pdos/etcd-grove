/-
The progress tracker at any configuration (2026-10-13, reconfiguration stage A1),
Lean-first.

`ownTracker cfg tv t` (`InvTracker.lean`) is the tracker at a non-joint configuration with
the voters `cfg` (the learners the other tracked ids). `ownTrackerC c tv t` is the tracker at
any configuration `c : CfgM` the `confchange` package can produce -- joint (an outgoing voter
set), with learners and staged learners (`LearnersNext`), `AutoLeave` set or not:

* the configuration value is `ownCfgCC tv.Config' (DFrac.own 1) c` (`InvConfchange.lean`:
  the incoming voter map owned, the outgoing map, `Learners` and `LearnersNext` canonical,
  `nil` exactly when empty, `AutoLeave = c.autoLeave`), the representation `confchange`'s
  specs read and produce;
* the progress map tracks exactly the configuration's ids (`CfgM.ids`: the voters of both
  halves and the learners; a staged learner is an outgoing voter), each `Progress`'s
  `IsLearner` is whether its id is a learner (`LearnerFlagsC`), and the configuration is
  one `checkInvariants` accepts (`CfgInv`, on the flags);
* the vote map, the progress map (read-only, `DFrac.discard`) with the `Progress` objects,
  and the two bounds, as in `ownTracker`.

`ownTracker` is the special case: `ownTracker_toC` and `ownTrackerC_toSimple` convert at
`CfgM.simple cfg (domSet t.prs \ cfg)`. The quorum and tracker specs are stated on
`ownTrackerC` (their old statements derived, in their `Spec` files); `ownRaftPhysC`
(`InvRaftPhys.lean`) is the raft struct over it.

* `MajIdx`/`JCommittedIdx`: what `MajorityConfig.CommittedIndex`/`JointConfig.CommittedIndex`
  compute (the quorum index, `MaxUint64` for an empty half, the smaller of the two halves').
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfchange

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Pure vocabulary -/

/-- A set is its own domain. (Moved from `InvApplyConf.lean`, 2026-10-13.) -/
theorem domSet_gset (s : GSet w64) : domSet s = s := by
  apply GMap.map_eq; intro k
  simp only [domSet, GMap.lookup_fmap]
  cases s !! k <;> rfl

/-- Each tracked id's `IsLearner`, read off the tracker's `Progress` records: what
`confchange` sees of the progress map (`CCState.prs`). -/
def trkFlags (pvs : GMap w64 Progress) : GMap w64 Bool :=
  GMap.fmap (fun p => p.learner) pvs

theorem trkFlags_lookup (pvs : GMap w64 Progress) (k : w64) :
    trkFlags pvs !! k = (pvs !! k).map (fun p => p.learner) := by
  simp [trkFlags, GMap.lookup_fmap]

/-- The ids a configuration tracks: the voters of both halves and the learners (a staged
learner, in `LearnersNext`, is an outgoing voter). -/
def CfgM.ids (c : CfgM) : GSet w64 := c.voters ∪ c.learners

/-- Each tracked `Progress`'s `IsLearner` is whether its id is a learner of `c`. -/
def LearnerFlagsC (c : CfgM) (pvs : GMap w64 Progress) : Prop :=
  ∀ k p, pvs !! k = some p → p.learner = decide (k ∈ c.learners)

/-- A `Progress` given back with the same `IsLearner` keeps `LearnerFlagsC`. -/
theorem LearnerFlagsC.insert {c : CfgM} {pvs : GMap w64 Progress} {k : w64}
    {p p' : Progress} (H : LearnerFlagsC c pvs) (Hp : pvs !! k = some p)
    (Hl : p'.learner = p.learner) : LearnerFlagsC c (<[k := p']> pvs) := by
  intro j q Hq
  by_cases hj : j = k
  · subst hj
    rw [GMap.lookup_insert_eq] at Hq
    cases Hq
    rw [Hl]; exact H _ _ Hp
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hj)] at Hq
    exact H _ _ Hq

theorem trkFlags_insert_same (pvs : GMap w64 Progress) (k : w64) (p p' : Progress)
    (Hp : pvs !! k = some p) (Hl : p'.learner = p.learner) :
    trkFlags (<[k := p']> pvs) = trkFlags pvs := by
  apply GMap.map_eq; intro j
  rw [trkFlags_lookup, trkFlags_lookup]
  by_cases hj : j = k
  · subst hj; rw [GMap.lookup_insert_eq, Hp]; simp [Hl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hj)]

/-- What `MajorityConfig.CommittedIndex` returns for the voter set `s`: `MaxUint64` when it is
empty, else the quorum index of `f` over `s`. -/
def MajIdx (s : GSet w64) (f : w64 → w64) (N : w64) : Prop :=
  (s = ∅ → N = W64 (2 ^ 64 - 1)) ∧ (s ≠ ∅ → IsQuorumIndex s f N)

/-- What `JointConfig.CommittedIndex` returns for the halves `s0`, `s1`: the smaller of the
two halves' answers (Go: `if idx0 < idx1 { return idx0 }; return idx1`). -/
def JCommittedIdx (s0 s1 : GSet w64) (f : w64 → w64) (N : w64) : Prop :=
  ∃ N0 N1, MajIdx s0 f N0 ∧ MajIdx s1 f N1 ∧ N = (if uint.Z N0 < uint.Z N1 then N0 else N1)

/-- At a non-joint configuration (an empty outgoing half) the joint answer is the incoming
half's. -/
theorem JCommittedIdx_simple (s0 : GSet w64) (f : w64 → w64) (N : w64)
    (H : JCommittedIdx s0 ∅ f N) : MajIdx s0 f N := by
  obtain ⟨N0, N1, H0, H1, HN⟩ := H
  have h1 : N1 = W64 (2 ^ 64 - 1) := H1.1 rfl
  subst h1
  have : N = N0 := by
    rw [HN]
    split
    · rfl
    · rename_i h
      word
  subst this
  exact H0

/-! ### The simple configuration's facts -/

theorem cfgInv_simple (cfg : GSet w64) (prs : GMap w64 Loc) (pvs : GMap w64 Progress)
    (Hsub : cfg ⊆ domSet prs) (Hd : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome)
    (Hfl : LearnerFlags cfg pvs) :
    CfgInv ⟨CfgM.simple cfg (domSet prs \ cfg), trkFlags pvs⟩ := by
  have Htr : ∀ k, k ∈ domSet prs → ∃ p, pvs !! k = some p := by
    intro k hk
    rw [GMap.elem_of_dom', GMap.mem_iff, Hd] at hk
    exact Option.isSome_iff_exists.1 hk
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun _ => ⟨rfl, rfl⟩⟩
  · show k ∈ trkFlags pvs
    have hk' : k ∈ domSet prs := by
      dsimp only [CfgM.simple] at hk
      rcases hk with hk | hk | hk | hk
      · exact (GMap.elem_of_subseteq _ _).1 Hsub k hk
      · exact absurd hk (GMap.not_elem_of_empty _)
      · exact ((GMap.elem_of_difference _ _ _).1 hk).1
      · exact absurd hk (GMap.not_elem_of_empty _)
    obtain ⟨p, hp⟩ := Htr k hk'
    rw [GMap.mem_iff, trkFlags_lookup, hp]; rfl
  · exact absurd hk (GMap.not_elem_of_empty _)
  · dsimp only [CfgM.simple] at hk ⊢
    obtain ⟨hk1, hk2⟩ := (GMap.elem_of_difference _ _ _).1 hk
    obtain ⟨p, hp⟩ := Htr k hk1
    refine ⟨GMap.not_elem_of_empty _, hk2, ?_⟩
    rw [trkFlags_lookup, hp, Option.map_some, Hfl k p hp]
    simp [hk2]

theorem ids_simple (cfg : GSet w64) (prs : GMap w64 Loc) (Hsub : cfg ⊆ domSet prs) :
    domSet prs = (CfgM.simple cfg (domSet prs \ cfg)).ids := by
  apply GMap.set_eq; intro k
  unfold CfgM.ids CfgM.voters
  dsimp only [CfgM.simple]
  rw [GMap.elem_of_union, GMap.elem_of_union, GMap.elem_of_difference]
  constructor
  · intro h
    by_cases hc : k ∈ cfg
    · exact .inl (.inl hc)
    · exact .inr ⟨h, hc⟩
  · rintro ((h | h) | h)
    · exact (GMap.elem_of_subseteq _ _).1 Hsub k h
    · exact absurd h (GMap.not_elem_of_empty _)
    · exact h.1

theorem learnerFlagsC_simple (cfg : GSet w64) (prs : GMap w64 Loc) (pvs : GMap w64 Progress)
    (Hd : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome) (Hfl : LearnerFlags cfg pvs) :
    LearnerFlagsC (CfgM.simple cfg (domSet prs \ cfg)) pvs := by
  intro k p hp
  rw [Hfl k p hp]
  dsimp only [CfgM.simple]
  have hk : k ∈ domSet prs := by
    rw [GMap.elem_of_dom', GMap.mem_iff, Hd, hp]; rfl
  by_cases hc : k ∈ cfg
  · have : k ∉ domSet prs \ cfg := fun h => ((GMap.elem_of_difference _ _ _).1 h).2 hc
    simp [hc, this]
  · have : k ∈ domSet prs \ cfg := (GMap.elem_of_difference _ _ _).2 ⟨hk, hc⟩
    simp [hc, this]

/-- Back: at a non-joint configuration, `LearnerFlagsC` is `ownTracker`'s `LearnerFlags` at the
incoming voters, and the learners are the tracked ids outside them. -/
theorem learnerFlags_of_C (c : CfgM) (prs : GMap w64 Loc) (pvs : GMap w64 Progress)
    (Hd : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome)
    (Hinv : CfgInv ⟨c, trkFlags pvs⟩) (Hdom : domSet prs = c.ids) (Hfl : LearnerFlagsC c pvs)
    (ho : c.outgoing = ∅) :
    LearnerFlags c.incoming pvs ∧ c.learners = domSet prs \ c.incoming := by
  have Hl : c.learners = domSet prs \ c.incoming := by
    apply GMap.set_eq; intro k
    rw [Hdom, GMap.elem_of_difference]
    unfold CfgM.ids CfgM.voters
    rw [ho, GMap.union_empty_r_L, GMap.elem_of_union]
    constructor
    · intro h; exact ⟨.inr h, (Hinv.2.2.1 k h).2.1⟩
    · rintro ⟨h | h, h'⟩
      · exact absurd h h'
      · exact h
  refine ⟨fun k p hp => ?_, Hl⟩
  rw [Hfl k p hp]
  have hk : k ∈ domSet prs := by
    rw [GMap.elem_of_dom', GMap.mem_iff, Hd, hp]; rfl
  by_cases hc : k ∈ c.incoming
  · have : k ∉ c.learners := fun h => (Hinv.2.2.1 k h).2.1 hc
    simp [hc, this]
  · have : k ∈ c.learners := by rw [Hl]; exact (GMap.elem_of_difference _ _ _).2 ⟨hk, hc⟩
    simp [hc, this]

/-- The voters of a configuration are tracked. -/
theorem voters_sub_ids (c : CfgM) : c.voters ⊆ c.ids := by
  unfold CfgM.ids; rw [GMap.elem_of_subseteq]; intro k hk; exact GMap.elem_of_union_l _ hk

theorem incoming_sub_voters (c : CfgM) : c.incoming ⊆ c.voters := by
  unfold CfgM.voters; rw [GMap.elem_of_subseteq]; intro k hk; exact GMap.elem_of_union_l _ hk

theorem outgoing_sub_voters (c : CfgM) : c.outgoing ⊆ c.voters := by
  unfold CfgM.voters; rw [GMap.elem_of_subseteq]; intro k hk; exact GMap.elem_of_union_r _ hk

/-- A permutation of the elements of an empty set is empty. -/
theorem perm_elements_empty (xs : List w64) (H : xs ≡ₚ elements (∅ : GSet w64)) : xs = [] := by
  have := H.length_eq
  rw [GMap.length_elements, GMap.size_empty] at this
  exact List.eq_nil_of_length_eq_zero this

theorem learners_sub_ids (c : CfgM) : c.learners ⊆ c.ids := by
  unfold CfgM.ids; rw [GMap.elem_of_subseteq]; intro k hk; exact GMap.elem_of_union_r _ hk

/-- A staged learner is an outgoing voter, so tracked. -/
theorem learnersNext_sub_ids (c : CfgM) (prs : GMap w64 Bool) (H : CfgInv ⟨c, prs⟩) :
    c.learnersNext ⊆ c.ids := by
  rw [GMap.elem_of_subseteq]; intro k hk
  exact GMap.elem_of_union_l _ (GMap.elem_of_union_r _ (H.2.1 k hk).1)

theorem incoming_sub_ids (c : CfgM) : c.incoming ⊆ c.ids :=
  GMap.map_subseteq_trans (incoming_sub_voters c) (voters_sub_ids c)

theorem outgoing_sub_ids (c : CfgM) : c.outgoing ⊆ c.ids :=
  GMap.map_subseteq_trans (outgoing_sub_voters c) (voters_sub_ids c)

/-- A subset of the tracked ids is at most as large as the progress map. -/
theorem size_le_of_sub_dom {V : Type} (s : GSet w64) (prs : GMap w64 V) (H : s ⊆ domSet prs) :
    GMap.size s ≤ GMap.size prs := by
  have h := GMap.subseteq_size H
  rw [GMap.size_dom] at h
  exact h

/-! ## The tracker at a configuration -/

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The tracker at the configuration `c` (see the file header): like `ownTracker`, what the
tracker value `tv` points at, indexed by `t`, with the configuration as `confchange`
represents it. -/
def ownTrackerC (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) : IProp GF :=
  iprop(
  "Hvotes" ∷ tv.Votes' ↦$ t.votes ∗
  "#Hprs" ∷ tv.Progress' ↦$□ t.prs ∗
  "Hprogs" ∷ ([∗map] _k ↦ pr;p ∈ t.prs;t.peers, ownProgress pr p) ∗
  "Hcfg" ∷ ownCfgCC tv.Config' (DFrac.own 1) c ∗
  "%Hinv" ∷ ⌜CfgInv ⟨c, trkFlags t.peers⟩⌝ ∗
  "%Hdom" ∷ ⌜domSet t.prs = c.ids⌝ ∗
  "%Hflags" ∷ ⌜LearnerFlagsC c t.peers⌝ ∗
  "%Hsize" ∷ ⌜(GMap.size t.prs : Int) ≤ 2 ^ 62⌝ ∗
  "%HmaxInfl" ∷ ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝)

/-- Sealing `ownTrackerC` as one `iapply`; the pure premises in the conjuncts' order. -/
theorem ownTrackerC_intro (c : CfgM) (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (peers : GMap w64 Progress)
    (Hinv : CfgInv ⟨c, trkFlags peers⟩) (Hdom : domSet prs = c.ids)
    (Hflags : LearnerFlagsC c peers) (Hsize : (GMap.size prs : Int) ≤ 2 ^ 62)
    (HmaxInfl : 0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62) :
    ⊢ (tv.Votes' ↦$ votes : IProp GF) -∗
      tv.Progress' ↦$□ prs -∗
      ([∗map] _k ↦ pr;p ∈ prs;peers, ownProgress pr p) -∗
      ownCfgCC tv.Config' (DFrac.own 1) c -∗
      ownTrackerC c tv ⟨votes, prs, peers⟩ := by
  unfold ownTrackerC
  iintro Hvotes #Hprs Hprogs Hcfg
  simp only [named]
  iframe Hvotes Hprs Hprogs Hcfg
  ipureintro
  exact ⟨Hinv, Hdom, Hflags, Hsize, HmaxInfl⟩

/-- `ownTracker` is `ownTrackerC` at its simple configuration. -/
theorem ownTracker_toC (cfg : GSet w64) (tv : tracker.ProgressTracker) (t : Trk) :
    ownTracker (GF := GF) cfg tv t ⊢ ownTrackerC (CfgM.simple cfg (domSet t.prs \ cfg)) tv t := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  obtain ⟨Hldom, Hlnx, Hfl⟩ := Hno_learners
  subst Hlnx
  have Hv : voters = cfg := by rw [← Hvoters_dom, domSet_gset]
  subst Hv
  have Hlrn : learners = domSet t.prs \ voters := by rw [← Hldom, domSet_gset]
  subst Hlrn
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  have Hd : ∀ k, (t.prs !! k).isSome ↔ (t.peers !! k).isSome := Hdom0
  iapply ownTrackerC_intro (CfgM.simple voters (domSet t.prs \ voters)) tv t.votes t.prs t.peers
    (cfgInv_simple voters t.prs t.peers Hprs_dom Hd Hfl) (ids_simple voters t.prs Hprs_dom)
    (learnerFlagsC_simple voters t.prs t.peers Hd Hfl) Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs [Hvoters Hlearners HlearnersNext]
  iapply ownCfgCC_intro tv.Config' (DFrac.own 1) (CfgM.simple voters (domSet t.prs \ voters))
    voters_ref map.nil Hvoters_arr Hautoleave $$ [Hvoters] [] [Hlearners] [HlearnersNext]
  · simp only [CfgM.simple]; iexact Hvoters
  · simp only [CfgM.simple]; iapply ownIdsetC_nil
  · simp only [CfgM.simple]; iexact Hlearners
  · simp only [CfgM.simple]; iexact HlearnersNext

/-- Back: at a non-joint configuration, `ownTrackerC` is `ownTracker` at the incoming voters,
the learners the tracked ids outside them. -/
theorem ownTrackerC_toSimple (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk)
    (ho : c.outgoing = ∅) :
    ownTrackerC (GF := GF) c tv t ⊢
      ownTracker c.incoming tv t ∗ ⌜c.learners = domSet t.prs \ c.incoming⌝ := by
  iintro Hown
  iunfold ownTrackerC at Hown
  iNamed Hown
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  have Hd : ∀ k, (t.prs !! k).isSome ↔ (t.peers !! k).isSome := Hdom0
  obtain ⟨Hfl, Hl⟩ := learnerFlags_of_C c t.prs t.peers Hd Hinv Hdom Hflags ho
  have Hln : c.learnersNext = ∅ := (Hinv.2.2.2 ho).1
  have Hal : c.autoLeave = false := (Hinv.2.2.2 ho).2
  icases ownCfgCC_elim _ _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hin, Hout, Hl', Hln', %Hal'⟩
  ihave %Hvout := ownIdsetC_nil_of _ _ _ ho $$ Hout
  subst Hvout
  isplitl
  · have Hsub : c.incoming ⊆ domSet t.prs := by
      rw [Hdom]; unfold CfgM.ids CfgM.voters
      rw [GMap.elem_of_subseteq]; intro k hk
      exact GMap.elem_of_union_l _ (GMap.elem_of_union_l _ hk)
    iapply ownTracker_intro c.incoming tv t.votes t.prs t.peers vin c.incoming c.learners
      c.learnersNext Hsub Harr (Hal'.trans Hal) (domSet_gset _)
      ⟨by rw [domSet_gset]; exact Hl, Hln, Hfl⟩ Hsize HmaxInfl
      $$ Hvotes Hprs Hprogs Hin Hl' Hln'
  · ipureintro; exact Hl

/-- `ownTrackerC_toSimple` at `CfgM.simple`. -/
theorem ownTrackerC_toTracker (cfg lrn : GSet w64) (tv : tracker.ProgressTracker) (t : Trk) :
    ownTrackerC (GF := GF) (CfgM.simple cfg lrn) tv t ⊢
      ownTracker cfg tv t ∗ ⌜lrn = domSet t.prs \ cfg⌝ :=
  ownTrackerC_toSimple (CfgM.simple cfg lrn) tv t rfl

/-! ### Readers -/

theorem ownTrackerC_pure (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ownTrackerC (GF := GF) c tv t ⊢
      ⌜CfgInv ⟨c, trkFlags t.peers⟩ ∧ domSet t.prs = c.ids ∧ LearnerFlagsC c t.peers ∧
        (GMap.size t.prs : Int) ≤ 2 ^ 62 ∧
        (0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62)⌝ ∗
      ownTrackerC c tv t := by
  iintro Hown
  iunfold ownTrackerC at Hown
  iNamed Hown
  isplitr
  · ipureintro
    exact ⟨Hinv, Hdom, Hflags, Hsize, HmaxInfl⟩
  iapply ownTrackerC_intro c tv t.votes t.prs t.peers Hinv Hdom Hflags Hsize HmaxInfl
    $$ Hvotes Hprs Hprogs Hcfg

/-- The voters of either half number at most `2^62` (they are tracked). -/
theorem ownTrackerC_voters_size (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ownTrackerC (GF := GF) c tv t ⊢
      ⌜(GMap.size c.voters : Int) ≤ 2 ^ 62 ∧ (GMap.size c.incoming : Int) ≤ 2 ^ 62 ∧
        (GMap.size c.outgoing : Int) ≤ 2 ^ 62⌝ ∗ ownTrackerC c tv t := by
  iintro Hown
  icases ownTrackerC_pure _ _ _ $$ Hown with ⟨%H, Hown⟩
  obtain ⟨-, Hdom, -, Hsize, -⟩ := H
  iframe Hown
  ipureintro
  have h1 := size_le_of_sub_dom c.voters t.prs (by rw [Hdom]; exact voters_sub_ids c)
  have h2 := size_le_of_sub_dom c.incoming t.prs (by rw [Hdom]; exact incoming_sub_ids c)
  have h3 := size_le_of_sub_dom c.outgoing t.prs (by rw [Hdom]; exact outgoing_sub_ids c)
  omega

/-- The progress map (persistent) and its domain, read out without consuming anything. -/
theorem ownTrackerC_progress_map (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ownTrackerC (GF := GF) c tv t ⊢
      tv.Progress' ↦$□ t.prs ∗ ⌜domSet t.prs = c.ids⌝ ∗ ownTrackerC c tv t := by
  iintro Hown
  iunfold ownTrackerC at Hown
  iNamed Hown
  iframe Hprs
  isplitr
  · ipureintro; exact Hdom
  iapply ownTrackerC_intro c tv t.votes t.prs t.peers Hinv Hdom Hflags Hsize HmaxInfl
    $$ Hvotes Hprs Hprogs Hcfg

/-- An id set read whole, as `MajorityConfig`'s specs take a half of a `JointConfig`: `nil`
and empty, or a map with that key set. -/
theorem ownIdsetQ_toMaj (m : Loc) (s : GSet w64) :
    ownIdsetQ (GF := GF) m (DFrac.own 1) s ⊢
      (⌜m = map.nil ∧ s = ∅⌝ ∨ ∃ ids : GMap w64 Unit, ⌜domSet ids = s⌝ ∗ m ↦$ ids) := by
  unfold ownIdsetQ
  iintro (%H | Hm)
  · ileft; ipureintro; exact H
  · iright; iexists s; iframe Hm; ipureintro; exact domSet_gset s

theorem ownIdsetQ_ofMaj (m : Loc) (s : GSet w64) :
    (⌜m = map.nil ∧ s = ∅⌝ ∨ ∃ ids : GMap w64 Unit, ⌜domSet ids = s⌝ ∗ m ↦$ ids) ⊢
      ownIdsetQ (GF := GF) m (DFrac.own 1) s := by
  unfold ownIdsetQ
  iintro (%H | ⟨%ids, %Hd, Hm⟩)
  · ileft; ipureintro; exact H
  · rw [domSet_gset] at Hd
    subst Hd
    iright; iexact Hm

/-- The two voter halves of a configuration value, as `JointConfig`'s specs take them
(`ownIdsetQ`), with the rest of the configuration kept in the wand that puts them back. -/
theorem ownCfgCC_voters (cfg : tracker.Config) (c : CfgM) :
    ownCfgCC (GF := GF) cfg (DFrac.own 1) c ⊢ ∃ (vin vout : Loc),
      ⌜cfg.Voters'.arr = [vin, vout]⌝ ∗ ownIdsetQ vin (DFrac.own 1) c.incoming ∗
      ownIdsetQ vout (DFrac.own 1) c.outgoing ∗
      (ownIdsetQ vin (DFrac.own 1) c.incoming -∗ ownIdsetQ vout (DFrac.own 1) c.outgoing -∗
        ownCfgCC cfg (DFrac.own 1) c) := by
  iintro Hc
  icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
  ihave %Hnn := ownMap_not_nil _ _ _ $$ Hin
  icases ownIdsetC_split _ _ _ $$ Hout with ⟨Hout, %Hcan⟩
  iexists vin, vout
  isplitr
  · ipureintro; exact Harr
  ihave Hin := ownIdsetQ_map _ _ _ $$ Hin
  iframe Hin Hout
  iintro Hin Hout
  ihave Hin := ownIdsetQ_not_nil _ _ _ Hnn $$ Hin
  ihave Hout := ownIdsetC_join _ _ _ Hcan $$ Hout
  iapply ownCfgCC_intro cfg (DFrac.own 1) c vin vout Harr Hal $$ Hin Hout Hl Hln

/-- One peer's `Progress`, borrowed out of `ownTrackerC` by its key, given back at any record
with the same `IsLearner` (as `ownTracker_lookup`). -/
theorem ownTrackerC_lookup (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) (i : w64)
    (pr : Loc) (Hpr : t.prs !! i = some pr) :
    ⊢ ownTrackerC (GF := GF) c tv t -∗
      ∃ p, ⌜t.peers !! i = some p⌝ ∗ ownProgress pr p ∗
        (∀ p', ownProgress pr p' -∗ ⌜p'.learner = p.learner⌝ -∗
               ownTrackerC c tv ⟨t.votes, t.prs, <[i := p']> t.peers⟩) := by
  iintro Hown
  iunfold ownTrackerC at Hown
  iNamed Hown
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  obtain ⟨p, Hv⟩ := Option.isSome_iff_exists.1
    ((Hiff i).1 (by show (t.prs !! i).isSome = true; rw [Hpr]; rfl))
  icases BigSepM2.bigSepM2_insert_acc (Φ := fun _ pr p => ownProgress (GF := GF) pr p)
    (m1 := t.prs) (m2 := t.peers) Hpr Hv $$ Hprogs with ⟨Hp, Hback⟩
  iexists p
  isplitr
  · ipureintro; exact Hv
  iframe Hp
  iintro %p' Hp %Hl
  ihave Hprogs := Hback $$ %pr %p' Hp
  have Hins : (Iris.Std.PartialMap.insert t.prs i pr : GMap w64 Loc) = t.prs :=
    GMap.insert_id t.prs i pr Hpr
  rw [Hins]
  iapply ownTrackerC_intro c tv t.votes t.prs _
    (by rw [trkFlags_insert_same _ _ _ _ Hv Hl]; exact Hinv) Hdom (Hflags.insert Hv Hl) Hsize
    HmaxInfl $$ Hvotes Hprs Hprogs Hcfg

/-- The `Progress` records are indexed by the same peers as the map (`ownTracker_prvals_dom`). -/
theorem ownTrackerC_prvals_dom (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTrackerC (GF := GF) c tv t -∗
      ⌜domSet t.peers = domSet t.prs⌝ ∗ ownTrackerC c tv t := by
  iintro Hown
  iunfold ownTrackerC at Hown
  iNamed Hown
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  isplitr
  · ipureintro
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom, GMap.elem_of_dom, ← Option.isSome_iff_exists,
      ← Option.isSome_iff_exists]
    exact (Hiff k).symm
  iapply ownTrackerC_intro c tv t.votes t.prs t.peers Hinv Hdom Hflags Hsize HmaxInfl
    $$ Hvotes Hprs Hprogs Hcfg

/-- The inflight bound (`ownTracker_maxinflight`). -/
theorem ownTrackerC_maxinflight (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTrackerC (GF := GF) c tv t -∗
      ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝ ∗ ownTrackerC c tv t := by
  iintro Hown
  icases ownTrackerC_pure _ _ _ $$ Hown with ⟨%H, Hown⟩
  iframe Hown
  ipureintro; exact H.2.2.2.2

/-- `ownTrackerC_lookup`, given back at the same record (as `ownTracker_lookup_same`). -/
theorem ownTrackerC_lookup_same (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) (i : w64)
    (pr : Loc) (Hpr : t.prs !! i = some pr) :
    ⊢ ownTrackerC (GF := GF) c tv t -∗
      ∃ p, ⌜t.peers !! i = some p⌝ ∗ ownProgress pr p ∗
        (ownProgress pr p -∗ ownTrackerC c tv t) := by
  iintro Hown
  icases ownTrackerC_lookup c tv t i pr Hpr $$ Hown with ⟨%p, %Hv, Hp, Hback⟩
  iexists p
  isplitr
  · ipureintro; exact Hv
  iframe Hp
  iintro Hp
  ihave Hown := Hback $$ %p Hp %rfl
  rw [GMap.insert_id t.peers i p Hv]
  iexact Hown

/-- `visitClosure` (`InvTracker.lean`) at the configuration `c`: the closure `Visit` calls for
each tracked id, lent the tracker field, the id's `Progress` and the wand back to the whole
tracker, and the caller's invariant `I`. -/
def visitClosureC (c : CfgM) (trk : Loc) (votes : GMap w64 Bool) (prs : GMap w64 Loc)
    (f : GoFunc) (I : GSet w64 → GMap w64 Progress → IProp GF) : IProp GF :=
  iprop(∀ (i : w64) (pr : Loc) (tv : tracker.ProgressTracker)
      (pvs : GMap w64 Progress) (p : Progress) (D : GSet w64),
    {{ ⌜i ∈ domSet prs⌝ ∗ ⌜prs !! i = some pr⌝ ∗ ⌜pvs !! i = some p⌝ ∗
        ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝ ∗
        trk ↦ tv ∗ ownProgress pr p ∗
        (∀ p', ownProgress pr p' -∗ ⌜p'.learner = p.learner⌝ -∗
          ownTrackerC c tv ⟨votes, prs, <[i := p']> pvs⟩) ∗
        I D pvs }}
      (App (App (Val #f) (Val #i)) (Val #pr))
    {{ RET #(); ∃ tv' pvs', trk ↦ tv' ∗ ownTrackerC c tv' ⟨votes, prs, pvs'⟩ ∗
                            I ({[i]} ∪ D) pvs' }})

/-- A closure for the simple configuration is one for `ownTrackerC` at it. -/
theorem visitClosure_toC (cfg : GSet w64) (trk : Loc) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (f : GoFunc) (I : GSet w64 → GMap w64 Progress → IProp GF) :
    □ visitClosure (GF := GF) cfg trk votes prs f I ⊢
      visitClosureC (CfgM.simple cfg (domSet prs \ cfg)) trk votes prs f I := by
  iintro #Hf
  unfold visitClosureC
  iintro %i %pr %tv %pvs %p %D
  imodintro
  iintro %Φ ⟨%Hi, %Hpr, %Hp, %Hmi, Htrk, Hpp, Hback, HI⟩ HΦ
  iunfold visitClosure at Hf
  iapply Hf $$ %i %pr %tv %pvs %p %D [Htrk Hpp Hback HI]
  · iframe Htrk Hpp HI
    isplitr
    · ipureintro; exact Hi
    isplitr
    · ipureintro; exact Hpr
    isplitr
    · ipureintro; exact Hp
    isplitr
    · ipureintro; exact Hmi
    iintro %p' Hpp' %Hl
    ihave Hown := Hback $$ %p' Hpp' %Hl
    icases ownTrackerC_toTracker _ _ _ _ $$ Hown with ⟨Hown, -⟩
    iexact Hown
  inext
  iintro ⟨%tv', %pvs', Htrk, Hown, HI⟩
  iapply HΦ
  iexists tv', pvs'
  iframe Htrk HI
  iapply ownTracker_toC _ _ _ $$ Hown

end defs

end EtcdGrove
end Perennial
