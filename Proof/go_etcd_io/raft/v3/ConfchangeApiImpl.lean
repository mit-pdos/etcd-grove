/-
The implementation of `ConfchangeApi.lean`'s sealed definitions and laws (2026-10-29, stage U11),
over `confchange`'s model (`InvConfchange.lean`, `CCApplyC.lean`) and the node API's memberships
(`InvApiDyn.lean`: `stOf`, `memOf`, `cfgOf`, `memApply`). Internal: clients import
`ConfchangeApi.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApiDyn
public import Proof.go_etcd_io.raft.v3.ConfRule
public import Proof.go_etcd_io.raft.v3.InvConfchange
public import Proof.go_etcd_io.raft.v3.InvRestore
public import Proof.go_etcd_io.raft.v3.InvApiDec
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- Go's `confchange` on a membership: `ccApplyM` of the change as `AsV2` makes it, on the
membership's canonical state, without `ccStepB`'s cut. -/
def memApplyGo (o : ConfChangeIM) (m : Membership) : Option Membership :=
  (ccApplyM (ccV2Of o).1 (ccV2Of o).2 (stOf m)).map fun s => memOf s.cfg

/-- A configuration `checkInvariants` accepts tracks the same ids as its membership (a staged
learner is an outgoing voter). -/
theorem memOf_ids_of_inv {s : CCState} (h : CfgInv s) :
    (memOf s.cfg).ids = s.cfg.ids := by
  apply GMap.set_eq; intro k
  simp only [Membership.ids, memOf, CfgM.ids, CfgM.voters, GMap.elem_of_union]
  constructor
  · rintro (((h1 | h1) | h1) | h1)
    · exact .inl (.inl h1)
    · exact .inl (.inr h1)
    · exact .inr h1
    · exact .inl (.inr (h.2.1 k h1).1)
  · rintro ((h1 | h1) | h1)
    · exact .inl (.inl (.inl h1))
    · exact .inl (.inl (.inr h1))
    · exact .inl (.inr h1)

/-- `memApply` is `memApplyGo` cut at `2^62` ids. -/
theorem memApply_eq_go (o : ConfChangeIM) (m : Membership) :
    memApply o m = (memApplyGo o m).filter (fun m' => decide (GMap.size m'.ids < 2 ^ 62)) := by
  unfold memApply memApplyGo ccStepB
  cases h : ccApplyM (ccV2Of o).1 (ccV2Of o).2 (stOf m) with
  | none => rfl
  | some s =>
    simp only [Option.bind_some, Option.map_some, Option.filter_some]
    rw [memOf_ids_of_inv (ccApplyM_inv _ _ h)]
    by_cases hs : GMap.size s.cfg.ids < 2 ^ 62 <;> simp [hs]

theorem gmap_size_eq_of_dom {V W : Type} (a : GMap w64 V) (b : GMap w64 W)
    (h : ∀ k, (a !! k).isSome ↔ (b !! k).isSome) : GMap.size a = GMap.size b := by
  rw [GMap.size_eq_length a b.domList (GMap.nodup_dom_list b)
    (fun k => by rw [GMap.mem_dom_list, h])]
  exact (GMap.size_eq_dom_list_length b).symm

/-- A reachable state's progress map tracks its membership's ids. -/
theorem size_prs_stOf {m : Membership} (hg : CCGood (stOf m)) :
    GMap.size (stOf m).prs = GMap.size m.ids := by
  apply gmap_size_eq_of_dom
  intro k
  rw [← GMap.mem_iff, ← GMap.mem_iff, hg.1 k]
  simp only [stOf_cfg, cfgOf, CfgM.ids, CfgM.voters, Membership.ids,
    GMap.elem_of_union]
  constructor
  · rintro ((h | h) | h)
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr h))
    · exact .inl (.inr h)
  · rintro (((h | h) | h) | h)
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr h
    · have := hg.2.2.2 k h
      exact .inl (.inr this)

/-- Raft's dispatch, `Simple`'s branch. -/
theorem ccApplyM_simple {o : ConfChangeIM} {t : w32} {l : List ConfChangeSingleM} {al : Bool}
    (s : CCState) (ho : ccV2Of o = (t, l)) (hne : ¬ (t = W32 0 ∧ l = []))
    (hj : enterJointOf t l.length = some (al, false)) :
    ccApplyM (ccV2Of o).1 (ccV2Of o).2 s = simpleM l s := by
  rw [ho]; unfold ccApplyM; simp only [hne, ↓reduceIte, hj]

/-- Raft's dispatch, `EnterJoint`'s branch. -/
theorem ccApplyM_enterJoint {o : ConfChangeIM} {t : w32} {l : List ConfChangeSingleM}
    {al : Bool} (s : CCState) (ho : ccV2Of o = (t, l))
    (hj : enterJointOf t l.length = some (al, true)) :
    ccApplyM (ccV2Of o).1 (ccV2Of o).2 s = enterJointM al l s := by
  have hne : ¬ (t = W32 0 ∧ l = []) := by
    rintro ⟨rfl, rfl⟩
    simp [enterJointOf] at hj
  rw [ho]; unfold ccApplyM; simp only [hne, ↓reduceIte, hj]

/-- Raft's dispatch, `LeaveJoint`'s branch. -/
theorem ccApplyM_leaveJoint {o : ConfChangeIM} (s : CCState) (ho : ccV2Of o = (W32 0, [])) :
    ccApplyM (ccV2Of o).1 (ccV2Of o).2 s = leaveJointM s := by
  rw [ho]; unfold ccApplyM; simp

/-! ### `Restore` of a `ConfState` reporting a membership -/

theorem cc_mem_of_perm {l : List w64} {S : GSet w64} (h : l ≡ₚ GMap.elements S) (k : w64) :
    k ∈ l ↔ k ∈ S := by
  rw [h.mem_iff, GMap.elem_of_elements]

theorem cc_listToSet_of_perm {l : List w64} {S : GSet w64} (h : l ≡ₚ GMap.elements S) :
    GMap.listToSet l = S :=
  GMap.set_eq fun k => by rw [GMap.elem_of_list_to_set, cc_mem_of_perm h]

theorem cc_nil_of_perm_empty {l : List w64} {S : GSet w64} (h : l ≡ₚ GMap.elements S)
    (hS : S = ∅) : l = [] := by
  subst hS
  exact List.eq_nil_iff_forall_not_mem.2 fun k hk => GMap.not_elem_of_empty k ((cc_mem_of_perm h k).1 hk)

theorem cc_mem_ids_iff (m : Membership) (k : w64) :
    k ∈ m.ids ↔ k ∈ m.voters ∨ k ∈ m.votersOutgoing ∨ k ∈ m.learners ∨ k ∈ m.learnersNext := by
  simp only [Membership.ids, GMap.elem_of_union, or_assoc]

/-- A `ConfState` reporting a valid membership that `Restore` rebuilds is well-formed, and
`Restore`'s model answers the membership's canonical state. -/
theorem restore_of_confStateIs (c : ConfStateM) (m : Membership) (hc : confStateIs c m)
    (hv : memValid m) (hr : W64 0 ∉ m.ids ∧ ∀ k, k ∈ m.learnersNext → k ∉ m.voters) :
    CSWf c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' ∧
      restoreM c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' c.AutoLeave' =
        some (stOf m) := by
  obtain ⟨hV, hVO, hL, hLN, hAL⟩ := hc
  obtain ⟨⟨hinv, hin, -⟩, hg⟩ := hv
  have hinvLN : ∀ k, k ∈ m.learnersNext → k ∈ m.votersOutgoing := fun k hk => (hinv.2.1 k hk).1
  have hinvO : m.votersOutgoing = ∅ → m.learnersNext = ∅ ∧ m.autoLeave = false := hinv.2.2.2
  have hgL : ∀ k, k ∈ m.learners → k ∉ m.voters ∧ k ∉ m.votersOutgoing := hg.2.2.1
  have hin' : m.voters ≠ ∅ := hin
  have Hwf : CSWf c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; apply hin'
      rw [← cc_listToSet_of_perm hV, h]; try rfl
    · intro x hx e; subst e; apply hr.1
      rw [cc_mem_ids_iff]
      rcases hx with hx | hx | hx | hx
      · exact .inr (.inl ((cc_mem_of_perm hVO _).1 hx))
      · exact .inl ((cc_mem_of_perm hV _).1 hx)
      · exact .inr (.inr (.inl ((cc_mem_of_perm hL _).1 hx)))
      · exact .inr (.inr (.inr ((cc_mem_of_perm hLN _).1 hx)))
    · intro x hx
      have := hgL x ((cc_mem_of_perm hL _).1 hx)
      exact ⟨fun h => this.1 ((cc_mem_of_perm hV _).1 h), fun h => this.2 ((cc_mem_of_perm hVO _).1 h)⟩
    · intro x hx
      have hx' := (cc_mem_of_perm hLN _).1 hx
      have ho := hinvLN x hx'
      refine ⟨(cc_mem_of_perm hVO _).2 ho, fun h => hr.2 x hx' ((cc_mem_of_perm hV _).1 h), fun h => ?_⟩
      exact (hgL x ((cc_mem_of_perm hL _).1 h)).2 ho
    · intro h
      have hO : m.votersOutgoing = ∅ := by rw [← cc_listToSet_of_perm hVO, h]; try rfl
      exact cc_nil_of_perm_empty hLN (hinvO hO).1
  refine ⟨Hwf, ?_⟩
  rw [restoreM_wf _ _ _ _ _ Hwf]
  congr 1
  unfold stOf
  congr 1
  unfold csCfgM cfgOf
  rw [cc_listToSet_of_perm hV, cc_listToSet_of_perm hVO, cc_listToSet_of_perm hL, cc_listToSet_of_perm hLN]
  congr 1
  by_cases h : c.VotersOutgoing' = []
  · have hO : m.votersOutgoing = ∅ := by rw [← cc_listToSet_of_perm hVO, h]; try rfl
    rw [ite_eq_left h, (hinvO hO).2]
  · rw [ite_eq_right h, hAL]

/-- The empty membership's `ConfState` has empty lists, `AutoLeave` off. -/
theorem confStateIs_empty {c : ConfStateM} (hc : confStateIs c Membership.empty) :
    c.Voters' = [] ∧ c.VotersOutgoing' = [] ∧ c.Learners' = [] ∧ c.LearnersNext' = [] ∧
      c.AutoLeave' = false := by
  obtain ⟨hV, hVO, hL, hLN, hAL⟩ := hc
  exact ⟨cc_nil_of_perm_empty hV rfl, cc_nil_of_perm_empty hVO rfl, cc_nil_of_perm_empty hL rfl,
    cc_nil_of_perm_empty hLN rfl, hAL⟩

theorem stOf_empty : stOf Membership.empty = cfgState ∅ ∅ := stOf_simple ∅

theorem ccGood_stOf_empty : CCGood (stOf Membership.empty) := by
  rw [stOf_empty]; exact ccGood_cfgState ∅

/-! ### What `Restore` needs, kept by every change -/

/-- What `Restore` needs of a state, kept by every `Changer` step: no tracked id `0`; a staged
learner is no incoming voter, and is tracked. -/
def RState (s : CCState) : Prop :=
  (∀ k, k ∈ s.prs → k ≠ W64 0) ∧
    (∀ k, k ∈ s.cfg.learnersNext → k ∉ s.cfg.incoming ∧ k ∈ s.prs)

theorem RState.initProgress {s : CCState} (h : RState s) (id : w64) (lrn : Bool)
    (h0 : id ≠ W64 0) (hn : id ∉ s.prs) : RState (initProgressM id lrn s) := by
  obtain ⟨h1, h2⟩ := h
  have hp : ∀ k, k ∈ (<[id := lrn]> s.prs : GMap w64 Bool) → k ≠ W64 0 := by
    intro k hk
    rcases (gm_mem_insert _ _ _ _).1 hk with rfl | hk
    · exact h0
    · exact h1 k hk
  cases lrn
  · refine ⟨hp, fun k hk => ?_⟩
    simp only [initProgressM, Bool.false_eq_true, ↓reduceIte] at hk ⊢
    obtain ⟨a, b⟩ := h2 k hk
    have hne : k ≠ id := fun e => hn (e ▸ b)
    refine ⟨fun h' => ?_, (gm_mem_insert _ _ _ _).2 (.inr b)⟩
    rcases (gm_mem_insert _ _ _ _).1 h' with e | h'
    · exact hne e
    · exact a h'
  · refine ⟨hp, fun k hk => ?_⟩
    simp only [initProgressM, ↓reduceIte] at hk ⊢
    obtain ⟨a, b⟩ := h2 k hk
    exact ⟨a, (gm_mem_insert _ _ _ _).2 (.inr b)⟩

theorem RState.makeVoter {s : CCState} (h : RState s) (id : w64) (h0 : id ≠ W64 0) :
    RState (makeVoterM id s) := by
  unfold makeVoterM
  split
  · obtain ⟨h1, h2⟩ := h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rcases (gm_mem_insert _ _ _ _).1 hk with rfl | hk
      · exact h0
      · exact h1 k hk
    · simp only at hk ⊢
      obtain ⟨hne, hk⟩ := (gm_mem_delete _ _ _).1 hk
      obtain ⟨a, b⟩ := h2 k hk
      refine ⟨fun h' => ?_, (gm_mem_insert _ _ _ _).2 (.inr b)⟩
      rcases (gm_mem_insert _ _ _ _).1 h' with e | h'
      · exact hne e
      · exact a h'
  · rename_i hn
    exact h.initProgress id false h0 hn

theorem RState.makeLearner {s : CCState} (h : RState s) (id : w64) (h0 : id ≠ W64 0) :
    RState (makeLearnerM id s) := by
  unfold makeLearnerM
  split
  · rename_i hl
    refine h.initProgress id true h0 ?_
    rw [GMap.mem_iff, hl]; simp
  · exact h
  · rename_i hl
    have ht : id ∈ s.prs := by rw [GMap.mem_iff, hl]; rfl
    obtain ⟨h1, h2⟩ := h
    split
    · refine ⟨h1, fun k hk => ?_⟩
      simp only [removeCfg] at hk ⊢
      rcases (gm_mem_insert _ _ _ _).1 hk with rfl | hk
      · exact ⟨fun h' => ((gm_mem_delete _ _ _).1 h').1 rfl, ht⟩
      · obtain ⟨-, hk⟩ := (gm_mem_delete _ _ _).1 hk
        obtain ⟨a, b⟩ := h2 k hk
        exact ⟨fun h' => a ((gm_mem_delete _ _ _).1 h').2, b⟩
    · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rcases (gm_mem_insert _ _ _ _).1 hk with rfl | hk
        · exact h0
        · exact h1 k hk
      · simp only [removeCfg] at hk ⊢
        obtain ⟨-, hk⟩ := (gm_mem_delete _ _ _).1 hk
        obtain ⟨a, b⟩ := h2 k hk
        exact ⟨fun h' => a ((gm_mem_delete _ _ _).1 h').2, (gm_mem_insert _ _ _ _).2 (.inr b)⟩

theorem RState.remove {s : CCState} (h : RState s) (id : w64) : RState (removeM id s) := by
  unfold removeM
  split
  · obtain ⟨h1, h2⟩ := h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · simp only at hk
      split at hk
      · exact h1 k hk
      · exact h1 k ((gm_mem_delete _ _ _).1 hk).2
    · simp only [removeCfg] at hk ⊢
      obtain ⟨hne, hk⟩ := (gm_mem_delete _ _ _).1 hk
      obtain ⟨a, b⟩ := h2 k hk
      refine ⟨fun h' => a ((gm_mem_delete _ _ _).1 h').2, ?_⟩
      split
      · exact b
      · exact (gm_mem_delete _ _ _).2 ⟨hne, b⟩
  · exact h

theorem RState.applyOne {s s' : CCState} (h : RState s) (cc : ConfChangeSingleM)
    (H : applyOne cc s = some s') : RState s' := by
  unfold EtcdGrove.applyOne at H
  split at H
  · cases H; exact h
  rename_i h0
  split at H
  · cases H; exact h.makeVoter _ h0
  split at H
  · cases H; exact h.makeLearner _ h0
  split at H
  · cases H; exact h.remove _
  split at H
  · cases H; exact h
  · cases H

theorem RState.applyAll {s s' : CCState} (h : RState s) (ccs : List ConfChangeSingleM)
    (H : applyAll ccs s = some s') : RState s' := by
  induction ccs generalizing s with
  | nil => cases H; exact h
  | cons cc ccs IH =>
    simp only [EtcdGrove.applyAll] at H
    cases h1 : EtcdGrove.applyOne cc s with
    | none => rw [h1] at H; cases H
    | some s1 =>
      rw [h1] at H
      exact IH (h.applyOne cc h1) H

theorem RState.applyM {s s' : CCState} (h : RState s) (ccs : List ConfChangeSingleM)
    (H : applyM ccs s = some s') : RState s' := by
  unfold EtcdGrove.applyM at H
  cases h1 : EtcdGrove.applyAll ccs s with
  | none => rw [h1] at H; cases H
  | some s1 =>
    rw [h1] at H
    simp only [Option.bind] at H
    split at H
    · cases H
    · cases H; exact h.applyAll ccs h1

theorem RState.ccApply {s s' : CCState} (h : RState s) (t : raftpb.ConfChangeTransition)
    (ccs : List ConfChangeSingleM) (H : ccApplyM t ccs s = some s') : RState s' := by
  unfold ccApplyM at H
  split at H
  · -- `LeaveJoint`: no staged learner, fewer tracked ids
    unfold leaveJointM at H
    split at H; · cases H
    split at H; · cases H
    obtain ⟨rfl, -⟩ := checkedM_some H
    refine ⟨fun k hk => ?_, fun k hk => absurd hk (GMap.not_elem_of_empty _)⟩
    simp only [leaveJointState] at hk
    rw [GMap.mem_iff, GMap.lookup_filter] at hk
    apply h.1 k
    rw [GMap.mem_iff]
    cases hp : s.prs !! k with
    | some _ => rfl
    | none =>
      exfalso
      have hu : (GMap.fmap (fun _ => true)
          (GMap.filter (fun k _ => decide (k ∈ s.cfg.learnersNext)) s.prs) ∪ s.prs) !! k =
          none := by
        rw [GMap.lookup_union, GMap.lookup_fmap, GMap.lookup_filter, hp]; rfl
      rw [hu] at hk
      simp at hk
  split at H
  · -- `EnterJoint`
    unfold enterJointM at H
    split at H; · cases H
    split at H; · cases H
    split at H; · cases H
    split at H
    · cases H
    · rename_i s1 h1
      obtain ⟨rfl, -⟩ := checkedM_some H
      have h' : RState { cfg := { s.cfg with outgoing := s.cfg.incoming, autoLeave := false }, prs := s.prs } := h
      have h2 := h'.applyM _ h1
      exact h2
  · -- `Simple`
    unfold simpleM at H
    split at H; · cases H
    split at H; · cases H
    split at H
    · cases H
    · rename_i s1 h1
      split at H
      · cases H
      · obtain ⟨rfl, -⟩ := checkedM_some H
        have h' : RState (clearAutoLeave s) := h
        exact h'.applyM _ h1
  · cases H

/-- A restorable membership's state, at a reachable `stOf m`. -/
theorem rstate_of_restorable {m : Membership} (hg : CCGood (stOf m))
    (hr : W64 0 ∉ m.ids ∧ ∀ k, k ∈ m.learnersNext → k ∉ m.voters) : RState (stOf m) := by
  have hmem : ∀ k, k ∈ (stOf m).prs → k ∈ m.ids := by
    intro k hk
    rw [hg.1 k, mem_ids] at hk
    rw [cc_mem_ids_iff]
    rcases hk with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  refine ⟨fun k hk e => hr.1 (e ▸ hmem k hk), fun k hk => ⟨hr.2 k hk, ?_⟩⟩
  rw [hg.1 k, mem_ids]
  exact .inr (.inl (hg.2.2.2 k hk))

/-- A change keeps a membership restorable. -/
theorem memApplyGo_restorable {o : ConfChangeIM} {m m' : Membership} (hg : CCGood (stOf m))
    (hr : W64 0 ∉ m.ids ∧ ∀ k, k ∈ m.learnersNext → k ∉ m.voters)
    (h : memApplyGo o m = some m') :
    W64 0 ∉ m'.ids ∧ ∀ k, k ∈ m'.learnersNext → k ∉ m'.voters := by
  unfold memApplyGo at h
  cases hs : ccApplyM (ccV2Of o).1 (ccV2Of o).2 (stOf m) with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hR := (rstate_of_restorable hg hr).ccApply _ _ hs
    have hinv := ccApplyM_inv _ _ hs
    refine ⟨fun h0 => ?_, fun k hk => (hR.2 k hk).1⟩
    rw [memOf_ids_of_inv hinv, mem_ids] at h0
    have hk : W64 0 ∈ s.cfg.incoming ∨ W64 0 ∈ s.cfg.outgoing ∨ W64 0 ∈ s.cfg.learners ∨
        W64 0 ∈ s.cfg.learnersNext := by
      rcases h0 with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
    exact hR.1 _ (hinv.1 _ hk) rfl

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The body of a `(Config, ProgressMap)` pair at `m`: the configuration (`ownCfgCC` at `m`'s),
the progress map (read at some fraction) and its `Progress` objects, whose learner flags are the
canonical ones of `m` (`stOf`), a reachable state (`CCGood`). -/
def cfgPairBody (cfg : tracker.Config) (prs : Loc) (m : Membership) : IProp GF :=
  iprop(∃ (pm : GMap w64 Loc) (pvs : GMap w64 tracker.Progress) (dq : DFrac),
    ⌜CCGood (stOf m) ∧ flagsOf pvs = (stOf m).prs⌝ ∗
    ownCfgCC cfg (DFrac.own 1) (cfgOf m) ∗ prs ↦${dq} pm ∗
    ([∗map] _k ↦ pr;pv ∈ pm;pvs, pr ↦ pv))

/-- The size of a pair's progress map, borrowed. -/
theorem cfgPairBody_size (cfg : tracker.Config) (prs : Loc) (m : Membership) :
    cfgPairBody (GF := GF) cfg prs m ⊢ ∃ (M : GMap w64 Loc) (dq : DFrac),
      prs ↦${dq} M ∗ ⌜GMap.size M = GMap.size m.ids⌝ ∗
      (prs ↦${dq} M -∗ cfgPairBody cfg prs m) := by
  unfold cfgPairBody
  iintro ⟨%pm, %pvs, %dq, %Hp, Hc, Hm, Hprs⟩
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  iexists pm, dq
  iframe Hm
  isplitr
  · ipureintro
    rw [← size_prs_stOf Hp.1, ← Hp.2, flagsOf, GMap.map_size_fmap]
    exact gmap_size_eq_of_dom pm pvs Hiff
  · iintro Hm
    iexists pm, pvs, dq
    iframe Hc Hm Hprs
    ipureintro; exact Hp

/-- The tracker a `Changer` reads, from a pair in its fields. -/
theorem cfgPairBody_tracker (tv : tracker.ProgressTracker) (m : Membership) :
    cfgPairBody (GF := GF) tv.Config' tv.Progress' m ⊢ ∃ (pm : GMap w64 Loc)
      (pvs : GMap w64 tracker.Progress) (dq : DFrac),
      ⌜CCGood (stOf m) ∧ ({ cfg := cfgOf m, prs := flagsOf pvs } : CCState) = stOf m⌝ ∗
      ownTrackerCC tv (DFrac.own 1) dq (DFrac.own 1) (cfgOf m) pm pvs ∗
      (ownTrackerCC tv (DFrac.own 1) dq (DFrac.own 1) (cfgOf m) pm pvs -∗
        cfgPairBody tv.Config' tv.Progress' m) := by
  unfold cfgPairBody
  iintro ⟨%pm, %pvs, %dq, %Hp, Hc, Hm, Hprs⟩
  iexists pm, pvs, dq
  isplitr
  · ipureintro
    refine ⟨Hp.1, ?_⟩
    rw [Hp.2]; rfl
  isplitl [Hc Hm Hprs]
  · unfold ownTrackerCC
    iframe
  · iintro Ht
    unfold ownTrackerCC
    icases Ht with ⟨Hc, Hm, Hprs⟩
    iexists pm, pvs, dq
    iframe
    ipureintro; exact Hp

/-- What a `Changer` method returns for `ccApplyM`'s answer at a reachable `stOf m`, as a pair
at `memApplyGo`'s answer. -/
theorem ownResult_pair (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (o : ConfChangeIM) (m : Membership) (r : Option CCState) (cfg : tracker.Config) (trk : Loc)
    (err : GoInterface) (hg : CCGood (stOf m))
    (hr : ccApplyM (ccV2Of o).1 (ccV2Of o).2 (stOf m) = r) :
    ownResult (GF := GF) chg base r cfg trk err ⊢
      (∃ m', ⌜err = interface.nil ∧ memApplyGo o m = some m'⌝ ∗ cfgPairBody cfg trk m') ∨
        ⌜err ≠ interface.nil ∧ memApplyGo o m = none⌝ := by
  cases r with
  | none =>
    unfold ownResult
    iintro %He
    iright; ipureintro
    refine ⟨He, ?_⟩
    unfold memApplyGo; rw [hr]; rfl
  | some s =>
    unfold ownResult ownPrsW
    iintro ⟨%He, Hc, Hw⟩
    iNamed Hw
    have hg' : CCGood s := ccApplyM_good hg _ _ hr
    have hs : stOf (memOf s.cfg) = s := stOf_memOf hg'
    ileft
    iexists memOf s.cfg
    isplitr
    · ipureintro
      refine ⟨He, ?_⟩
      unfold memApplyGo; rw [hr]; rfl
    unfold cfgPairBody
    iexists prs, pvs, DFrac.own 1
    rw [cfgOf_memOf, hs]
    iframe Hc Htrk Hprs
    ipureintro
    exact ⟨hg', Hflags⟩

/-- The empty membership's pair: the fresh tracker's own maps. -/
theorem cfgPairBody_empty (cfg : tracker.Config) (prs v0 : Loc)
    (Harr : cfg.Voters'.arr = [v0, map.nil]) (Hl : cfg.Learners' = map.nil)
    (Hln : cfg.LearnersNext' = map.nil) (Hal : cfg.AutoLeave' = false) :
    ⊢ (v0 ↦$ (∅ : GMap w64 Unit) : IProp GF) -∗ prs ↦$□ (∅ : GMap w64 Loc) -∗
      cfgPairBody cfg prs Membership.empty := by
  iintro Hv0 Hprs
  unfold cfgPairBody
  iexists ∅, ∅, DFrac.discard
  isplitr
  · ipureintro
    refine ⟨ccGood_stOf_empty, ?_⟩
    rw [stOf_empty]
    apply GMap.map_eq; intro k
    show (flagsOf ∅) !! k = cfgFlags ∅ ∅ !! k
    rw [flagsOf_lookup', cfgFlags_lookup]
    simp [GMap.not_elem_of_empty]
  isplitl [Hv0]
  · have e : cfgOf Membership.empty = ⟨∅, ∅, ∅, ∅, false⟩ := rfl
    rw [e]
    unfold ownCfgCC
    iexists v0, map.nil
    simp only [named]
    rw [Hl, Hln]
    iframe Hv0
    isplitr
    · ipureintro; exact Harr
    isplitr
    · iapply ownIdsetC_nil
    isplitr
    · iapply ownIdsetC_nil
    isplitr
    · iapply ownIdsetC_nil
    · ipureintro; exact Hal
  isplitl [Hprs]
  · iexact Hprs
  · iapply (BigSepM2.bigSepM2_empty _).2; iempintro

/-- What `Restore` builds for a `ConfState` reporting `m` (its second arm), as a pair at `m`. -/
theorem cfgPairBody_of_restore (m : Membership) (cfg : tracker.Config) (prsm : Loc)
    (prs : GMap w64 Loc) (hg : CCGood (stOf m)) (Hdom : domSet prs = domSet (stOf m).prs) :
    ⊢ ownCfgCC (GF := GF) cfg (DFrac.own 1) (stOf m).cfg -∗ prsm ↦$ prs -∗
      ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗ ⌜(stOf m).prs !! k = some p.learner⌝) -∗
      cfgPairBody cfg prsm m := by
  rw [stOf_cfg]
  iintro Hc Hprsm Hprogs
  ihave Hprogs : ([∗map] k ↦ pr ∈ prs, ∃ pv : tracker.Progress, (pr ↦ pv : IProp GF) ∗
      ⌜(stOf m).prs !! k = some pv.IsLearner'⌝) $$ [Hprogs]
  · iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
    intro k pr _
    iintro ⟨%p, Hp, %Hpk⟩
    unfold ownProgress
    iNamed Hp
    iexists pv
    iframe Hpv
    ipureintro
    rw [Hpk, ((progressAbs_Some _ _ _).1 Habs).1]
  icases bigSepM_exist_sepM2 prs
    (fun k pr (pv : tracker.Progress) => iprop((pr ↦ pv : IProp GF) ∗
      ⌜(stOf m).prs !! k = some pv.IsLearner'⌝))
    $$ Hprogs with ⟨%pvs, Hprogs⟩
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ Hprogs with ⟨Hprogs, Hfl⟩
  ihave %Hfl := BigSepM2.bigSepM2_pure_intro $$ Hfl
  have Htf : flagsOf pvs = (stOf m).prs := by
    apply GMap.map_eq; intro k
    rw [flagsOf_lookup']
    cases hp : pvs !! k with
    | some pv =>
      obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1
        ((Hiff k).2 (by show (pvs !! k).isSome = true; rw [hp]; rfl))
      exact (Hfl k pr pv hpr hp).symm
    | none =>
      cases hc : (stOf m).prs !! k with
      | none => rfl
      | some b =>
        exfalso
        have hk : k ∈ domSet prs := by
          rw [Hdom, GMap.elem_of_dom', GMap.mem_iff, hc]; rfl
        rw [GMap.elem_of_dom', GMap.mem_iff] at hk
        have h2 : (pvs !! k).isSome = true := (Hiff k).1 hk
        rw [hp] at h2
        simp at h2
  unfold cfgPairBody
  iexists prs, pvs, DFrac.own 1
  iframe Hc Hprsm Hprogs
  ipureintro; exact ⟨hg, Htf⟩

end defs

/-! ### Every configuration of a cluster of client decisions is restorable -/

section confat

theorem decFoldFrom_restorable [GooseExts] (M : DecMap) (k : Nat) (m m' : Membership)
    (l : List LogEntry) (hm : m.Valid)
    (hr : W64 0 ∉ m.ids ∧ ∀ k, k ∈ m.learnersNext → k ∉ m.voters)
    (h : decFoldFrom M k m l = some m') :
    W64 0 ∉ m'.ids ∧ ∀ k, k ∈ m'.learnersNext → k ∉ m'.voters := by
  induction l generalizing k m with
  | nil => simp only [decFoldFrom, Option.some.injEq] at h; subst h; exact hr
  | cons e l ih =>
    simp only [decFoldFrom] at h
    cases hs : decStep M k m e with
    | none => rw [hs] at h; cases h
    | some m1 =>
      rw [hs, Option.bind_some] at h
      have hv1 : m1.Valid := by
        unfold decStep at hs
        split at hs
        · split at hs
          · cases hs
          · cases hs; exact hm
          · exact memApply_valid _ m m1 hm hs
        · cases hs; exact hm
      apply ih (k + 1) m1 hv1 _ h
      unfold decStep at hs
      split at hs
      · split at hs
        · cases hs
        · cases hs; exact hr
        · rename_i o _
          have hs' : memApply o m = some m1 := hs
          rw [memApply_eq_go] at hs'
          cases hg : memApplyGo o m with
          | none => rw [hg] at hs'; cases hs'
          | some m2 =>
            rw [hg, Option.filter_some] at hs'
            split at hs'
            · cases hs'; exact memApplyGo_restorable hm.2 hr hg
            · cases hs'
      · cases hs; exact hr

variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem confAtU_restorable (γ : Cluster) (k : Nat) (m : Membership) :
    confAtU (GF := GF) γ k m ⊢ ⌜W64 0 ∉ m.ids ∧ ∀ k, k ∈ m.learnersNext → k ∉ m.voters⌝ := by
  unfold confAtU
  iintro ⟨%l, %M, -, -, %P⟩
  ipureintro
  obtain ⟨-, c0, g, hm, hf⟩ := P
  exact decFoldFrom_restorable M 0 c0 m _ hm.valid hm.2.2 hf

end confat

end ApiImpl
end EtcdGrove
end Perennial
