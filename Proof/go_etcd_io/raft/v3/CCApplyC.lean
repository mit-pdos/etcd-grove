/-
Applying a configuration change at any configuration, the model (raft v3.7 retarget, stage
R1): the pure part of `InvApplyConfC.lean` of the old proof (its `section model`, verbatim but
for R1's type rename), split off as `CCApply.lean` is from `InvApplyConf.lean`; the heap section
(`ownTrackerC_toCC`, `ownResult_transfer`) is ported with the raft layer.

From `InvApplyConfC.lean` (2026-10-13, reconfiguration stage A2): `CCGood`, what every
`confchange` state the node can reach satisfies -- the progress map tracks exactly the
configuration's ids (`CfgM.ids`), each tracked `IsLearner` is whether the id is a learner, a
learner is no voter, a staged learner is an outgoing voter and no incoming one. Every
`Changer` operation keeps it (`ccApplyM_good`).
-/
module

public import Proof.go_etcd_io.raft.v3.CCApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The reachable states -/

section model
variable [FfiSyntax]

theorem gm_mem_insert {V : Type} (m : GMap w64 V) (i k : w64) (v : V) :
    k ∈ (<[i := v]> m : GMap w64 V) ↔ k = i ∨ k ∈ m := by
  rw [GMap.mem_iff, GMap.mem_iff]
  by_cases h : i = k
  · subst h; simp [GMap.lookup_insert]
  · rw [GMap.lookup_insert_ne _ _ h]
    exact ⟨fun h' => .inr h', fun h' => h'.elim (fun e => absurd e.symm h) id⟩

theorem gm_mem_delete {V : Type} (m : GMap w64 V) (i k : w64) :
    k ∈ (GMap.delete i m : GMap w64 V) ↔ k ≠ i ∧ k ∈ m := by
  rw [GMap.mem_iff, GMap.mem_iff]
  by_cases h : i = k
  · subst h; simp [GMap.lookup_delete]
  · rw [GMap.lookup_delete_ne _ h]
    exact ⟨fun h' => ⟨fun e => h e.symm, h'⟩, fun h' => h'.2⟩

theorem gm_lookup_insert {V : Type} (m : GMap w64 V) (i k : w64) (v : V) :
    (<[i := v]> m : GMap w64 V) !! k = if k = i then some v else m !! k := by
  by_cases h : k = i
  · subst h; simp [GMap.lookup_insert]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]; simp [h]

theorem gm_lookup_delete {V : Type} (m : GMap w64 V) (i k : w64) :
    (GMap.delete i m : GMap w64 V) !! k = if k = i then none else m !! k := by
  by_cases h : k = i
  · subst h; simp [GMap.lookup_delete]
  · rw [GMap.lookup_delete_ne _ (Ne.symm h)]; simp [h]

theorem mem_ids (c : CfgM) (k : w64) :
    k ∈ c.ids ↔ k ∈ c.incoming ∨ k ∈ c.outgoing ∨ k ∈ c.learners := by
  unfold CfgM.ids CfgM.voters
  rw [GMap.elem_of_union, GMap.elem_of_union, or_assoc]

/-- What every reachable `confchange` state satisfies (see the file header). -/
def CCGood (s : CCState) : Prop :=
  (∀ k, k ∈ s.prs ↔ k ∈ s.cfg.ids) ∧
  (∀ k b, s.prs !! k = some b → b = decide (k ∈ s.cfg.learners)) ∧
  (∀ k, k ∈ s.cfg.learners → k ∉ s.cfg.incoming ∧ k ∉ s.cfg.outgoing) ∧
  (∀ k, k ∈ s.cfg.learnersNext → k ∈ s.cfg.outgoing)

theorem CCGood.clearAutoLeave {s : CCState} (h : CCGood s) : CCGood (clearAutoLeave s) := h

theorem CCGood.initProgress {s : CCState} (h : CCGood s) (id : w64) (lrn : Bool)
    (hn : id ∉ s.prs) : CCGood (initProgressM id lrn s) := by
  obtain ⟨hd, hf, hl, hn2⟩ := h
  have hni : id ∉ s.cfg.ids := fun h' => hn ((hd id).2 h')
  rw [mem_ids] at hni
  simp only [not_or] at hni
  obtain ⟨hi1, hi2, hi3⟩ := hni
  cases lrn
  · refine ⟨fun k => ?_, fun k b hb => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · simp only [initProgressM, Bool.false_eq_true, ↓reduceIte]
      rw [gm_mem_insert, mem_ids, gm_mem_insert, hd, mem_ids]
      by_cases e : k = id <;> simp [e]
    · simp only [initProgressM, Bool.false_eq_true, ↓reduceIte] at hb ⊢
      rw [gm_lookup_insert] at hb
      split at hb
      · subst_vars; cases hb; simp [hi3]
      · exact hf k b hb
    · simp only [initProgressM, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      obtain ⟨a1, a2⟩ := hl k hk
      refine ⟨?_, a2⟩
      rw [gm_mem_insert]
      rintro (rfl | h')
      · exact hi3 hk
      · exact a1 h'
    · simp only [initProgressM, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      exact hn2 k hk
  · refine ⟨fun k => ?_, fun k b hb => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · simp only [initProgressM, ↓reduceIte]
      rw [gm_mem_insert, mem_ids, gm_mem_insert, hd, mem_ids]
      by_cases e : k = id <;> simp [e]
    · simp only [initProgressM, ↓reduceIte] at hb ⊢
      rw [gm_lookup_insert] at hb
      split at hb
      · subst_vars; cases hb; simp [gm_mem_insert]
      · rename_i hk
        rw [hf k b hb]
        simp [gm_mem_insert, hk]
    · simp only [initProgressM, ↓reduceIte] at hk ⊢
      rw [gm_mem_insert] at hk
      rcases hk with rfl | hk
      · exact ⟨hi1, hi2⟩
      · exact hl k hk
    · simp only [initProgressM, ↓reduceIte] at hk ⊢
      exact hn2 k hk

theorem CCGood.makeVoter {s : CCState} (h : CCGood s) (id : w64) :
    CCGood (makeVoterM id s) := by
  unfold makeVoterM
  split
  · rename_i ht
    obtain ⟨hd, hf, hl, hn2⟩ := h
    refine ⟨fun k => ?_, fun k b hb => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · simp only
      rw [gm_mem_insert, mem_ids, gm_mem_insert, gm_mem_delete, hd, mem_ids]
      constructor
      · rintro (rfl | h')
        · exact .inl (.inl rfl)
        · rcases h' with h' | h' | h'
          · exact .inl (.inr h')
          · exact .inr (.inl h')
          · by_cases e : k = id
            · exact .inl (.inl e)
            · exact .inr (.inr ⟨e, h'⟩)
      · rintro ((rfl | h') | h' | ⟨-, h'⟩)
        · exact .inl rfl
        · exact .inr (.inl h')
        · exact .inr (.inr (.inl h'))
        · exact .inr (.inr (.inr h'))
    · simp only at hb ⊢
      rw [gm_lookup_insert] at hb
      split at hb
      · subst_vars; cases hb; simp [gm_mem_delete]
      · rename_i hk
        rw [hf k b hb]
        simp [gm_mem_delete, hk]
    · simp only at hk ⊢
      rw [gm_mem_delete] at hk
      obtain ⟨hk1, hk2⟩ := hk
      obtain ⟨a1, a2⟩ := hl k hk2
      refine ⟨?_, a2⟩
      rw [gm_mem_insert]
      rintro (e | h')
      · exact hk1 e
      · exact a1 h'
    · simp only at hk ⊢
      rw [gm_mem_delete] at hk
      obtain ⟨hk1, hk2⟩ := hk
      exact hn2 k hk2
  · rename_i hn
    exact h.initProgress id false hn

/-- `removeCfg`'s effect on the sets. -/
theorem removeCfg_incoming (id : w64) (c : CfgM) (k : w64) :
    k ∈ (removeCfg id c).incoming ↔ k ≠ id ∧ k ∈ c.incoming := gm_mem_delete _ _ _
theorem removeCfg_learners (id : w64) (c : CfgM) (k : w64) :
    k ∈ (removeCfg id c).learners ↔ k ≠ id ∧ k ∈ c.learners := gm_mem_delete _ _ _
theorem removeCfg_learnersNext (id : w64) (c : CfgM) (k : w64) :
    k ∈ (removeCfg id c).learnersNext ↔ k ≠ id ∧ k ∈ c.learnersNext := gm_mem_delete _ _ _
theorem removeCfg_outgoing (id : w64) (c : CfgM) : (removeCfg id c).outgoing = c.outgoing := rfl

theorem CCGood.remove {s : CCState} (h : CCGood s) (id : w64) : CCGood (removeM id s) := by
  unfold removeM
  split
  · rename_i ht
    obtain ⟨hd, hf, hl, hn2⟩ := h
    by_cases ho : id ∈ s.cfg.outgoing
    · simp only [ho, ↓reduceIte]
      have hnl : id ∉ s.cfg.learners := fun h' => (hl id h').2 ho
      refine ⟨fun k => ?_, fun k b hb => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · rw [hd, mem_ids, mem_ids, removeCfg_incoming, removeCfg_outgoing, removeCfg_learners]
        by_cases e : k = id
        · subst e; simp [ho]
        · simp [e]
      · rw [hf k b hb]
        by_cases e : k = id
        · subst e; simp [gm_mem_delete, hnl]
        · simp [gm_mem_delete, e]
      · rw [removeCfg_learners] at hk
        obtain ⟨a1, a2⟩ := hl k hk.2
        rw [removeCfg_incoming, removeCfg_outgoing]
        exact ⟨fun h' => a1 h'.2, a2⟩
      · rw [removeCfg_learnersNext] at hk
        rw [removeCfg_outgoing]
        exact hn2 k hk.2
    · simp only [ho, ↓reduceIte]
      refine ⟨fun k => ?_, fun k b hb => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · rw [gm_mem_delete, hd, mem_ids, mem_ids, removeCfg_incoming, removeCfg_outgoing,
          removeCfg_learners]
        by_cases e : k = id
        · subst e; simp [ho]
        · simp [e]
      · rw [gm_lookup_delete] at hb
        split at hb
        · cases hb
        · rename_i e
          rw [hf k b hb]
          simp [gm_mem_delete, e]
      · rw [removeCfg_learners] at hk
        obtain ⟨a1, a2⟩ := hl k hk.2
        rw [removeCfg_incoming, removeCfg_outgoing]
        exact ⟨fun h' => a1 h'.2, a2⟩
      · rw [removeCfg_learnersNext] at hk
        rw [removeCfg_outgoing]
        exact hn2 k hk.2
  · exact h

theorem CCGood.makeLearner {s : CCState} (h : CCGood s) (id : w64) :
    CCGood (makeLearnerM id s) := by
  unfold makeLearnerM
  split
  · rename_i hn
    exact h.initProgress id true (by rw [GMap.mem_iff, hn]; simp)
  · exact h
  · rename_i hfalse
    obtain ⟨hd, hf, hl, hn2⟩ := h
    have ht : id ∈ s.prs := by rw [GMap.mem_iff, hfalse]; rfl
    have hnl : id ∉ s.cfg.learners := by
      intro h'
      have := hf id false hfalse
      simp [h'] at this
    split
    · rename_i ho
      refine ⟨fun k => ?_, fun k b hb => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · simp only
        rw [hd, mem_ids, mem_ids, removeCfg_incoming, removeCfg_outgoing, removeCfg_learners]
        by_cases e : k = id
        · subst e; simp [ho]
        · simp [e]
      · simp only
        rw [hf k b hb]
        by_cases e : k = id
        · subst e; simp [gm_mem_delete, hnl]
        · simp [gm_mem_delete, e]
      · simp only at hk ⊢
        rw [removeCfg_learners] at hk
        obtain ⟨a1, a2⟩ := hl k hk.2
        rw [removeCfg_incoming, removeCfg_outgoing]
        exact ⟨fun h' => a1 h'.2, a2⟩
      · simp only at hk ⊢
        rw [gm_mem_insert, gm_mem_delete] at hk
        rw [removeCfg_outgoing]
        rcases hk with rfl | ⟨hk1, hk2⟩
        · exact ho
        · exact hn2 k hk2
    · rename_i ho
      refine ⟨fun k => ?_, fun k b hb => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · simp only
        rw [gm_mem_insert, hd, mem_ids, mem_ids, removeCfg_incoming, removeCfg_outgoing,
          gm_mem_insert, gm_mem_delete]
        by_cases e : k = id
        · subst e; simp
        · simp [e]
      · simp only at hb ⊢
        rw [gm_lookup_insert] at hb
        split at hb
        · subst_vars; cases hb; simp [gm_mem_insert]
        · rename_i e
          rw [hf k b hb]
          simp [gm_mem_insert, gm_mem_delete, e]
      · simp only at hk ⊢
        rw [gm_mem_insert, gm_mem_delete] at hk
        rw [removeCfg_incoming, removeCfg_outgoing]
        rcases hk with rfl | ⟨hk1, hk2⟩
        · exact ⟨fun h' => h'.1 rfl, ho⟩
        · obtain ⟨a1, a2⟩ := hl k hk2
          exact ⟨fun h' => a1 h'.2, a2⟩
      · simp only at hk ⊢
        rw [removeCfg_learnersNext] at hk
        rw [removeCfg_outgoing]
        exact hn2 k hk.2

theorem CCGood.applyOne {s s' : CCState} (h : CCGood s) (cc : ConfChangeSingleM)
    (H : applyOne cc s = some s') : CCGood s' := by
  unfold EtcdGrove.applyOne at H
  split at H
  · cases H; exact h
  split at H
  · cases H; exact h.makeVoter _
  split at H
  · cases H; exact h.makeLearner _
  split at H
  · cases H; exact h.remove _
  split at H
  · cases H; exact h
  · cases H

theorem CCGood.applyAll {s s' : CCState} (h : CCGood s) (ccs : List ConfChangeSingleM)
    (H : applyAll ccs s = some s') : CCGood s' := by
  induction ccs generalizing s with
  | nil => cases H; exact h
  | cons cc ccs IH =>
    simp only [EtcdGrove.applyAll] at H
    cases h1 : EtcdGrove.applyOne cc s with
    | none => rw [h1] at H; cases H
    | some s1 =>
      rw [h1] at H
      exact IH (h.applyOne cc h1) H

theorem CCGood.applyM {s s' : CCState} (h : CCGood s) (ccs : List ConfChangeSingleM)
    (H : applyM ccs s = some s') : CCGood s' := by
  unfold EtcdGrove.applyM at H
  cases h1 : EtcdGrove.applyAll ccs s with
  | none => rw [h1] at H; cases H
  | some s1 =>
    rw [h1] at H
    simp only [Option.bind] at H
    split at H
    · cases H
    · cases H; exact h.applyAll ccs h1

theorem checkedM_some {s s' : CCState} (H : checkedM s = some s') : s' = s ∧ CfgInv s := by
  unfold checkedM at H
  split at H
  · cases H; exact ⟨rfl, ‹_›⟩
  · cases H

theorem CCGood.simple {s s' : CCState} (h : CCGood s) (ccs : List ConfChangeSingleM)
    (H : simpleM ccs s = some s') : CCGood s' := by
  unfold simpleM at H
  split at H
  · cases H
  split at H
  · cases H
  split at H
  · cases H
  · rename_i s1 h1
    split at H
    · cases H
    · obtain ⟨rfl, -⟩ := checkedM_some H
      exact h.clearAutoLeave.applyM ccs h1

theorem CCGood.enterJoint {s s' : CCState} (h : CCGood s) (al : Bool)
    (ccs : List ConfChangeSingleM) (H : enterJointM al ccs s = some s') : CCGood s' := by
  unfold enterJointM at H
  split at H
  · cases H
  split at H
  · cases H
  rename_i hout0
  have hout : s.cfg.outgoing = ∅ := Classical.byContradiction (fun hc => hout0 hc)
  split at H
  · cases H
  split at H
  · cases H
  · rename_i s1 h1
    obtain ⟨rfl, -⟩ := checkedM_some H
    have h0 : CCGood { cfg := { s.cfg with outgoing := s.cfg.incoming, autoLeave := false }, prs := s.prs } := by
      obtain ⟨hd, hf, hl, hn2⟩ := h
      refine ⟨fun k => ?_, fun k b hb => hf k b hb, fun k hk => ?_, fun k hk => ?_⟩
      · rw [hd, mem_ids, mem_ids, hout]
        simp only [GMap.elem_of_empty, false_or]
        by_cases e1 : k ∈ s.cfg.incoming <;> simp [e1]
      · exact ⟨(hl k hk).1, (hl k hk).1⟩
      · have := hn2 k hk
        rw [hout] at this
        exact absurd this (GMap.not_elem_of_empty _)
    have h2 := h0.applyM ccs h1
    exact h2

theorem CCGood.leaveJoint {s s' : CCState} (h : CCGood s) (H : leaveJointM s = some s') :
    CCGood s' := by
  unfold leaveJointM at H
  split at H
  · cases H
  split at H
  · cases H
  obtain ⟨rfl, hci⟩ := checkedM_some H
  obtain ⟨hd, hf, hl, hn2⟩ := h
  -- the merged flags: staged learners `true`, the rest as tracked
  have hlk : ∀ k, (GMap.fmap (fun _ => true)
      (GMap.filter (fun k _ => decide (k ∈ s.cfg.learnersNext)) s.prs) ∪ s.prs) !! k =
      if k ∈ s.cfg.learnersNext ∧ k ∈ s.prs then some true else s.prs !! k := by
    intro k
    by_cases hk : k ∈ s.cfg.learnersNext ∧ k ∈ s.prs
    · rw [ite_eq_left hk]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ((GMap.mem_iff _ _).1 hk.2)
      apply GMap.lookup_union_Some_l
      rw [GMap.lookup_fmap, GMap.lookup_filter, hb]
      simp [hk.1]
    · rw [ite_eq_right hk]
      apply GMap.lookup_union_r
      rw [GMap.lookup_fmap, GMap.lookup_filter]
      cases hb : s.prs !! k with
      | none => rfl
      | some b =>
        have : k ∉ s.cfg.learnersNext := fun h' => hk ⟨h', by rw [GMap.mem_iff, hb]; rfl⟩
        simp [this]
  refine ⟨fun k => ?_, fun k b hb => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [leaveJointState]
    rw [GMap.mem_iff, GMap.lookup_filter, hlk, mem_ids]
    simp only [GMap.elem_of_union, GMap.elem_of_empty, false_or]
    have hprs := hd k
    rw [mem_ids] at hprs
    rw [GMap.mem_iff] at hprs
    by_cases hn : k ∈ s.cfg.learnersNext
    · have ht : k ∈ s.prs := (hd k).2 ((mem_ids _ _).2 (.inr (.inl (hn2 k hn))))
      simp [hn, ht]
    · simp only [hn, false_and, ↓reduceIte, or_false]
      cases hb : s.prs !! k with
      | none =>
        rw [hb] at hprs
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_or] at hprs
        simp [hprs.1, hprs.2.2]
      | some b =>
        rw [hb] at hprs
        simp only [Option.isSome_some, true_iff] at hprs
        simp only [Option.filter]
        by_cases hi : k ∈ s.cfg.incoming
        · simp [hi]
        · by_cases hl' : k ∈ s.cfg.learners
          · simp [hl']
          · have ho : k ∈ s.cfg.outgoing := by
              rcases hprs with h' | h' | h'
              · exact absurd h' hi
              · exact h'
              · exact absurd h' hl'
            simp [hi, hl', ho]
  · simp only [leaveJointState] at hb ⊢
    rw [GMap.lookup_filter, hlk] at hb
    simp only [GMap.elem_of_union]
    by_cases hn : k ∈ s.cfg.learnersNext ∧ k ∈ s.prs
    · rw [ite_eq_left hn] at hb
      simp only [Option.filter] at hb
      split at hb
      · cases hb; simp [hn.1]
      · cases hb
    · rw [ite_eq_right hn] at hb
      cases hb' : s.prs !! k with
      | none => rw [hb'] at hb; cases hb
      | some b' =>
        rw [hb'] at hb
        simp only [Option.filter] at hb
        split at hb
        · cases hb
          have hn' : k ∉ s.cfg.learnersNext := fun h' => hn ⟨h', by rw [GMap.mem_iff, hb']; rfl⟩
          rw [hf k b hb']
          simp [hn']
        · cases hb
  · obtain ⟨a1, a2, -⟩ := hci.2.2.1 k hk
    exact ⟨a2, a1⟩
  · simp only [leaveJointState] at hk
    exact absurd hk (GMap.not_elem_of_empty _)

/-- Every choice of `applyConfChange` keeps `CCGood`. -/
theorem ccApplyM_good {s s' : CCState} (h : CCGood s) (t : raftpb.ConfChangeTransition)
    (ccs : List ConfChangeSingleM) (H : ccApplyM t ccs s = some s') : CCGood s' := by
  unfold ccApplyM at H
  split at H
  · exact h.leaveJoint H
  split at H
  · exact h.enterJoint _ ccs H
  · exact h.simple ccs H
  · cases H

/-- `ccApplyM`'s answer passes `checkInvariants`. -/
theorem ccApplyM_inv {s s' : CCState} (t : raftpb.ConfChangeTransition)
    (ccs : List ConfChangeSingleM) (H : ccApplyM t ccs s = some s') : CfgInv s' := by
  unfold ccApplyM at H
  split at H
  · unfold leaveJointM at H
    split at H
    · cases H
    split at H
    · cases H
    obtain ⟨rfl, hi⟩ := checkedM_some H; exact hi
  split at H
  · unfold enterJointM at H
    split at H
    · cases H
    split at H
    · cases H
    split at H
    · cases H
    split at H
    · cases H
    obtain ⟨rfl, hi⟩ := checkedM_some H; exact hi
  · unfold simpleM at H
    split at H
    · cases H
    split at H
    · cases H
    split at H
    · cases H
    split at H
    · cases H
    obtain ⟨rfl, hi⟩ := checkedM_some H; exact hi
  · cases H

/-- What `confchange` sees of a node at the configuration `c`: its voters tracked as
non-learners, its learners as learners (`cfgState` at any configuration). -/
def cfgStateC (c : CfgM) : CCState := { cfg := c, prs := cfgFlags c.voters c.learners }

theorem cfgStateC_simple (cfg lrn : GSet w64) :
    cfgStateC (CfgM.simple cfg lrn) = cfgState cfg lrn := by
  unfold cfgStateC cfgState
  rw [CfgM.voters_simple]; rfl

/-- (2026-10-15, stage N) A configuration of voters only is a reachable `confchange` state. -/
theorem ccGood_cfgState (V : GSet w64) : CCGood (cfgState V ∅) := by
  refine ⟨fun k => ?_, fun k b hb => ?_, fun k hk => absurd hk (GMap.not_elem_of_empty _),
    fun k hk => absurd hk (GMap.not_elem_of_empty _)⟩
  · show k ∈ cfgFlags V ∅ ↔ k ∈ (cfgM V ∅).ids
    rw [cfgFlags_mem, mem_ids]
    simp only [cfgM]
    constructor
    · rintro (h | h)
      · exact .inl h
      · exact absurd h (GMap.not_elem_of_empty _)
    · rintro (h | h | h)
      · exact .inl h
      · exact absurd h (GMap.not_elem_of_empty _)
      · exact absurd h (GMap.not_elem_of_empty _)
  · have hb' : cfgFlags V ∅ !! k = some b := hb
    rw [cfgFlags_lookup] at hb'
    have hl : k ∉ (cfgM V ∅).learners := GMap.not_elem_of_empty _
    by_cases h1 : k ∈ V
    · rw [ite_eq_left h1] at hb'; cases hb'
      show false = decide (k ∈ (cfgM V ∅).learners)
      simp [hl]
    · rw [ite_eq_right h1, ite_eq_right (GMap.not_elem_of_empty _)] at hb'; cases hb'

/-- A reachable state's flags are its configuration's (`cfgStateC`). -/
theorem CCGood.flags {c : CfgM} {f : GMap w64 Bool} (h : CCGood ⟨c, f⟩) :
    f = cfgFlags c.voters c.learners := by
  obtain ⟨hd, hf, hl, -⟩ := h
  apply GMap.map_eq; intro k
  rw [cfgFlags_lookup]
  by_cases hv : k ∈ c.voters
  · have hk : k ∈ f := (hd k).2 (GMap.elem_of_union_l _ hv)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ((GMap.mem_iff _ _).1 hk)
    have hnl : k ∉ c.learners := by
      intro h'
      obtain ⟨a1, a2⟩ := hl k h'
      unfold CfgM.voters at hv
      rcases (GMap.elem_of_union _ _ _).1 hv with h'' | h''
      · exact a1 h''
      · exact a2 h''
    rw [ite_eq_left hv, hb, hf k b hb]
    simp [hnl]
  · rw [ite_eq_right hv]
    by_cases hl' : k ∈ c.learners
    · have hk : k ∈ f := (hd k).2 (GMap.elem_of_union_r _ hl')
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ((GMap.mem_iff _ _).1 hk)
      rw [ite_eq_left hl', hb, hf k b hb]
      simp [hl']
    · rw [ite_eq_right hl']
      have hk : k ∉ f := by
        rw [hd, mem_ids]
        intro h'
        rcases h' with h' | h' | h'
        · exact hv (GMap.elem_of_union_l _ h')
        · exact hv (GMap.elem_of_union_r _ h')
        · exact hl' h'
      rw [GMap.mem_iff] at hk
      cases h3 : f !! k with
      | none => rfl
      | some _ => rw [h3] at hk; exact absurd rfl hk

end model

end EtcdGrove
end Perennial
