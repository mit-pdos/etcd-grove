/-
Applying a configuration change at any configuration (2026-10-13, reconfiguration stage A2),
Lean-first.

* `CCGood`: what every `confchange` state the node can reach satisfies -- the progress map
  tracks exactly the configuration's ids (`CfgM.ids`), each tracked `IsLearner` is whether
  the id is a learner, a learner is no voter, a staged learner is an outgoing voter and no
  incoming one. Every `Changer` operation keeps it (`ccApplyM_good`): so a `Changer` result is
  the configuration of an `ownTrackerC` (`LearnerFlagsC`, `domSet = ids`), which stage A1
  checked by hand.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApplyConf

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
        · subst e; simp [removeCfg_learners, gm_mem_delete, hnl]
        · simp [removeCfg_learners, gm_mem_delete, e]
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
          simp [removeCfg_learners, gm_mem_delete, e]
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
        · subst e; simp [removeCfg_learners, gm_mem_delete, hnl]
        · simp [removeCfg_learners, gm_mem_delete, e]
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

theorem CCGood.applyOne {s s' : CCState} (h : CCGood s) (cc : raftpb.ConfChangeSingle)
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

theorem CCGood.applyAll {s s' : CCState} (h : CCGood s) (ccs : List raftpb.ConfChangeSingle)
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

theorem CCGood.applyM {s s' : CCState} (h : CCGood s) (ccs : List raftpb.ConfChangeSingle)
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

theorem CCGood.simple {s s' : CCState} (h : CCGood s) (ccs : List raftpb.ConfChangeSingle)
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
    (ccs : List raftpb.ConfChangeSingle) (H : enterJointM al ccs s = some s') : CCGood s' := by
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
    · rw [if_pos hk]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ((GMap.mem_iff _ _).1 hk.2)
      apply GMap.lookup_union_Some_l
      rw [GMap.lookup_fmap, GMap.lookup_filter, hb]
      simp [hk.1]
    · rw [if_neg hk]
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
        simp only [Option.filter, Option.isSome_some]
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
    · rw [if_pos hn] at hb
      simp only [Option.filter] at hb
      split at hb
      · cases hb; simp [hn.1]
      · cases hb
    · rw [if_neg hn] at hb
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
    (ccs : List raftpb.ConfChangeSingle) (H : ccApplyM t ccs s = some s') : CCGood s' := by
  unfold ccApplyM at H
  split at H
  · exact h.leaveJoint H
  split at H
  · exact h.enterJoint _ ccs H
  · exact h.simple ccs H
  · cases H

/-- `ccApplyM`'s answer passes `checkInvariants`. -/
theorem ccApplyM_inv {s s' : CCState} (t : raftpb.ConfChangeTransition)
    (ccs : List raftpb.ConfChangeSingle) (H : ccApplyM t ccs s = some s') : CfgInv s' := by
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

end model

/-! ## The tracker as a `Changer` reads it, and a result as `switchToConfig` takes it -/

section heap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ownTracker_toCC` at any configuration: the node's tracker at `c` as the `Changer` reads it
(`ownTrackerCC` at `c`), the old `Progress` objects' rings set apart (`progRAt`), the tally;
the `Changer`'s state is `⟨c, trkFlags t.peers⟩`, which is reachable (`CCGood`) and passes
`checkInvariants`. -/
theorem ownTrackerC_toCC (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ownTrackerC (GF := GF) c tv t ⊢ ∃ (pvs : GMap w64 tracker.Progress),
      ownTrackerCC tv (DFrac.own 1) DFrac.discard (DFrac.own 1) c t.prs pvs ∗
      ([∗map] k ↦ pv ∈ pvs, progRAt t.peers k pv) ∗
      tv.Votes' ↦$ t.votes ∗
      ⌜flagsOf pvs = trkFlags t.peers⌝ ∗
      ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝ ∗
      ⌜CCGood ⟨c, trkFlags t.peers⟩ ∧ CfgInv ⟨c, trkFlags t.peers⟩ ∧
        domSet t.prs = c.ids ∧ (GMap.size t.prs : Int) ≤ 2 ^ 62⌝ := by
  iintro Hown
  iunfold ownTrackerC at Hown
  iNamed Hown
  ihave H : ([∗map] k ↦ pr;p ∈ t.prs;t.peers, ∃ pv : tracker.Progress,
      (pr ↦ pv ∗ (⌜pv.IsLearner' = p.learner⌝ ∗ (emp ∗ progRAt (GF := GF) t.peers k pv)) :
        IProp GF))
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
  -- the records' flags, read off with their keys
  ihave %Hlf0 := BigSepM2.bigSepM2_lookup_iff $$ H
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun k pr => iprop(∃ pv : tracker.Progress,
      (pr ↦ pv ∗ (⌜pv.IsLearner' = decide (k ∈ c.learners)⌝ ∗
        (emp ∗ progRAt (GF := GF) t.peers k pv)) : IProp GF)))
    (Φ2 := fun (_ : w64) (_ : Progress) => (emp : IProp GF)) Hdom0).1 $$ [H] with ⟨H, -⟩
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr p} _ hp => ?_)) $$ H
    iintro ⟨%pv, Hpv, %Hl, HR⟩
    isplitl
    · iexists pv
      iframe Hpv HR
      ipureintro; rw [Hl]; exact Hflags k p hp
    · iempintro
  icases bigSepM_exist_sepM2 t.prs _ $$ H with ⟨%pvs, H⟩
  ihave %HdomP := BigSepM2.bigSepM2_lookup_iff $$ H
  have Hdom' : ∀ k, (t.prs !! k).isSome ↔ (pvs !! k).isSome := HdomP
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hpt, H⟩
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hl, H⟩
  ihave %Hlf := BigSepM2.bigSepM2_pure_intro $$ Hl
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun k pv => progRAt (GF := GF) t.peers k pv) HdomP).1 $$ H with ⟨-, HR⟩
  iexists pvs
  iframe HR Hvotes
  isplitl [Hcfg Hpt]
  · unfold ownTrackerCC
    iframe Hcfg Hpt Hprs
  ipureintro
  have Hfl : flagsOf pvs = trkFlags t.peers := by
    apply GMap.map_eq; intro k
    rw [flagsOf_lookup', trkFlags_lookup]
    cases hpv : pvs !! k with
    | none =>
      have h1 : (t.prs !! k).isSome = false := by
        cases h : t.prs !! k with
        | none => rfl
        | some _ => have := (Hdom' k).1 (by rw [h]; rfl); rw [hpv] at this; cases this
      cases hp : t.peers !! k with
      | none => rfl
      | some _ => have := (Hdom0' k).2 (by rw [hp]; rfl); rw [h1] at this; cases this
    | some pv =>
      obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom' k).2 (by rw [hpv]; rfl))
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 ((Hdom0' k).1 (by rw [hpr]; rfl))
      rw [hp]
      simp only [Option.map_some]
      rw [Hlf k pr pv hpr hpv, Hflags k p hp]
  refine ⟨Hfl, HmaxInfl, ⟨fun k => ?_, fun k b hb => ?_,
    fun k hk => ⟨(Hinv.2.2.1 k hk).2.1, (Hinv.2.2.1 k hk).1⟩,
    fun k hk => (Hinv.2.1 k hk).1⟩, Hinv, Hdom, Hsize⟩
  · show k ∈ trkFlags t.peers ↔ k ∈ c.ids
    rw [← Hdom, GMap.elem_of_dom', GMap.mem_iff, GMap.mem_iff, trkFlags_lookup, Hdom0' k]
    cases t.peers !! k <;> rfl
  · show b = decide (k ∈ c.learners)
    rw [trkFlags_lookup] at hb
    cases hp : t.peers !! k with
    | none => rw [hp] at hb; cases hb
    | some p =>
      rw [hp] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      rw [← hb]; exact Hflags k p hp

/-- What a result's new object is, once the old objects' rings are moved to it. -/
private def newPrQC (peers : GMap w64 Progress) (k : w64) (pv : tracker.Progress) : IProp GF :=
  iprop(∃ p, ownInflights pv.Inflights' p.infl ∗
    ⌜progressAbs pv p.infl = some p ∧
      (uint.Z p.matched = 0 ∨ ∃ p0, peers !! k = some p0 ∧ p0.matched = p.matched)⌝)

/-- `ownResult_noop_transfer` at any configuration: a `Changer` result in a reachable state
`s'` (`CCGood`, `CfgInv`), with the old objects' rings moved to the new ones, is the new
configuration `switchToConfig` takes (`ownConfigC s'.cfg`), each new `Match` the old one or
`0` (`MatchKept`). -/
theorem ownResult_transfer (s' : CCState) (Hgood : CCGood s') (Hinv : CfgInv s')
    (chg : confchange.Changer)
    (base : GMap w64 tracker.Progress) (peers : GMap w64 Progress) (cfgv : tracker.Config)
    (trk : Loc) (Hsz : (GMap.size s'.cfg.ids : Int) ≤ 2 ^ 62) :
    ownCfgCC (GF := GF) cfgv (DFrac.own 1) s'.cfg ∗
      ownPrsW chg base trk s'.prs ∗
      ([∗map] k ↦ pv ∈ base, progRAt peers k pv) ⊢
      |==> ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
        ownConfigC s'.cfg cfgv trk prs pvs ∗ ⌜MatchKept peers pvs⌝ := by
  iintro ⟨Hc, Hw, HR⟩
  unfold ownPrsW
  icases Hw with ⟨%prs, %pvs, Htrk, Hprs, %Hflags, Hnew⟩
  ihave HQ := ownNewPr_transfer chg base (fun k pv => progRAt (GF := GF) peers k pv)
      (fun k pv => newPrQC (GF := GF) peers k pv) ?_ ?_ pvs $$ [$HR $Hnew]
  · intro k pv0 pv _ h1
    unfold progRAt newPrQC
    iintro ⟨%p, %Hp, Hinfl, %Habs⟩
    iexists { p with learner := pv.IsLearner' }
    have Hinf : pv.Inflights' = pv0.Inflights' := by rw [h1]
    rw [Hinf]
    iframe Hinfl
    ipureintro
    obtain ⟨_, h2, h3, h4, h5, h6, h7, h8⟩ := (progressAbs_Some _ _ _).1 Habs
    refine ⟨(progressAbs_Some _ _ _).2 ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, h8⟩, .inr ⟨p, Hp, rfl⟩⟩ <;>
      (rw [h1]; assumption)
  · intro k pv Hf
    unfold newPrQC
    iintro Hinfl
    iexists progressOf pv .probe (inflightsNew chg.Tracker'.MaxInflight'
      chg.Tracker'.MaxInflightBytes')
    isplitl [Hinfl]
    · simp only [progressOf]; iexact Hinfl
    ipureintro
    obtain ⟨Hm, -, -, Hst, -, -, -⟩ := Hf
    refine ⟨(progressAbs_Some _ _ _).2 ⟨rfl, Hst, rfl, rfl, rfl, rfl, rfl, rfl⟩, .inl ?_⟩
    simp only [progressOf, Hm]; rfl
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdom : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome := Hdom0
  obtain ⟨Hgd, Hgf, -, -⟩ := Hgood
  have Hlf : ∀ k pv, pvs !! k = some pv → pv.IsLearner' = decide (k ∈ s'.cfg.learners) := by
    intro k pv h
    have h' := flagsOf_lookup pvs k pv h
    rw [Hflags] at h'
    exact Hgf k _ h'
  have Hpdom : domSet prs = s'.cfg.ids := by
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom', GMap.mem_iff, Hdom k, ← flagsOf_mem, Hflags]
    exact Hgd k
  ihave HQ2 := (BigSepM2.bigSepM2_sepM (Φ1 := fun (_ : w64) (_ : Loc) => (emp : IProp GF))
    (Φ2 := fun k pv => newPrQC (GF := GF) peers k pv) (m1 := prs) (m2 := pvs) Hdom0).2 $$ [HQ]
  · isplitr
    · iapply (BigSepM.bigSepM_emp (m := prs)).2
      iempintro
    · iexact HQ
  ihave H := BigSepM2.bigSepM2_sep_eqv.2 $$ [$Hprs $HQ2]
  ihave H : ([∗map] k ↦ pr;pv ∈ prs;pvs, ((∃ p, ownProgress pr p ∗
      ⌜(uint.Z p.matched = 0 ∨ ∃ p0, peers !! k = some p0 ∧ p0.matched = p.matched) ∧
        p.learner = decide (k ∈ s'.cfg.learners)⌝) ∗ emp :
        IProp GF)) $$ [H]
  · iapply (BigSepM2.bigSepM2_mono (fun {k pr pv} _ hpv => ?_)) $$ H
    iintro ⟨Hp, -, HQ⟩
    unfold newPrQC
    icases HQ with ⟨%p, Hinfl, %Hp⟩
    obtain ⟨Habs, Hm⟩ := Hp
    isplitl
    · iexists p
      isplitl
      · iapply ownProgress_intro _ _ p $$ Hp Hinfl
        ipureintro; exact Habs
      · ipureintro
        exact ⟨Hm, ((progressAbs_Some _ _ _).1 Habs).1.symm.trans (Hlf k pv hpv)⟩
    · iempintro
  icases (BigSepM2.bigSepM2_sepM (Φ1 := fun k pr => iprop(∃ p, ownProgress (GF := GF) pr p ∗
      ⌜(uint.Z p.matched = 0 ∨ ∃ p0, peers !! k = some p0 ∧ p0.matched = p.matched) ∧
        p.learner = decide (k ∈ s'.cfg.learners)⌝))
    (Φ2 := fun (_ : w64) (_ : tracker.Progress) => (emp : IProp GF)) (m1 := prs) (m2 := pvs)
    Hdom0).1 $$ H with ⟨H, -⟩
  icases bigSepM_exist_sepM2 prs _ $$ H with ⟨%ps, H⟩
  ihave %Hdom2 := BigSepM2.bigSepM2_lookup_iff $$ H
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ H with ⟨Hprogs, Hmk⟩
  ihave %Hmk := BigSepM2.bigSepM2_pure_intro $$ Hmk
  have Hdom2' : ∀ k, (prs !! k).isSome ↔ (ps !! k).isSome := Hdom2
  have Hflc : LearnerFlagsC s'.cfg ps := by
    intro k p hp
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp]; rfl))
    exact (Hmk k pr p hpr hp).2
  have Htf : trkFlags ps = s'.prs := by
    apply GMap.map_eq; intro k
    rw [trkFlags_lookup]
    cases hp : ps !! k with
    | none =>
      have h1 : (prs !! k).isSome = false := by
        cases h : prs !! k with
        | none => rfl
        | some _ => have := (Hdom2' k).1 (by rw [h]; rfl); rw [hp] at this; cases this
      have h2 : k ∉ s'.prs := by
        rw [← Hflags, flagsOf_mem, ← Hdom k, h1]; simp
      rw [GMap.mem_iff] at h2
      cases h3 : s'.prs !! k with
      | none => rfl
      | some _ => rw [h3] at h2; exact absurd rfl h2
    | some p =>
      simp only [Option.map_some]
      obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp]; rfl))
      obtain ⟨pv, hpv⟩ := Option.isSome_iff_exists.1 ((Hdom k).1 (by rw [hpr]; rfl))
      have h' := flagsOf_lookup pvs k pv hpv
      rw [Hflags] at h'
      rw [h', Hflc k p hp, ← Hlf k pv hpv]
  imod ownMap_persist $$ Htrk with #Htrk
  imodintro
  iexists prs, ps
  isplitl
  · unfold ownConfigC
    simp only [named]
    iframe Hc Htrk Hprogs
    ipureintro
    refine ⟨?_, Hpdom, Hflc, ?_⟩
    · rw [Htf]; exact Hinv
    · rw [← GMap.size_dom, Hpdom]; exact Hsz
  · ipureintro
    intro k p' hp'
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 ((Hdom2' k).2 (by rw [hp']; rfl))
    exact (Hmk k pr p' hpr hp').1

end heap

end EtcdGrove
end Perennial
