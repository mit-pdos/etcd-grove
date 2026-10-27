/-
**A write's new state** (pure lemmas): a change logged in one table at the next version, with
the issued UIDs `u`, leaves a well-formed state later than the one before (`St.write_wf`), which
the create, update and delete proofs instantiate. Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.State

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

section pure
variable [FfiSyntax]

@[simp] theorem St.tbl_with (σ : St) (a b : w64) (r : Res) :
    ({ σ with rev := a, uids := b } : St).tbl r = σ.tbl r := by
  cases r <;> rfl

/-- **A write's new state**: `σ` with the change `c` recorded in `r`'s table, at the next
version, `u` UIDs issued. -/
def St.write (σ : St) (r : Res) (c : Change) (u : w64) : St :=
  { σ.setTbl r ((σ.tbl r).record c) with rev := σ.rev + 1, uids := u }

theorem St.write_tbl (σ : St) (r r' : Res) (c : Change) (u : w64) :
    (σ.write r c u).tbl r' = if r' = r then (σ.tbl r).record c else σ.tbl r' := by
  unfold St.write
  rw [St.tbl_with]
  by_cases h : r' = r
  · subst h; simp
  · rw [if_neg h, St.tbl_setTbl_ne _ _ _ _ h]

theorem replay_snoc (l : List Change) (c : Change) :
    replay (l ++ [c]) = applyChange (replay l) c := by
  unfold replay
  rw [List.foldl_append]
  rfl

/-- **A write keeps the state well formed and is later.** -/
theorem St.write_wf (σ : St) (r : Res) (c : Change) (u : w64) (hwf : σ.wf)
    (hrv : c.rv = σ.rev + 1) (hno : (σ.rev + 1).toNat = σ.rev.toNat + 1)
    (hres : c.obj.res = r) (hRV : c.obj.meta.ResourceVersion' = rvStr c.rv)
    (hu1 : σ.uids.toNat ≤ u.toNat) (hu2 : u.toNat < σ.rev.toNat + 1)
    (huid : ∃ n : w64, 1 ≤ n.toNat ∧ n.toNat ≤ u.toNat ∧
      c.obj.meta.UID' = go!"uid-" ++ rvStr n) :
    (σ.write r c u).wf ∧ St.le σ (σ.write r c u) := by
  have hcrv : c.rv.toNat = σ.rev.toNat + 1 := by rw [hrv, hno]
  have hrev' : (σ.write r c u).rev = σ.rev + 1 := rfl
  have huids' : (σ.write r c u).uids = u := rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hrev', hno]; omega
  · intro r'
    rw [St.write_tbl]
    by_cases h : r' = r
    · rw [if_pos h]; subst h
      simp only [Table.record]
      rw [List.pairwise_append]
      refine ⟨hwf.log_sorted r', List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp at hb; subst hb
      have := (hwf.log_le r' a ha).2
      omega
    · rw [if_neg h]; exact hwf.log_sorted r'
  · intro r' c' hc'
    rw [St.write_tbl] at hc'
    rw [hrev', hno]
    by_cases h : r' = r
    · rw [if_pos h] at hc'
      simp only [Table.record, List.mem_append, List.mem_singleton] at hc'
      rcases hc' with hc' | rfl
      · have := hwf.log_le r c' hc'; omega
      · have := hwf.rev_pos; omega
    · rw [if_neg h] at hc'
      have := hwf.log_le r' c' hc'; omega
  · intro r' c' hc'
    rw [St.write_tbl] at hc'
    by_cases h : r' = r
    · rw [if_pos h] at hc'
      simp only [Table.record, List.mem_append, List.mem_singleton] at hc'
      rcases hc' with hc' | rfl
      · subst h; exact hwf.log_obj r' c' hc'
      · exact ⟨h ▸ hres, hRV⟩
    · rw [if_neg h] at hc'
      exact hwf.log_obj r' c' hc'
  · intro r'
    rw [St.write_tbl]
    by_cases h : r' = r
    · rw [if_pos h]
      simp only [Table.record]
      rw [replay_snoc, ← hwf.objs_replay r]
    · rw [if_neg h]; exact hwf.objs_replay r'
  · rw [hrev', huids', hno]; exact hu2
  · intro r' c' hc'
    rw [St.write_tbl] at hc'
    rw [huids']
    by_cases h : r' = r
    · rw [if_pos h] at hc'
      simp only [Table.record, List.mem_append, List.mem_singleton] at hc'
      rcases hc' with hc' | rfl
      · obtain ⟨n, h1, h2, h3⟩ := hwf.log_uid r c' hc'
        exact ⟨n, h1, by omega, h3⟩
      · exact huid
    · rw [if_neg h] at hc'
      obtain ⟨n, h1, h2, h3⟩ := hwf.log_uid r' c' hc'
      exact ⟨n, h1, by omega, h3⟩
  · refine ⟨by rw [hrev', hno]; omega, by rw [huids']; exact hu1, fun r' => ?_⟩
    rw [St.write_tbl]
    by_cases h : r' = r
    · rw [if_pos h]; subst h
      simp only [Table.record]
      refine ⟨List.prefix_append _ _, ?_⟩
      intro x hx
      rw [List.drop_left] at hx
      simp at hx; subst hx
      omega
    · rw [if_neg h]
      refine ⟨List.prefix_refl _, ?_⟩
      intro x hx
      simp at hx

end pure

end apimodel
end EtcdGrove
end Perennial
