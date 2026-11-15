/-
`node.put`'s and `node.del`'s entries on a sorted node (U7h, for `Put`/`Delete`/`CreateBucket`):
`wsPutAt ws e.key e` (at the search index) is the logical `wsPut ws e`, and `wsDelAt ws k` is
`wsDel ws k`, so that `Write/Data`'s `wtxData_put'`/`wtxData_del'` apply.
-/
module

public import Proof.go_etcd_io.bbolt.Write.DataMap
public import Proof.go_etcd_io.bbolt.Model.WOps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section putAt
variable [GooseExts]

omit [GooseExts] in
theorem wsIdx_cons_lt (a : WEntry) (ws : List WEntry) (k : List w8) (h : go.GoStringLt a.key k) :
    wsIdx (a :: ws) k = wsIdx ws k + 1 := by
  unfold wsIdx; rw [List.takeWhile_cons_of_pos (by simpa using h)]; simp

omit [GooseExts] in
theorem wsIdx_cons_nlt (a : WEntry) (ws : List WEntry) (k : List w8)
    (h : ¬ go.GoStringLt a.key k) : wsIdx (a :: ws) k = 0 := by
  unfold wsIdx; rw [List.takeWhile_cons_of_neg (by simpa using h)]; rfl

omit [GooseExts] in
/-- Every later key of a sorted list is above the first. -/
private theorem pw_all_gt {a : WEntry} {ws : List WEntry} {k : List w8} (h : wsPw (a :: ws))
    (hk : ¬ go.GoStringLt a.key k) : ∀ w ∈ ws, go.GoStringLt k w.key := by
  unfold wsPw at h
  rw [List.pairwise_cons] at h
  intro w hw
  by_cases he : a.key = k
  · rw [← he]; exact h.1 w hw
  · have : go.GoStringLt k a.key :=
      Classical.byContradiction fun hc => he (go.goStringLt_eq_of_not_lt hk hc)
    exact go.goStringLt_trans this (h.1 w hw)

/-- **`node.put` at the new entry's own key, on a sorted node, is `wsPut`.** -/
theorem wsPutAt_wsPut (ws : List WEntry) (e : WEntry) (h : wsPw ws) :
    wsPutAt ws e.key e = wsPut ws e := by
  induction ws with
  | nil =>
    unfold wsPutAt wsPut wsFound wsIdx; simp
  | cons a ws ih =>
    have hp : wsPw ws := by unfold wsPw at h ⊢; exact (List.pairwise_cons.1 h).2
    rw [wsPut_split]
    by_cases h1 : go.GoStringLt a.key e.key
    · have h2 : ¬ go.GoStringLt e.key a.key := go.goStringLt_asymm h1
      have hidx := wsIdx_cons_lt a ws e.key h1
      have hf : wsFound (a :: ws) e.key ↔ wsFound ws e.key := by
        unfold wsFound; rw [hidx]; simp
      rw [List.filter_cons_of_pos (by simpa using h1), List.filter_cons_of_neg (by simpa using h2)]
      have ih' := ih hp
      rw [wsPut_split] at ih'
      unfold wsPutAt at ih' ⊢
      rw [hidx]
      by_cases hfw : wsFound ws e.key
      · rw [if_pos (hf.2 hfw)]; rw [if_pos hfw] at ih'
        simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
        rw [ih']
      · rw [if_neg (fun h' => hfw (hf.1 h'))]; rw [if_neg hfw] at ih'
        simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
        rw [ih']
    · have hidx := wsIdx_cons_nlt a ws e.key h1
      have hgt := pw_all_gt h h1
      have hlt0 : ws.filter (fun w => decide (go.GoStringLt w.key e.key)) = [] := by
        rw [List.filter_eq_nil_iff]; intro w hw
        simpa using go.goStringLt_asymm (hgt w hw)
      have hgt0 : ws.filter (fun w => decide (go.GoStringLt e.key w.key)) = ws := by
        rw [List.filter_eq_self]; intro w hw; simpa using hgt w hw
      rw [List.filter_cons_of_neg (by simpa using h1), hlt0]
      unfold wsPutAt
      rw [hidx]
      by_cases he : a.key = e.key
      · have hf : wsFound (a :: ws) e.key := by unfold wsFound; rw [hidx]; simp [he]
        rw [if_pos hf, List.filter_cons_of_neg (by simp [he]; exact go.goStringLt_irrefl _), hgt0]
        simp
      · have hlt : go.GoStringLt e.key a.key :=
          Classical.byContradiction fun hc => he (go.goStringLt_eq_of_not_lt h1 hc)
        have hf : ¬ wsFound (a :: ws) e.key := by unfold wsFound; rw [hidx]; simp [he]
        rw [if_neg hf, List.filter_cons_of_pos (by simpa using hlt), hgt0]
        simp

omit [GooseExts] in
/-- **`node.del` on a sorted node is `wsDel`.** -/
theorem wsDelAt_wsDel (ws : List WEntry) (k : List w8) (h : wsPw ws) :
    wsDelAt ws k = wsDel ws k := by
  induction ws with
  | nil => unfold wsDelAt wsDel; simp
  | cons a ws ih =>
    have hp : wsPw ws := by unfold wsPw at h ⊢; exact (List.pairwise_cons.1 h).2
    unfold wsDel
    by_cases h1 : go.GoStringLt a.key k
    · have hne : a.key ≠ k := fun he => by subst he; exact go.goStringLt_irrefl _ h1
      have hidx := wsIdx_cons_lt a ws k h1
      have hf : wsFound (a :: ws) k ↔ wsFound ws k := by
        unfold wsFound; rw [hidx]; simp
      rw [List.filter_cons_of_pos (by simpa using hne)]
      have ih' := ih hp
      unfold wsDel at ih'
      rw [← ih']
      unfold wsDelAt
      rw [hidx]
      by_cases hfw : wsFound ws k
      · rw [if_pos (hf.2 hfw), if_pos hfw]; simp
      · rw [if_neg (fun h' => hfw (hf.1 h')), if_neg hfw]
    · have hidx := wsIdx_cons_nlt a ws k h1
      have hgt := pw_all_gt h h1
      have hne0 : ws.filter (fun w => decide (w.key ≠ k)) = ws := by
        rw [List.filter_eq_self]; intro w hw
        have := hgt w hw
        simp only [ne_eq, decide_eq_true_eq]
        intro he; rw [he] at this; exact go.goStringLt_irrefl _ this
      unfold wsDelAt
      rw [hidx]
      by_cases he : a.key = k
      · have hf : wsFound (a :: ws) k := by unfold wsFound; rw [hidx]; simp [he]
        rw [if_pos hf, List.filter_cons_of_neg (by simp [he]), hne0]
        simp
      · have hf : ¬ wsFound (a :: ws) k := by unfold wsFound; rw [hidx]; simp [he]
        rw [if_neg hf, List.filter_cons_of_pos (by simpa using he), hne0]

end putAt

end Write

end bbolt
end EtcdGrove
end Perennial
