/-
The writer's objects (`WTx.objs`) by lookup (U8, `notes/bbolt-proof-plan.md`).

`WTx.objs` folds the buckets' nodes over the dead nodes, so a lookup is the record a bucket's
`ns` holds only when no other bucket holds the same node: `objsDisj` (`objs_node`). The buckets
are `WTx.bobjs` (batch 14: `bobjs_bkt`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Wtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section objs
variable [GooseExts]

-- `objsDisj` is in `Model/Wtx.lean` (shared: `wtxHeap` holds it).

private def insNodes (bl : Loc) (L : List (Loc × NRec)) (m : GMap Loc WObj) : GMap Loc WObj :=
  L.foldl (fun m' lr => m'.insert lr.1 (.node bl lr.2)) m

private theorem insNodes_notin (bl : Loc) (L : List (Loc × NRec)) (m : GMap Loc WObj) (k : Loc)
    (hk : k ∉ L.map Prod.fst) : insNodes bl L m !! k = m !! k := by
  induction L generalizing m with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    simp only [insNodes, List.foldl_cons] at ih ⊢
    rw [ih _ hk.2, GMap.lookup_insert_ne _ _ (Ne.symm hk.1)]

private theorem insNodes_in (bl : Loc) (L : List (Loc × NRec)) (m : GMap Loc WObj) (k : Loc)
    (r : NRec) (hnd : (L.map Prod.fst).Nodup) (hk : (k, r) ∈ L) :
    insNodes bl L m !! k = some (.node bl r) := by
  induction L generalizing m with
  | nil => simp at hk
  | cons a L ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [insNodes, List.foldl_cons] at ih ⊢
    rcases List.mem_cons.1 hk with h | h
    · subst h
      have := insNodes_notin bl L (m.insert k (.node bl r)) k hnd.1
      simp only [insNodes] at this
      rw [this, GMap.lookup_insert]
    · exact ih _ hnd.2 h

private def objStep (m : GMap Loc WObj) (bB : Loc × BRec) : GMap Loc WObj :=
  insNodes bB.1 bB.2.ns.toList m

/-- The dead nodes as objects. -/
def WTx.deadObjs (T : WTx) : GMap Loc WObj := T.dead.fmap fun p => .node p.1 p.2

private theorem objs_eq (T : WTx) : T.objs = T.bs.toList.foldl objStep T.deadObjs := rfl

private theorem objStep_notin (m : GMap Loc WObj) (bB : Loc × BRec) (k : Loc)
    (h2 : bB.2.ns !! k = none) : objStep m bB !! k = m !! k := by
  unfold objStep
  apply insNodes_notin
  intro hm
  obtain ⟨⟨k', r⟩, hm', hk⟩ := List.mem_map.1 hm
  simp only at hk
  subst hk
  rw [(GMap.mem_toList _ _ _).1 hm'] at h2
  simp at h2

private theorem fold_notin (L : List (Loc × BRec)) (m : GMap Loc WObj) (k : Loc)
    (h : ∀ bB ∈ L, bB.2.ns !! k = none) : L.foldl objStep m !! k = m !! k := by
  induction L generalizing m with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun bB hb => h bB (List.mem_cons_of_mem _ hb))]
    exact objStep_notin m a k (h a List.mem_cons_self)

private theorem fold_node (L : List (Loc × BRec)) (m : GMap Loc WObj) (bl : Loc) (B : BRec)
    (n : Loc) (r : NRec) (hnd : (L.map Prod.fst).Nodup) (hin : (bl, B) ∈ L)
    (hr : B.ns !! n = some r)
    (hoth : ∀ bB ∈ L, bB.1 ≠ bl → bB.2.ns !! n = none) :
    L.foldl objStep m !! n = some (.node bl r) := by
  induction L generalizing m with
  | nil => simp at hin
  | cons a L ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hin with h | h
    · subst h
      rw [fold_notin L _ n (fun bB hb =>
        hoth bB (List.mem_cons_of_mem _ hb) (fun he => hnd.1 (by rw [← he]; exact List.mem_map.2 ⟨bB, hb, rfl⟩)))]
      unfold objStep
      exact insNodes_in bl _ m n r (GMap.toList_keys_nodup _) ((GMap.mem_toList _ _ _).2 hr)
    · exact ih _ hnd.2 h (fun bB hb => hoth bB (List.mem_cons_of_mem _ hb))

/-- **A bucket of the transaction is its bucket object** (batch 14: buckets are `bobjs`'). -/
theorem bobjs_bkt (T : WTx) (bl : Loc) (B : BRec) (hb : T.bs !! bl = some B) :
    T.bobjs !! bl = some B := by
  unfold WTx.bobjs
  exact GMap.lookup_union_Some_l _ _ _ _ hb

/-- **A node of a bucket is its object** (a node in at most one bucket). -/
theorem objs_node (T : WTx) (bl : Loc) (B : BRec) (n : Loc) (r : NRec) (hd : objsDisj T)
    (hb : T.bs !! bl = some B) (hr : B.ns !! n = some r) :
    T.objs !! n = some (.node bl r) := by
  rw [objs_eq]
  have hd' := hd bl B hb n (by simp [hr])
  apply fold_node _ _ bl B n r (GMap.toList_keys_nodup _) ((GMap.mem_toList _ _ _).2 hb) hr
  intro ⟨bl', B'⟩ hm hne
  exact hd' bl' B' ((GMap.mem_toList _ _ _).1 hm) hne

/-- A location no bucket holds as a node is the dead nodes'. -/
theorem objs_other (T : WTx) (k : Loc)
    (h : ∀ bl B, T.bs !! bl = some B → B.ns !! k = none) :
    T.objs !! k = T.deadObjs !! k := by
  rw [objs_eq]
  apply fold_notin
  intro ⟨bl, B⟩ hm
  exact h bl B ((GMap.mem_toList _ _ _).1 hm)

/-- The transaction with node `n` of bucket `bl` (record `B`) holding `r'`. -/
def WTx.setNodeT (T : WTx) (bl n : Loc) (B : BRec) (r' : NRec) : WTx :=
  { T with bs := T.bs.insert bl { B with ns := B.ns.insert n r' } }

theorem objsDisj_setNodeT (T : WTx) (bl n : Loc) (B : BRec) (r r' : NRec) (hd : objsDisj T)
    (hb : T.bs !! bl = some B) (hr : B.ns !! n = some r) :
    objsDisj (T.setNodeT bl n B r') := by
  have hns : ∀ k, (({ B with ns := B.ns.insert n r' } : BRec).ns !! k).isSome =
      (B.ns !! k).isSome := by
    intro k
    by_cases hk : k = n
    · subst hk; simp [GMap.lookup_insert, hr]
    · simp [Ne.symm hk]
  have hlook : ∀ c C, (T.setNodeT bl n B r').bs !! c = some C → ∃ C0, T.bs !! c = some C0 ∧
      ∀ k, (C.ns !! k).isSome = (C0.ns !! k).isSome := by
    intro c C hc
    by_cases hcb : c = bl
    · subst hcb
      simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hc
      subst hc
      exact ⟨B, hb, hns⟩
    · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hc
      exact ⟨C, hc, fun _ => rfl⟩
  intro c C hc k hk c' C' hc' hne
  obtain ⟨C0, hc0, hC⟩ := hlook c C hc
  rw [hC] at hk
  obtain ⟨C0', hc0', hC'⟩ := hlook c' C' hc'
  have h3 := hd c C0 hc0 k hk c' C0' hc0' hne
  have e := hC' k
  rw [h3] at e
  cases h : C'.ns !! k with
  | none => rfl
  | some _ => rw [h] at e; simp at e

/-- **The nodes after a node's record changes**: the node's record replaced. -/
theorem objs_setNodeT (T : WTx) (bl n : Loc) (B : BRec) (r r' : NRec) (hd : objsDisj T)
    (hb : T.bs !! bl = some B) (hr : B.ns !! n = some r) :
    (T.setNodeT bl n B r').objs = T.objs.insert n (.node bl r') := by
  have hd' := objsDisj_setNodeT T bl n B r r' hd hb hr
  apply GMap.map_eq
  intro k
  by_cases hk2 : k = n
  · subst hk2
    rw [GMap.lookup_insert]
    exact objs_node _ bl { B with ns := B.ns.insert k r' } k r' hd' (by simp [WTx.setNodeT])
      (by simp)
  rw [GMap.lookup_insert_ne _ _ (Ne.symm hk2)]
  by_cases hkn : ∃ c C rk, T.bs !! c = some C ∧ C.ns !! k = some rk
  · obtain ⟨c, C, rk, hC, hrk⟩ := hkn
    rw [objs_node T c C k rk hd hC hrk]
    by_cases hcb : c = bl
    · subst hcb
      rw [hb] at hC; cases hC
      exact objs_node _ c { B with ns := B.ns.insert n r' } k rk hd' (by simp [WTx.setNodeT])
        (by simp [Ne.symm hk2, hrk])
    · exact objs_node _ c C k rk hd'
        (by simp [WTx.setNodeT, Ne.symm hcb, hC]) hrk
  · have hno : ∀ c C, T.bs !! c = some C → C.ns !! k = none := by
      intro c C hC
      cases h : C.ns !! k with
      | none => rfl
      | some rk => exact absurd ⟨c, C, rk, hC, h⟩ hkn
    rw [objs_other T k hno, objs_other]
    · rfl
    intro c C hC
    by_cases hcb : c = bl
    · subst hcb
      simp only [WTx.setNodeT, GMap.lookup_insert, Option.some.injEq] at hC
      subst hC
      simp only [GMap.lookup_insert_ne _ _ (Ne.symm hk2)]
      exact hno c B hb
    · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hC
      exact hno c C hC

/-- **The buckets after a node's record changes**: its bucket's record replaced. -/
theorem bobjs_setNodeT (T : WTx) (bl n : Loc) (B : BRec) (r' : NRec) :
    (T.setNodeT bl n B r').bobjs = T.bobjs.insert bl { B with ns := B.ns.insert n r' } := by
  apply GMap.map_eq
  intro k
  by_cases hk : k = bl
  · subst hk; simp [WTx.setNodeT, WTx.bobjs, GMap.lookup_insert]
  · have hk' : bl ≠ k := Ne.symm hk
    simp [WTx.setNodeT, WTx.bobjs, GMap.lookup_insert_ne _ _ hk', hk']

end objs

end bbolt
end EtcdGrove
end Perennial
