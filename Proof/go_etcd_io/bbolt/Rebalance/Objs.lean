/-
The writer's objects (`WTx.objs`) by lookup (U8, `notes/bbolt-proof-plan.md`).

`WTx.objs` folds the buckets' nodes and the buckets over the dead objects, so a lookup is the
record a bucket's `ns` holds only when no other bucket holds the same location (as a node or as
a bucket): `objsDisj`. `wtxHeap_node_acc` (U5) takes the lookup (`objs !! l = some (.node bl r)`),
which the specs' `B.ns !! n = some rn` gives only under `objsDisj` (`objs_node`, `objs_bkt`).
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
  (insNodes bB.1 bB.2.ns.toList m).insert bB.1 (.bkt bB.2)

private theorem objs_eq (T : WTx) : T.objs = T.bs.toList.foldl objStep T.dead := rfl

private theorem objStep_notin (m : GMap Loc WObj) (bB : Loc × BRec) (k : Loc) (h1 : k ≠ bB.1)
    (h2 : bB.2.ns !! k = none) : objStep m bB !! k = m !! k := by
  unfold objStep
  rw [GMap.lookup_insert_ne _ _ (Ne.symm h1)]
  apply insNodes_notin
  intro hm
  obtain ⟨⟨k', r⟩, hm', hk⟩ := List.mem_map.1 hm
  simp only at hk
  subst hk
  rw [(GMap.mem_toList _ _ _).1 hm'] at h2
  simp at h2

private theorem fold_notin (L : List (Loc × BRec)) (m : GMap Loc WObj) (k : Loc)
    (h : ∀ bB ∈ L, k ≠ bB.1 ∧ bB.2.ns !! k = none) : L.foldl objStep m !! k = m !! k := by
  induction L generalizing m with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun bB hb => h bB (List.mem_cons_of_mem _ hb))]
    exact objStep_notin m a k (h a List.mem_cons_self).1 (h a List.mem_cons_self).2

private theorem fold_bkt (L : List (Loc × BRec)) (m : GMap Loc WObj) (bl : Loc) (B : BRec)
    (hnd : (L.map Prod.fst).Nodup) (hin : (bl, B) ∈ L) (hno : ∀ bB ∈ L, bB.2.ns !! bl = none) :
    L.foldl objStep m !! bl = some (.bkt B) := by
  induction L generalizing m with
  | nil => simp at hin
  | cons a L ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hin with h | h
    · subst h
      rw [fold_notin L _ bl (fun bB hb => ⟨fun he => hnd.1 (by rw [he]; exact List.mem_map.2 ⟨bB, hb, rfl⟩),
        hno bB (List.mem_cons_of_mem _ hb)⟩)]
      unfold objStep
      exact GMap.lookup_insert _ _ _
    · exact ih _ hnd.2 h (fun bB hb => hno bB (List.mem_cons_of_mem _ hb))

private theorem fold_node (L : List (Loc × BRec)) (m : GMap Loc WObj) (bl : Loc) (B : BRec)
    (n : Loc) (r : NRec) (hnd : (L.map Prod.fst).Nodup) (hin : (bl, B) ∈ L)
    (hr : B.ns !! n = some r) (hnb : ∀ bB ∈ L, n ≠ bB.1)
    (hoth : ∀ bB ∈ L, bB.1 ≠ bl → bB.2.ns !! n = none) :
    L.foldl objStep m !! n = some (.node bl r) := by
  induction L generalizing m with
  | nil => simp at hin
  | cons a L ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hin with h | h
    · subst h
      rw [fold_notin L _ n (fun bB hb => ⟨hnb bB (List.mem_cons_of_mem _ hb),
        hoth bB (List.mem_cons_of_mem _ hb) (fun he => hnd.1 (by rw [← he]; exact List.mem_map.2 ⟨bB, hb, rfl⟩))⟩)]
      unfold objStep
      rw [GMap.lookup_insert_ne _ _ (Ne.symm (hnb _ List.mem_cons_self))]
      exact insNodes_in bl _ m n r (GMap.toList_keys_nodup _) ((GMap.mem_toList _ _ _).2 hr)
    · exact ih _ hnd.2 h (fun bB hb => hnb bB (List.mem_cons_of_mem _ hb))
        (fun bB hb => hoth bB (List.mem_cons_of_mem _ hb))

/-- A bucket of the transaction is its object, if no bucket holds a node at its location. -/
theorem objs_bkt (T : WTx) (bl : Loc) (B : BRec) (hd : objsDisj T) (hb : T.bs !! bl = some B) :
    T.objs !! bl = some (.bkt B) := by
  rw [objs_eq]
  apply fold_bkt _ _ bl B (GMap.toList_keys_nodup _) ((GMap.mem_toList _ _ _).2 hb)
  intro ⟨bl', B'⟩ hm
  have hb' := (GMap.mem_toList _ _ _).1 hm
  cases h : B'.ns !! bl with
  | none => rfl
  | some r =>
    have := (hd bl' B' hb' bl (by simp [h])).1
    rw [hb] at this; cases this

/-- **A node of a bucket is its object** (disjoint objects). -/
theorem objs_node (T : WTx) (bl : Loc) (B : BRec) (n : Loc) (r : NRec) (hd : objsDisj T)
    (hb : T.bs !! bl = some B) (hr : B.ns !! n = some r) :
    T.objs !! n = some (.node bl r) := by
  rw [objs_eq]
  have hd' := hd bl B hb n (by simp [hr])
  apply fold_node _ _ bl B n r (GMap.toList_keys_nodup _) ((GMap.mem_toList _ _ _).2 hb) hr
  · intro ⟨bl', B'⟩ hm he
    have hb' := (GMap.mem_toList _ _ _).1 hm
    simp only at he
    rw [← he, hd'.1] at hb'; cases hb'
  · intro ⟨bl', B'⟩ hm hne
    exact hd'.2 bl' B' ((GMap.mem_toList _ _ _).1 hm) hne

/-- A location no bucket holds (as itself or a node) is the dead objects'. -/
theorem objs_other (T : WTx) (k : Loc)
    (h : ∀ bl B, T.bs !! bl = some B → k ≠ bl ∧ B.ns !! k = none) :
    T.objs !! k = T.dead !! k := by
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
  have hbs : ∀ c, (T.setNodeT bl n B r').bs !! c = none ↔ T.bs !! c = none := by
    intro c
    by_cases hc : c = bl
    · subst hc; simp [WTx.setNodeT, GMap.lookup_insert, hb]
    · simp [WTx.setNodeT, Ne.symm hc]
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
  intro c C hc k hk
  obtain ⟨C0, hc0, hC⟩ := hlook c C hc
  rw [hC] at hk
  obtain ⟨h1, h2⟩ := hd c C0 hc0 k hk
  refine ⟨(hbs k).2 h1, fun c' C' hc' hne => ?_⟩
  obtain ⟨C0', hc0', hC'⟩ := hlook c' C' hc'
  have h3 := h2 c' C0' hc0' hne
  have e := hC' k
  rw [h3] at e
  cases h : C'.ns !! k with
  | none => rfl
  | some _ => rw [h] at e; simp at e

/-- **The objects after a node's record changes**: the node's, and its bucket's record. -/
theorem objs_setNodeT (T : WTx) (bl n : Loc) (B : BRec) (r r' : NRec) (hd : objsDisj T)
    (hb : T.bs !! bl = some B) (hr : B.ns !! n = some r) :
    (T.setNodeT bl n B r').objs =
      (T.objs.insert n (.node bl r')).insert bl (.bkt { B with ns := B.ns.insert n r' }) := by
  have hd' := objsDisj_setNodeT T bl n B r r' hd hb hr
  have hnb : n ≠ bl := by
    intro h; have := (hd bl B hb n (by simp [hr])).1; rw [h, hb] at this; cases this
  apply GMap.map_eq
  intro k
  by_cases hk1 : k = bl
  · subst hk1
    rw [GMap.lookup_insert]
    exact objs_bkt _ _ _ hd' (by simp [WTx.setNodeT])
  rw [GMap.lookup_insert_ne _ _ (Ne.symm hk1)]
  by_cases hk2 : k = n
  · subst hk2
    rw [GMap.lookup_insert]
    exact objs_node _ bl { B with ns := B.ns.insert k r' } k r' hd' (by simp [WTx.setNodeT])
      (by simp)
  rw [GMap.lookup_insert_ne _ _ (Ne.symm hk2)]
  by_cases hkb : ∃ C, T.bs !! k = some C
  · obtain ⟨C, hC⟩ := hkb
    rw [objs_bkt T k C hd hC]
    exact objs_bkt _ k C hd' (by simp [WTx.setNodeT, Ne.symm hk1, hC])
  · have hkb' : T.bs !! k = none := by
      cases h : T.bs !! k with
      | none => rfl
      | some C => exact absurd ⟨C, h⟩ hkb
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
    · have hno : ∀ c C, T.bs !! c = some C → k ≠ c ∧ C.ns !! k = none := by
        intro c C hC
        refine ⟨fun h => (by rw [← h, hkb'] at hC; cases hC), ?_⟩
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
        refine ⟨hk1, ?_⟩
        simp only [GMap.lookup_insert_ne _ _ (Ne.symm hk2)]
        exact (hno c B hb).2
      · simp only [WTx.setNodeT, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hC
        exact hno c C hC

end objs

end bbolt
end EtcdGrove
end Perennial
