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

/-- **The transaction's objects are disjoint**: a node of a bucket is no bucket and no other
bucket's node. -/
def objsDisj (T : WTx) : Prop :=
  ∀ bl B, T.bs !! bl = some B → ∀ n, (B.ns !! n).isSome → T.bs !! n = none ∧
    ∀ bl' B', T.bs !! bl' = some B' → bl' ≠ bl → B'.ns !! n = none

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

end objs

end bbolt
end EtcdGrove
end Perennial
