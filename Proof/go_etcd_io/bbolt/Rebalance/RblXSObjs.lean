/-
The writer's objects by domain (U8b, `Rebalance/RblXSteps.lean`): whether a location is an
object of `WTx.objs` does not depend on the buckets' order or disjointness (`objs_isSome`): the
dead objects, the buckets and their nodes. A node killed (moved from its bucket to `dead`) or a
bucket's nodes changed with their domain kept keeps every object (`objs_isSome_mono`).
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

private theorem insNodes_isSome (bl : Loc) (L : List (Loc × NRec)) (m : GMap Loc WObj) (k : Loc) :
    ((L.foldl (fun m' lr => m'.insert lr.1 (WObj.node bl lr.2)) m) !! k).isSome =
      ((m !! k).isSome || decide (k ∈ L.map Prod.fst)) := by
  induction L generalizing m with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons]
    rw [ih]
    by_cases h : a.1 = k
    · subst h; simp
    · rw [GMap.lookup_insert_ne _ _ h]
      simp only [List.map_cons, List.mem_cons]
      have : ¬ k = a.1 := fun e => h e.symm
      simp [this]

private theorem fold_isSome (L : List (Loc × BRec)) (m : GMap Loc WObj) (k : Loc) :
    ((L.foldl (fun m bB =>
      (bB.2.ns.toList.foldl (fun m' lr => m'.insert lr.1 (WObj.node bB.1 lr.2)) m).insert bB.1
        (WObj.bkt bB.2)) m) !! k).isSome = true ↔
      (m !! k).isSome = true ∨ ∃ bB ∈ L, k = bB.1 ∨ (bB.2.ns !! k).isSome = true := by
  induction L generalizing m with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons]
    rw [ih]
    have hstep : (((a.2.ns.toList.foldl (fun m' lr => m'.insert lr.1 (WObj.node a.1 lr.2)) m).insert
        a.1 (WObj.bkt a.2)) !! k).isSome = true ↔
        (m !! k).isSome = true ∨ k = a.1 ∨ (a.2.ns !! k).isSome = true := by
      by_cases h : a.1 = k
      · subst h; simp
      · rw [GMap.lookup_insert_ne _ _ h, insNodes_isSome]
        have hk : k ∈ a.2.ns.toList.map Prod.fst ↔ (a.2.ns !! k).isSome = true := by
          constructor
          · intro hm
            obtain ⟨⟨k', r⟩, hm', he⟩ := List.mem_map.1 hm
            simp only at he; subst he
            rw [(GMap.mem_toList _ _ _).1 hm']; rfl
          · intro hs
            obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hs
            exact List.mem_map.2 ⟨(k, r), (GMap.mem_toList _ _ _).2 hr, rfl⟩
        have : ¬ k = a.1 := fun e => h e.symm
        simp only [Bool.or_eq_true, decide_eq_true_eq, hk, this, false_or]
    rw [hstep]
    constructor
    · rintro ((h | h | h) | ⟨bB, hb, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self, Or.inl h⟩
      · exact Or.inr ⟨a, List.mem_cons_self, Or.inr h⟩
      · exact Or.inr ⟨bB, List.mem_cons_of_mem _ hb, h⟩
    · rintro (h | ⟨bB, hb, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨bB, hb, h⟩

/-- **The objects by domain**: the dead ones, the buckets and their nodes. -/
theorem objs_isSome (T : WTx) (k : Loc) :
    (T.objs !! k).isSome = true ↔ (T.dead !! k).isSome = true ∨
      ∃ bl B, T.bs !! bl = some B ∧ (k = bl ∨ (B.ns !! k).isSome = true) := by
  unfold WTx.objs
  rw [fold_isSome]
  constructor
  · rintro (h | ⟨⟨bl, B⟩, hb, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨bl, B, (GMap.mem_toList _ _ _).1 hb, h⟩
  · rintro (h | ⟨bl, B, hb, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(bl, B), (GMap.mem_toList _ _ _).2 hb, h⟩

/-- **Objects are kept** when every dead object stays dead, every bucket stays a bucket, and
every node of a bucket stays a node of a bucket or becomes dead. -/
theorem objs_isSome_mono (T T' : WTx)
    (hd : ∀ k, (T.dead !! k).isSome = true → (T'.dead !! k).isSome = true)
    (hb : ∀ bl, (T.bs !! bl).isSome = true → (T'.bs !! bl).isSome = true)
    (hn : ∀ bl B k, T.bs !! bl = some B → (B.ns !! k).isSome = true →
      (T'.dead !! k).isSome = true ∨ ∃ bl' B', T'.bs !! bl' = some B' ∧ (B'.ns !! k).isSome = true)
    (k : Loc) (h : (T.objs !! k).isSome = true) : (T'.objs !! k).isSome = true := by
  rw [objs_isSome] at h ⊢
  rcases h with h | ⟨bl, B, hB, rfl | h⟩
  · exact Or.inl (hd k h)
  · obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.1 (hb k (by rw [hB]; rfl))
    exact Or.inr ⟨k, B', hB', Or.inl rfl⟩
  · rcases hn bl B k hB h with h | ⟨bl', B', hB', h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨bl', B', hB', Or.inr h'⟩

/-- **Disjointness is kept** when the buckets' locations are, and each bucket's nodes are some of
its nodes before. -/
theorem objsDisj_mono (T T' : WTx) (hd : objsDisj T)
    (hdom : ∀ c, (T'.bs !! c).isSome = (T.bs !! c).isSome)
    (hsub : ∀ c C', T'.bs !! c = some C' → ∃ C, T.bs !! c = some C ∧
      ∀ k, (C'.ns !! k).isSome = true → (C.ns !! k).isSome = true) :
    objsDisj T' := by
  intro c C' hC' k hk
  obtain ⟨C, hC, hs⟩ := hsub c C' hC'
  obtain ⟨h1, h2⟩ := hd c C hC k (hs k hk)
  refine ⟨?_, fun c' D' hD' hne => ?_⟩
  · have := hdom k; rw [h1] at this
    cases h : T'.bs !! k with
    | none => rfl
    | some _ => rw [h] at this; cases this
  · obtain ⟨D, hD, hsD⟩ := hsub c' D' hD'
    have := h2 c' D hD hne
    cases h : D'.ns !! k with
    | none => rfl
    | some _ => have := hsD k (by rw [h]; rfl); rw [‹D.ns !! k = none›] at this; cases this

end objs

end bbolt
end EtcdGrove
end Perennial
