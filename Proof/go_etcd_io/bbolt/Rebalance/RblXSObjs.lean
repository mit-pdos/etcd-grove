/-
The writer's objects by domain (U8b, `Rebalance/RblXSteps.lean`): whether a location is an
node object of `WTx.objs` does not depend on the buckets' order or disjointness (`objs_isSome`):
the dead nodes and the buckets' nodes. A node killed (moved from its bucket to `dead`) or a
bucket's nodes changed with their domain kept keeps every object (`objs_isSome_mono`; the
buckets: `bobjs_isSome_mono`).
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
      bB.2.ns.toList.foldl (fun m' lr => m'.insert lr.1 (WObj.node bB.1 lr.2)) m) m) !! k).isSome = true ↔
      (m !! k).isSome = true ∨ ∃ bB ∈ L, (bB.2.ns !! k).isSome = true := by
  induction L generalizing m with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons]
    rw [ih]
    have hstep : ((a.2.ns.toList.foldl (fun m' lr => m'.insert lr.1 (WObj.node a.1 lr.2)) m) !!
        k).isSome = true ↔ (m !! k).isSome = true ∨ (a.2.ns !! k).isSome = true := by
      rw [insNodes_isSome]
      have hk : k ∈ a.2.ns.toList.map Prod.fst ↔ (a.2.ns !! k).isSome = true := by
        constructor
        · intro hm
          obtain ⟨⟨k', r⟩, hm', he⟩ := List.mem_map.1 hm
          simp only at he; subst he
          rw [(GMap.mem_toList _ _ _).1 hm']; rfl
        · intro hs
          obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hs
          exact List.mem_map.2 ⟨(k, r), (GMap.mem_toList _ _ _).2 hr, rfl⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq, hk]
    rw [hstep]
    constructor
    · rintro ((h | h) | ⟨bB, hb, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
      · exact Or.inr ⟨bB, List.mem_cons_of_mem _ hb, h⟩
    · rintro (h | ⟨bB, hb, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨bB, hb, h⟩

/-- **The node objects by domain**: the dead ones and the buckets' nodes (batch 14: no
buckets). -/
theorem objs_isSome (T : WTx) (k : Loc) :
    (T.objs !! k).isSome = true ↔ (T.dead !! k).isSome = true ∨
      ∃ bl B, T.bs !! bl = some B ∧ (B.ns !! k).isSome = true := by
  unfold WTx.objs
  rw [fold_isSome]
  have hd : ((T.dead.fmap fun p => WObj.node p.1 p.2) !! k).isSome = (T.dead !! k).isSome := by
    simp only [GMap.lookup_fmap]; cases T.dead !! k <;> rfl
  rw [hd]
  constructor
  · rintro (h | ⟨⟨bl, B⟩, hb, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨bl, B, (GMap.mem_toList _ _ _).1 hb, h⟩
  · rintro (h | ⟨bl, B, hb, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(bl, B), (GMap.mem_toList _ _ _).2 hb, h⟩

/-- **Node objects are kept** when every dead node stays dead, and every node of a bucket stays a
node of a bucket or becomes dead. -/
theorem objs_isSome_mono (T T' : WTx)
    (hd : ∀ k, (T.dead !! k).isSome = true → (T'.dead !! k).isSome = true)
    (hn : ∀ bl B k, T.bs !! bl = some B → (B.ns !! k).isSome = true →
      (T'.dead !! k).isSome = true ∨ ∃ bl' B', T'.bs !! bl' = some B' ∧ (B'.ns !! k).isSome = true)
    (k : Loc) (h : (T.objs !! k).isSome = true) : (T'.objs !! k).isSome = true := by
  rw [objs_isSome] at h ⊢
  rcases h with h | ⟨bl, B, hB, h⟩
  · exact Or.inl (hd k h)
  · rcases hn bl B k hB h with h | ⟨bl', B', hB', h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨bl', B', hB', h'⟩

/-- **Bucket objects are kept** when every dead bucket stays dead and every bucket stays a
bucket. -/
theorem bobjs_isSome_mono (T T' : WTx)
    (hd : ∀ k, (T.deadB !! k).isSome = true → (T'.deadB !! k).isSome = true)
    (hb : ∀ bl, (T.bs !! bl).isSome = true → (T'.bs !! bl).isSome = true)
    (k : Loc) (h : (T.bobjs !! k).isSome = true) : (T'.bobjs !! k).isSome = true := by
  simp only [WTx.bobjs, GMap.lookup_union] at h ⊢
  cases h1 : T.bs !! k with
  | some B =>
    obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.1 (hb k (by rw [h1]; rfl))
    rw [hB']; rfl
  | none =>
    rw [h1] at h
    cases h2 : T'.bs !! k with
    | some _ => rfl
    | none => simpa using hd k (by simpa using h)

/-- **A node in at most one bucket, kept** when the buckets' locations are, and each bucket's
nodes are some of its nodes before. -/
theorem objsDisj_mono (T T' : WTx) (hd : objsDisj T)
    (hdom : ∀ c, (T'.bs !! c).isSome = (T.bs !! c).isSome)
    (hsub : ∀ c C', T'.bs !! c = some C' → ∃ C, T.bs !! c = some C ∧
      ∀ k, (C'.ns !! k).isSome = true → (C.ns !! k).isSome = true) :
    objsDisj T' := by
  intro c C' hC' k hk c' D' hD' hne
  obtain ⟨C, hC, hs⟩ := hsub c C' hC'
  obtain ⟨D, hD, hsD⟩ := hsub c' D' hD'
  have := hd c C hC k (hs k hk) c' D hD hne
  cases h : D'.ns !! k with
  | none => rfl
  | some _ => have := hsD k (by rw [h]; rfl); rw [‹D.ns !! k = none›] at this; cases this

end objs

end bbolt
end EtcdGrove
end Perennial
