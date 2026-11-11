/-
`node.spill`'s tail (U9z, `notes/bbolt-proof-plan.md`; pure): **the frame of `n.children = nil`**
(`spFrame_nilCh`: only `n` and its old children touched; the objects' locations kept,
`objs_isSome_iff`), and what it keeps (`nilCh_spP`, `nilCh_pm`, `nilCh_mv`, `nilCh_objs`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section lemmas
variable [GooseExts]

theorem foldl_ins_isSome {β : Type} (L : List (Loc × β)) (g : Loc × β → WObj)
    (m : GMap Loc WObj) (k : Loc) :
    ((L.foldl (fun m' lr => m'.insert lr.1 (g lr)) m) !! k).isSome ↔
      (m !! k).isSome ∨ ∃ lr ∈ L, lr.1 = k := by
  induction L generalizing m with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases e : a.1 = k
    · subst e
      simp only [GMap.lookup_insert, Option.isSome_some, true_or, true_iff]
      exact Or.inr ⟨a, Or.inl rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ e]
      constructor
      · rintro (h | ⟨lr, hm, he⟩)
        · exact Or.inl h
        · exact Or.inr ⟨lr, Or.inr hm, he⟩
      · rintro (h | ⟨lr, hm | hm, he⟩)
        · exact Or.inl h
        · subst hm; exact absurd he e
        · exact Or.inr ⟨lr, hm, he⟩

theorem toList_key_isSome {V : Type} (m : GMap Loc V) (k : Loc) :
    (∃ lr ∈ m.toList, lr.1 = k) ↔ (m !! k).isSome := by
  constructor
  · rintro ⟨⟨k', v⟩, hm, rfl⟩
    rw [(GMap.mem_toList _ _ _).1 hm]; rfl
  · intro h
    cases e : m !! k with
    | none => rw [e] at h; cases h
    | some v => exact ⟨(k, v), (GMap.mem_toList _ _ _).2 e, rfl⟩

theorem foldl_bkt_isSome (L : List (Loc × BRec)) (m : GMap Loc WObj) (k : Loc) :
    ((L.foldl (fun m bB => bB.2.ns.toList.foldl
        (fun m' lr => m'.insert lr.1 (.node bB.1 lr.2)) m) m) !! k).isSome ↔
      (m !! k).isSome ∨ ∃ bB ∈ L, (bB.2.ns !! k).isSome := by
  induction L generalizing m with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons]
    rw [ih]
    have h1 := foldl_ins_isSome a.2.ns.toList (fun lr => WObj.node a.1 lr.2) m k
    rw [toList_key_isSome] at h1
    rw [h1]
    constructor
    · rintro ((h | h) | ⟨bB, hm, hb⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
      · exact Or.inr ⟨bB, List.mem_cons_of_mem _ hm, hb⟩
    · rintro (h | ⟨bB, hm, hb⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hm with rfl | hm
        · exact Or.inl (Or.inr hb)
        · exact Or.inr ⟨bB, hm, hb⟩

/-- **A location is an object** iff it is a dead node or a node of a bucket. -/
theorem objs_isSome_iff (T : WTx) (k : Loc) :
    (T.objs !! k).isSome ↔ (T.dead !! k).isSome ∨
      ∃ bl B, T.bs !! bl = some B ∧ (B.ns !! k).isSome := by
  unfold WTx.objs
  rw [foldl_bkt_isSome]
  simp only [GMap.lookup_fmap, Option.isSome_map]
  constructor
  · rintro (h | ⟨⟨bl, B⟩, hm, hb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨bl, B, (GMap.mem_toList _ _ _).1 hm, hb⟩
  · rintro (h | ⟨bl, B, hB, hb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(bl, B), (GMap.mem_toList _ _ _).2 hB, hb⟩

/-- `X` after `n.children = nil`, unfolded. -/
theorem nilCh_eq {X : WX} {bl n : Loc} {r : NRec} {B : BRec} (hB : X.t.bs !! bl = some B) :
    X.nilCh bl n r = { X with
      t := ({ X.t with bs := X.t.bs.insert bl ({ B with ns := B.ns.insert n r.nilCh } : BRec) } : WTx),
      live := r.cs.foldr (fun c m => m.delete c) X.live } := by
  unfold WX.nilCh WX.killL WX.setNode WX.setBkt; rw [hB]

theorem nilCh_spP (X : WX) (bl n : Loc) (r : NRec) : spP (X.nilCh bl n r) = spP X := by
  unfold WX.nilCh WX.killL WX.setNode WX.setBkt
  cases X.t.bs !! bl <;> rfl

theorem nilCh_pm (X : WX) (bl n : Loc) (r : NRec) : (X.nilCh bl n r).t.pm = X.t.pm := by
  unfold WX.nilCh WX.killL WX.setNode WX.setBkt
  cases X.t.bs !! bl <;> rfl

theorem nilCh_mv (X : WX) (bl n : Loc) (r : NRec) : (X.nilCh bl n r).t.mv = X.t.mv := by
  unfold WX.nilCh WX.killL WX.setNode WX.setBkt
  cases X.t.bs !! bl <;> rfl

theorem nilCh_bufs (X : WX) (bl n : Loc) (r : NRec) : (X.nilCh bl n r).t.bufs = X.t.bufs := by
  unfold WX.nilCh WX.killL WX.setNode WX.setBkt
  cases X.t.bs !! bl <;> rfl

/-- `n.children = nil` keeps every object. -/
theorem nilCh_objs_isSome {X : WX} {bl n : Loc} {r : NRec} (hn : X.node bl n = some r) {y : Loc}
    (hy : (X.t.objs !! y).isSome) : ((X.nilCh bl n r).t.objs !! y).isSome := by
  obtain ⟨B, hB, hr⟩ := node_bs_of hn
  rw [nilCh_eq hB]
  rw [objs_isSome_iff] at hy ⊢
  rcases hy with hy | ⟨bl', B', hB', hy⟩
  · exact Or.inl hy
  · refine Or.inr ?_
    by_cases hb : bl = bl'
    · subst hb
      rw [hB] at hB'; cases hB'
      refine ⟨bl, _, GMap.lookup_insert _ _ _, ?_⟩
      simp only
      by_cases e : n = y
      · subst e; rw [GMap.lookup_insert]; rfl
      · rw [GMap.lookup_insert_ne _ _ e]; exact hy
    · refine ⟨bl', B', ?_, hy⟩
      show (X.t.bs.insert bl _) !! bl' = some B'
      rw [GMap.lookup_insert_ne _ _ hb]; exact hB'

/-- A location that is no object after `n.children = nil` was none before. -/
theorem nilCh_objs_none {X : WX} {bl n : Loc} {r : NRec} (hn : X.node bl n = some r) {y : Loc}
    (h : (X.nilCh bl n r).t.objs !! y = none) : X.t.objs !! y = none := by
  cases e : X.t.objs !! y with
  | none => rfl
  | some _ =>
    have := nilCh_objs_isSome hn (y := y) (by rw [e]; rfl)
    rw [h] at this; cases this

/-- `n`'s children are of `bl` only, when they are nodes of `bl` and the buckets' nodes are
disjoint (`spFrame_nilCh`'s premise). -/
theorem nilCh_cs_only {X : WX} {bl : Loc} {r : NRec} (hd : objsDisj X.t)
    (hcs : ∀ c ∈ r.cs, ∃ B, X.t.bs !! bl = some B ∧ (B.ns !! c).isSome) :
    ∀ c ∈ r.cs, ∀ bl' B, X.t.bs !! bl' = some B → (B.ns !! c).isSome → bl' = bl := by
  intro c hc bl' B hB hs
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨B0, hB0, hs0⟩ := hcs c hc
  have := hd bl B0 hB0 c hs0 bl' B hB hne
  rw [this] at hs; cases hs

/-- **The frame of `n.children = nil`**: `n` and its old children touched. -/
theorem spFrame_nilCh {X : WX} {bl n : Loc} {r : NRec} (hn : X.node bl n = some r)
    (hcs : ∀ c ∈ r.cs, ∀ bl' B, X.t.bs !! bl' = some B → (B.ns !! c).isSome → bl' = bl) :
    spFrame X (X.nilCh bl n r) bl (n :: r.cs) := by
  obtain ⟨B, hB, hr⟩ := node_bs_of hn
  rw [nilCh_eq hB]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, meta_with_pgid_self _, Nat.le_refl _, fun _ _ h => h, fun _ _ h => h,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro bl' hne B0 hB0
    refine ⟨B0, ?_, bktSim_refl B0, fun _ => optRel_nodeSim_refl _⟩
    show (X.t.bs.insert bl _) !! bl' = some B0
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hB0
  · intro bl' hne h0
    show (X.t.bs.insert bl _) !! bl' = none
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact h0
  · intro B0 hB0
    rw [hB] at hB0; cases hB0
    refine ⟨_, GMap.lookup_insert _ _ _, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun l' hl' => ?_⟩
    have hne : n ≠ l' := fun e => hl' (by rw [e]; exact List.mem_cons_self)
    simp only
    rw [GMap.lookup_insert_ne _ _ hne]
    exact optRel_nodeSim_refl _
  · intro l bl' B0 hB0 hs hl
    have := killL_live X r.cs l
    unfold WX.killL at this
    rw [this]
    refine ⟨fun h => h.1, fun h => ⟨h, fun hm => ?_⟩⟩
    have e := hcs l hm bl' B0 hB0 hs
    exact hl e (List.mem_cons_of_mem _ hm)
  · exact fun y hy => by have := nilCh_objs_isSome hn hy; rwa [nilCh_eq hB] at this
  · intro bl' B0 B' l' r0 r' hB0 hB' hr0 hr' hT _ hv
    change (X.t.bs.insert bl _) !! bl' = some B' at hB'
    by_cases hb : bl = bl'
    · subst hb
      rw [hB] at hB0; cases hB0
      have hne : n ≠ l' := fun e => hT rfl (by rw [e]; exact List.mem_cons_self)
      rw [GMap.lookup_insert] at hB'; cases hB'
      simp only at hr'
      rw [GMap.lookup_insert_ne _ _ hne, hr0] at hr'; cases hr'; exact hv
    · rw [GMap.lookup_insert_ne _ _ hb, hB0] at hB'; cases hB'
      rw [hr0] at hr'; cases hr'; exact hv

/-- A location that is no object after a frame was none before. -/
theorem spFrame_objs_none {X X' : WX} {bl : Loc} {T : List Loc} (hfr : spFrame X X' bl T)
    {l : Loc} (h : X'.t.objs !! l = none) : X.t.objs !! l = none := by
  cases e : X.t.objs !! l with
  | none => rfl
  | some _ =>
    have := hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l (by rw [e]; rfl)
    rw [h] at this; cases this

end lemmas

end Spill

end bbolt
end EtcdGrove
end Perennial
