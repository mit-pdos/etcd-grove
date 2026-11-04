/-
`node.spill`'s split (U9v, `notes/bbolt-proof-plan.md`; pure): **nodes put into a bucket**
(`splitX`): some of bucket `bl`'s records replaced (`psOld`) and fresh nodes added, live
(`psNew`), what `n.split` does to the records; its lookups and its `spFrame`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitDefs
public import Proof.go_etcd_io.bbolt.Spill.StepComp
public import Proof.go_etcd_io.bbolt.Write.Heap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section put
variable [GooseExts]

/-- The records `ps` put into a node map. -/
def nsIns (ns : GMap Loc NRec) (ps : List (Loc × NRec)) : GMap Loc NRec :=
  ps.foldl (fun m p => m.insert p.1 p.2) ns

/-- The locations of `ps` added to a live set. -/
def lvIns (lv : GMap Loc Unit) (ps : List (Loc × NRec)) : GMap Loc Unit :=
  ps.foldl (fun m p => m.insert p.1 ()) lv

/-- **`X` with bucket `bl`'s records `psOld ++ psNew` put** (its record `B` before), the fresh
nodes `psNew` live. -/
def splitX (X : WX) (bl : Loc) (B : BRec) (psOld psNew : List (Loc × NRec)) : WX :=
  { X with t := { X.t with bs := X.t.bs.insert bl { B with ns := nsIns B.ns (psOld ++ psNew) } },
           live := lvIns X.live psNew }

theorem nsIns_append (ns : GMap Loc NRec) (a b : List (Loc × NRec)) :
    nsIns ns (a ++ b) = nsIns (nsIns ns a) b := by
  unfold nsIns; rw [List.foldl_append]

theorem nsIns_out (ns : GMap Loc NRec) (ps : List (Loc × NRec)) (l : Loc)
    (h : l ∉ ps.map (·.1)) : nsIns ns ps !! l = ns !! l := by
  induction ps generalizing ns with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    show nsIns (ns.insert p.1 p.2) ps !! l = _
    rw [ih _ h.2, GMap.lookup_insert_ne _ _ (Ne.symm h.1)]

theorem nsIns_in (ns : GMap Loc NRec) (ps : List (Loc × NRec)) (hnd : (ps.map (·.1)).Nodup)
    (p : Loc × NRec) (hp : p ∈ ps) : nsIns ns ps !! p.1 = some p.2 := by
  induction ps generalizing ns with
  | nil => cases hp
  | cons q ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    show nsIns (ns.insert q.1 q.2) ps !! p.1 = _
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [nsIns_out _ _ _ hnd.1, GMap.lookup_insert]
    · exact ih _ hnd.2 hp

theorem nsIns_isSome (ns : GMap Loc NRec) (ps : List (Loc × NRec)) (l : Loc)
    (h : (ns !! l).isSome) : (nsIns ns ps !! l).isSome := by
  induction ps generalizing ns with
  | nil => exact h
  | cons p ps ih =>
    show (nsIns (ns.insert p.1 p.2) ps !! l).isSome
    apply ih
    by_cases e : p.1 = l
    · subst e; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ e]; exact h

theorem lvIns_mem (lv : GMap Loc Unit) (ps : List (Loc × NRec)) (l : Loc) :
    l ∈ lvIns lv ps ↔ l ∈ lv ∨ l ∈ ps.map (·.1) := by
  induction ps generalizing lv with
  | nil => simp [lvIns]
  | cons p ps ih =>
    show l ∈ lvIns (lv.insert p.1 ()) ps ↔ _
    rw [ih]
    simp only [GMap.mem_iff, List.map_cons, List.mem_cons]
    by_cases e : p.1 = l
    · subst e; simp
    · rw [GMap.lookup_insert_ne _ _ e]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact absurd h.symm e
        · exact Or.inr h

section facts
variable {X : WX} {bl : Loc} {B : BRec} {psOld psNew : List (Loc × NRec)}

theorem splitX_bs (X : WX) (bl : Loc) (B : BRec) (psOld psNew : List (Loc × NRec)) :
    (splitX X bl B psOld psNew).t.bs !! bl =
      some { B with ns := nsIns B.ns (psOld ++ psNew) } :=
  GMap.lookup_insert _ _ _

theorem splitX_bs_ne (X : WX) (bl : Loc) (B : BRec) (psOld psNew : List (Loc × NRec)) (c : Loc)
    (h : c ≠ bl) : (splitX X bl B psOld psNew).t.bs !! c = X.t.bs !! c :=
  GMap.lookup_insert_ne _ _ (Ne.symm h)

/-- A put record, looked up. -/
theorem splitX_node (hnd : ((psOld ++ psNew).map (·.1)).Nodup) (p : Loc × NRec)
    (hp : p ∈ psOld ++ psNew) : (splitX X bl B psOld psNew).node bl p.1 = some p.2 := by
  unfold WX.node; rw [splitX_bs]
  exact nsIns_in _ _ hnd p hp

theorem splitX_live (l : Loc) :
    l ∈ (splitX X bl B psOld psNew).live ↔ l ∈ X.live ∨ l ∈ psNew.map (·.1) :=
  lvIns_mem _ _ _

/-- **The frame of the put**: the touched nodes `T` include the put ones. -/
theorem splitX_frame (hb : X.t.bs !! bl = some B) (T : List Loc)
    (hT : ∀ p ∈ psOld ++ psNew, p.1 ∈ T) :
    spFrame X (splitX X bl B psOld psNew) bl T := by
  have hout : ∀ l, l ∉ T → nsIns B.ns (psOld ++ psNew) !! l = B.ns !! l := by
    intro l hl
    apply nsIns_out
    intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    exact hl (hT p hp)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, fun _ _ h => h, fun _ _ h => h,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro bl' hne B0 hB0
    refine ⟨B0, ?_, bktSim_refl B0, fun _ => optRel_nodeSim_refl _⟩
    rw [splitX_bs_ne _ _ _ _ _ _ hne]; exact hB0
  · intro bl' hne h0
    rw [splitX_bs_ne _ _ _ _ _ _ hne]; exact h0
  · intro B0 hB0
    rw [hb] at hB0; cases hB0
    refine ⟨_, splitX_bs _ _ _ _ _, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun l hl => ?_⟩
    simp only
    rw [hout l hl]; exact optRel_nodeSim_refl _
  · intro l hl _
    rw [splitX_live]
    constructor
    · rintro (h | h)
      · exact h
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
        exact absurd (hT p (List.mem_append_right _ hp)) hl
    · exact Or.inl
  · intro l hl
    by_cases hk : ∃ c C rk, X.t.bs !! c = some C ∧ C.ns !! l = some rk
    · obtain ⟨c, C, rk, hC, hrk⟩ := hk
      by_cases hc : c = bl
      · subst hc
        rw [hb] at hC; cases hC
        exact Write.objs_isSome_node _ c _ l (splitX_bs _ _ _ _ _)
          (nsIns_isSome _ _ _ (by rw [hrk]; rfl))
      · exact Write.objs_isSome_node _ c C l (by rw [splitX_bs_ne _ _ _ _ _ _ hc]; exact hC)
          (by rw [hrk]; rfl)
    · have hno : ∀ c C, X.t.bs !! c = some C → C.ns !! l = none := by
        intro c C hC
        cases h : C.ns !! l with
        | none => rfl
        | some rk => exact absurd ⟨c, C, rk, hC, h⟩ hk
      by_cases hk' : ∃ c C, (splitX X bl B psOld psNew).t.bs !! c = some C ∧ (C.ns !! l).isSome
      · obtain ⟨c, C, hC, hs⟩ := hk'
        exact Write.objs_isSome_node _ c C l hC hs
      · have hno' : ∀ c C, (splitX X bl B psOld psNew).t.bs !! c = some C → C.ns !! l = none := by
          intro c C hC
          cases h : C.ns !! l with
          | none => rfl
          | some rk => exact absurd ⟨c, C, hC, by rw [h]; rfl⟩ hk'
        rw [objs_other _ l hno']
        rw [objs_other _ l hno] at hl
        exact hl
  · intro bl' B0 B' l r r' hB0 hB' hr hr' hTl hv
    by_cases hc : bl' = bl
    · subst hc
      rw [hb] at hB0; cases hB0
      rw [splitX_bs] at hB'; cases hB'
      simp only at hr'
      rw [hout l (hTl rfl), hr] at hr'; cases hr'; exact hv
    · rw [splitX_bs_ne _ _ _ _ _ _ hc, hB0] at hB'; cases hB'
      rw [hr] at hr'; cases hr'; exact hv

end facts

end put

end Spill

end bbolt
end EtcdGrove
end Perennial
