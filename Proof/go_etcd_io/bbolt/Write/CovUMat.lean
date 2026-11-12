/-
**`covU` and `flViewU` under materializations** (U7i, `notes/bbolt-proof-plan.md`; batch 20's
`covU_nodeAdded`, the review's U1: `Put`/`Delete` keep the exclusive part's `flViewU` across
`Cursor.node`): a materialization keeps every bucket's positions and, at each of them, its extent
(`nodeAdded_posParts`, the case split of `Write/FlView.flView_nodeAdded'`), so `covU` (by
`covU_congr'`, `covU_congr` with the extents compared on the positions only: an inline bucket's
extents at other ids change) and `flViewU` (`flViewU_nodeAdded`); `flViewU_matGrow` by induction,
as `wtxData_matGrow`.
-/
module

public import Proof.go_etcd_io.bbolt.Write.CovU
public import Proof.go_etcd_io.bbolt.Write.MatGrow

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section covumat
variable [GooseExts]

/-- **`covU` from its parts**, the extents compared at the positions only. -/
theorem covU_congr' (X X' : WX) (hv : X'.v = X.v) (hroot : rootEnts X' = rootEnts X)
    (hbkt : ∀ n, bktLoc X' n = bktLoc X n)
    (hbs : ∀ c, (X'.t.bs !! c).isSome = (X.t.bs !! c).isSome)
    (hpos : ∀ c, (X.t.bs !! c).isSome → X'.positions c = X.positions c)
    (hpe : ∀ c pid, (X.t.bs !! c).isSome → pid ∈ X.positions c →
      X'.posExtent c pid = X.posExtent c pid)
    (h : covU X) : covU X' := by
  have hne : ∀ c, (X'.t.bs !! c ≠ none ↔ X.t.bs !! c ≠ none) := by
    intro c; have := hbs c
    cases h1 : X'.t.bs !! c <;> cases h2 : X.t.bs !! c <;> simp_all
  have hsome : ∀ c, X.t.bs !! c ≠ none → (X.t.bs !! c).isSome := by
    intro c hc; cases e : X.t.bs !! c <;> simp_all
  have hcw : ∀ s c, coverW X' s c → coverW X s c := by
    intro s c hc
    cases c with
    | pos bl pid =>
      obtain ⟨h1, h2, e, h3, h4⟩ := hc
      have h1' := (hne bl).1 h1
      have h2' : pid ∈ X.positions bl := by rw [← hpos bl (hsome bl h1')]; exact h2
      refine ⟨h1', h2', e, ?_, h4⟩
      rw [← hpe bl pid (hsome bl h1') h2']; exact h3
    | bkt n =>
      obtain ⟨v, h1, h2, h3⟩ := hc
      refine ⟨v, ?_, ?_, ?_⟩
      · rw [← hroot]; exact h1
      · rw [← hbkt]; exact h2
      · rw [← hv]; exact h3
  intro s c1 c2 h1 h2
  exact h s c1 c2 (hcw s c1 h1) (hcw s c2 h2)

/-- **A materialization keeps every bucket's positions, and their extents.** -/
theorem nodeAdded_posParts (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (hok : wOK X) (h : nodeAdded X X' bl l pgid parent) (hpos : matPos X bl pgid parent)
    (c : Loc) :
    X'.positions c = X.positions c ∧
      ∀ pid ∈ X.positions c, X'.posExtent c pid = X.posExtent c pid := by
  have hf := wOK_matFresh X X' bl l pgid parent hok h hpos
  obtain ⟨-, -, -, hvv, hfuel, hrp, -, -⟩ :=
    nodeAdded_facts X X' bl l pgid parent h hf (wOK_inlineLeaf X bl pgid hok)
  have hlt := ltree_nodeAdded' X X' bl l pgid parent h hf
  obtain ⟨B, pa, pg, r, ns', bv', hB, hpg, hnm, hl0, hlo, hrb, hrp0, hrid, hrleaf, hru, hrs, hrcs,
    hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase, hX'⟩ := h
  obtain ⟨hfnm, hfroot⟩ := hf B hB
  have hns_pg : ∀ l0, l0 ≠ l → (ns' !! l0).map (fun r => r.nv.pgid') = (B.ns !! l0).map (fun r => r.nv.pgid') := by
    intro l0 hl0'
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrpp, -, -, -, -, -, -, -, hnv, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hl0')]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hl0')]
      by_cases hp : parent = l0
      · subst hp; rw [GMap.lookup_insert, hrpp]; simp only [Option.map_some, Option.some.injEq]
        rw [hnv]
      · rw [GMap.lookup_insert_ne _ _ hp]
  have hB' : X'.t.bs !! bl = some { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } := by
    rw [hX']; simp
  have hbsc : ∀ c, c ≠ bl → X'.t.bs !! c = X.t.bs !! c := by
    intro c hc; rw [hX']; simp [Ne.symm hc]
  by_cases hcb : c = bl
  · subst hcb
    by_cases hin : B.ib.root' = W64 0
    · -- an inline bucket: its only position is `0`
      have hrn := hfroot hin
      have hrp0' : X.rootPid c = W64 0 := by simp [WX.rootPid, hB, hin]
      have hX0 := hlt c (W64 0) (fun _ _ _ _ => rfl)
      have hpg0 : pgid = W64 0 := by
        unfold wpageAt at hpg; rw [if_pos hin] at hpg; split at hpg
        · assumption
        · simp at hpg
      subst hpg0
      have hshp0 : shp (ltree X c (W64 0)) = none := by
        have hl := wOK_inlineLeaf X c (W64 0) hok B pa pg hB hin hrn hpg
        have hd : decide (pageFlags pg = leafPageFlag) = true := by simp [hl]
        unfold ltree resolve
        rw [hB]
        simp only [hin, ↓reduceIte, hrn]
        rw [hpg]
        simp only [Option.map_some, hd, shp]
      have hshp0' : shp (ltree X' c (W64 0)) = none := by
        rw [shp_of_ldat _ _ hX0, hshp0]
      have hpos' : ∀ (L : LTree) n, shp (L c (W64 0)) = none →
          lposF L c n (W64 0) = if n = 0 then [] else [W64 0] := by
        intro L n hs
        cases n with
        | zero => rfl
        | succ n =>
          simp only [lposF, Nat.add_one_ne_zero, ↓reduceIte, List.cons.injEq, true_and]
          cases hL : L c (W64 0) with
          | none => rfl
          | some y =>
            obtain ⟨y1, y2⟩ := y
            rw [hL] at hs
            cases y1 <;> simp_all [shp]
      have hpX : X.positions c = if X.fuel = 0 then [] else [W64 0] := by
        unfold WX.positions; rw [hrp0', hpos' _ _ hshp0]
      have hpX' : X'.positions c = if X.fuel = 0 then [] else [W64 0] := by
        unfold WX.positions; rw [hfuel, hrp, hrp0', hpos' _ _ hshp0']
      refine ⟨by rw [hpX, hpX'], fun pid hpid => ?_⟩
      have hpid0 : pid = W64 0 := by
        rw [hpX] at hpid; split at hpid
        · cases hpid
        · simpa using hpid
      subst hpid0
      rw [posExtent_eq X X' c (W64 0) hvv]
      rw [hB', hB]
      simp only [Option.map_some, Option.some.injEq]
      unfold posIdOf resolve
      simp only [hin, ↓reduceIte, hrn]
      rcases hcase with ⟨-, hbv, hns⟩ | ⟨-, hbv, -⟩
      · rw [hbv]
        simp only [hl0, ↓reduceIte]
        have : ns' !! l = some r := by rw [hns]; simp
        rw [this]
        simp only [Option.map_some, Option.getD_some, hrid]
        have hpgB : pg = B.ipg := by
          unfold wpageAt at hpg; simp only [hin, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at hpg
          exact hpg.2.symm
        obtain ⟨-, -, hg, -⟩ := (wOK_bktClean X hok c B hB).1 hin hrn
        rw [hpgB]
        apply BitVec.eq_of_toNat_eq
        exact hg.1
      · rw [hbv]; simp only [hrn, ↓reduceIte]
    · -- a file bucket: every position
      have hshape : ∀ pid, shp (ltree X' c pid) = shp (ltree X c pid) := fun pid =>
        shp_of_ldat _ _ (hlt c pid (fun _ B1 hB1 hin1 => by rw [hB] at hB1; cases hB1; exact absurd hin1 hin))
      have hpos2 : X'.positions c = X.positions c := by
        unfold WX.positions; rw [hfuel, hrp]; exact lposF_congr _ _ c hshape _ _
      refine ⟨hpos2, fun pid _ => ?_⟩
      apply posExtent_eq X X' c pid hvv
      rw [hB', hB]
      simp only [Option.map_some, Option.some.injEq]
      unfold posIdOf resolve
      simp only [hin, ↓reduceIte]
      by_cases hp : pid = pgid
      · subst hp
        rw [GMap.lookup_insert, hnm]
        simp only
        have : ns' !! l = some r := by
          rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', -, -, -, -, -, -, -, -, -, rfl⟩ <;> simp
        rw [this]
        simp only [Option.map_some, Option.getD_some, hrid]
        exact nodeAdded_pgid X hok c B pid parent pa pg hB hpos hpg hin
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hp)]
        cases hc : B.nm !! pid with
        | none => rfl
        | some l0 =>
          simp only
          have : l0 ≠ l := by intro e; subst e; exact hfnm pid hc
          rw [hns_pg l0 this]
  · have hshape : ∀ pid, shp (ltree X' c pid) = shp (ltree X c pid) := fun pid =>
      shp_of_ldat _ _ (hlt c pid (fun h => absurd h hcb))
    have hpos2 : X'.positions c = X.positions c := by
      unfold WX.positions; rw [hfuel, hrp]; exact lposF_congr _ _ c hshape _ _
    refine ⟨hpos2, fun pid _ => ?_⟩
    apply posExtent_eq X X' c pid hvv
    rw [hbsc c hcb]

/-- **`covU_nodeAdded`**: a materialization keeps `covU`. -/
theorem covU_nodeAdded (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (hok : wOK X) (h : nodeAdded X X' bl l pgid parent) (hpos : matPos X bl pgid parent)
    (hv : covU X) : covU X' := by
  have hf := wOK_matFresh X X' bl l pgid parent hok h hpos
  obtain ⟨hroot, hbkt, -, hvv, -, -, -, hbs⟩ :=
    nodeAdded_facts X X' bl l pgid parent h hf (wOK_inlineLeaf X bl pgid hok)
  exact covU_congr' X X' hvv hroot hbkt hbs
    (fun c _ => (nodeAdded_posParts X X' bl l pgid parent hok h hpos c).1)
    (fun c pid _ hp => (nodeAdded_posParts X X' bl l pgid parent hok h hpos c).2 pid hp) hv

/-- **A materialization keeps `flViewU`.** -/
theorem flViewU_nodeAdded (X X' : WX) (fl : FLPg) (bl l : Loc) (pgid : w64) (parent : Loc)
    (hok : wOK X) (h : nodeAdded X X' bl l pgid parent) (hpos : matPos X bl pgid parent)
    (hv : flViewU X fl) : flViewU X' fl := by
  have hf := wOK_matFresh X X' bl l pgid parent hok h hpos
  obtain ⟨-, -, -, hvv, -, -, -, -⟩ :=
    nodeAdded_facts X X' bl l pgid parent h hf (wOK_inlineLeaf X bl pgid hok)
  refine ⟨flView_nodeAdded' X X' fl bl l pgid parent hv.1 hok h hpos,
    covU_nodeAdded X X' bl l pgid parent hok h hpos hv.2.1, ?_, hv.2.2.2⟩
  rw [hvv]; exact hv.2.2.1

/-- **`flViewU_matGrow`**: materializations keep `flViewU` (from `wOK` at the start). -/
theorem flViewU_matGrow (X X' : WX) (fl : FLPg) (bl : Loc) (hok : wOK X) (h : matGrow X X' bl)
    (hv : flViewU X fl) : flViewU X' fl := by
  revert hok hv
  induction h with
  | refl => intro _ hv; exact hv
  | step X Y Z bl l pgid parent hadd hpos _ ih =>
    intro hok hv
    exact ih (wOK_nodeAdded X Y bl l pgid parent hok hadd hpos)
      (flViewU_nodeAdded X Y fl bl l pgid parent hok hadd hpos hv)

end covumat

end Write

end bbolt
end EtcdGrove
end Perennial
