/-
U7's (`notes/bbolt-proof-plan.md`) `flView` lemmas: the logical tree's cover (`lCovers`) depends
only on the tree's shape (branch positions and their children), the nodes' page ids, the root
bucket's entries and the opened buckets; a leaf's new entries (`flView_withWs'`) and a
materialization (`flView_nodeAdded'`) keep them.
-/
module

public import Proof.go_etcd_io.bbolt.Write.Mat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section flview
variable [GooseExts]

/-- What a walk of positions reads of a position: a branch's children. -/
def shp (x : Option (Bool × List WEntry)) : Option (List w64) :=
  match x with
  | some (false, ws) => some (ws.map WEntry.pgid)
  | _ => none

theorem shp_of_ldat (x y : Option (Bool × List WEntry)) (h : ldat x = ldat y) : shp x = shp y := by
  cases x with
  | none => cases y with
    | none => rfl
    | some _ => simp [ldat] at h
  | some a => cases y with
    | none => simp [ldat] at h
    | some b =>
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only [ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have : a2.map WEntry.pgid = b2.map WEntry.pgid := by
        have := congrArg (List.map fun d => d.2.1) h2
        simpa [List.map_map, Function.comp_def, wDat] using this
      cases a1 <;> simp [shp, this]

theorem flatMap_pgid_congr (f : w64 → List w64) (ws1 ws2 : List WEntry)
    (h : ws1.map WEntry.pgid = ws2.map WEntry.pgid) :
    ws1.flatMap (fun w => f w.pgid) = ws2.flatMap (fun w => f w.pgid) := by
  induction ws1 generalizing ws2 with
  | nil => cases ws2 <;> simp_all
  | cons a xs ih =>
    cases ws2 with
    | nil => simp at h
    | cons b ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.flatMap_cons, h.1, ih ys h.2]

/-- The positions of a walk depend only on the shape. -/
theorem lposF_congr (L L' : LTree) (bl : Loc) (h : ∀ pid, shp (L' bl pid) = shp (L bl pid)) :
    ∀ n pid, lposF L' bl n pid = lposF L bl n pid
  | 0, _ => rfl
  | n + 1, pid => by
    have hp := h pid
    simp only [lposF]
    congr 1
    have ih := lposF_congr L L' bl h n
    cases h1 : L bl pid with
    | none =>
      rw [h1] at hp
      cases h2 : L' bl pid with
      | none => rfl
      | some y =>
        obtain ⟨y1, y2⟩ := y
        rw [h2] at hp
        cases y1 <;> simp_all [shp]
    | some x =>
      obtain ⟨x1, x2⟩ := x
      rw [h1] at hp
      cases h2 : L' bl pid with
      | none => rw [h2] at hp; cases x1 <;> simp_all [shp]
      | some y =>
        obtain ⟨y1, y2⟩ := y
        rw [h2] at hp
        cases x1 <;> cases y1 <;> simp only [shp, Option.some.injEq, reduceCtorEq] at hp ⊢
        · simp only [funext ih]
          exact flatMap_pgid_congr _ _ _ hp

/-- **The cover from its parts.** -/
theorem lCovers_congr (X X' : WX) (hv : X'.v = X.v) (hroot : rootEnts X' = rootEnts X)
    (hbkt : ∀ n, bktLoc X' n = bktLoc X n)
    (hbs : ∀ c, (X'.t.bs !! c).isSome = (X.t.bs !! c).isSome)
    (hext : ∀ c, (X.t.bs !! c).isSome → X'.extents c = X.extents c) :
    ∀ s, lCovers X' s ↔ lCovers X s := by
  intro s
  have hne : ∀ c, (X'.t.bs !! c ≠ none ↔ X.t.bs !! c ≠ none) := by
    intro c; have := hbs c
    cases h1 : X'.t.bs !! c <;> cases h2 : X.t.bs !! c <;> simp_all
  unfold lCovers
  rw [hroot, hv]
  simp only [hbkt]
  constructor
  · rintro (⟨c, e, hc, he, h1⟩ | h)
    · have hc' := (hne c).1 hc
      rw [hext c (by cases h : X.t.bs !! c <;> simp_all)] at he
      exact Or.inl ⟨c, e, hc', he, h1⟩
    · exact Or.inr h
  · rintro (⟨c, e, hc, he, h1⟩ | h)
    · have hc' := (hne c).2 hc
      rw [← hext c (by cases h : X.t.bs !! c <;> simp_all)] at he
      exact Or.inl ⟨c, e, hc', he, h1⟩
    · exact Or.inr h

theorem flView_congr (X X' : WX) (fl : FLPg) (hv : X'.v = X.v)
    (hcov : ∀ s, lCovers X' s ↔ lCovers X s) (h : flView X fl) : flView X' fl := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun s hs => ?_, by rw [hv]; exact h2, h3, h4⟩
  rw [hv] at hs
  rw [hcov]; exact h1 s hs

/-- A bucket with node `l`'s entries `ws'` (`WX.withWs`'s bucket record). -/
def brecWithWs (B : BRec) (l : Loc) (ws' : List WEntry) : BRec :=
  { B with ns := match B.ns !! l with
    | none => B.ns
    | some r => B.ns.insert l { r with ws := ws' } }

theorem withWs_bs_at (X : WX) (bl l : Loc) (ws' : List WEntry) (c : Loc) :
    (X.withWs bl l ws').t.bs !! c =
      (X.t.bs !! c).map fun B => if c = bl then brecWithWs B l ws' else B := by
  unfold WX.withWs brecWithWs
  simp only
  cases hB : X.t.bs !! bl with
  | none =>
    by_cases hc : c = bl
    · subst hc; simp [hB]
    · simp [hc]
  | some B =>
    by_cases hc : c = bl
    · subst hc; simp only [hB, GMap.lookup_insert, Option.map_some, ↓reduceIte]
      congr 2
    · simp [Ne.symm hc, hc]

theorem brecWithWs_ns (B : BRec) (l : Loc) (ws' : List WEntry) (l0 : Loc) :
    (brecWithWs B l ws').ns !! l0 = (B.ns !! l0).map fun r => if l0 = l then { r with ws := ws' } else r := by
  unfold brecWithWs
  simp only
  cases hl : B.ns !! l with
  | none =>
    by_cases h : l0 = l
    · subst h; simp [hl]
    · cases B.ns !! l0 <;> simp [h]
  | some r =>
    by_cases h : l0 = l
    · subst h; simp [hl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]; cases B.ns !! l0 <;> simp [h]

/-- `flView_withWs` (`Model/WOps`). -/
theorem flView_withWs' (X : WX) (fl : FLPg) (bl l : Loc) (ws' : List WEntry) (hv : flView X fl)
    (hleaf : ∀ B r, X.t.bs !! bl = some B → B.ns !! l = some r → r.nv.isLeaf' = true)
    (hroot : bl ≠ X.rl) : flView (X.withWs bl l ws') fl := by
  refine flView_congr X (X.withWs bl l ws') fl rfl ?_ hv
  have hvv : (X.withWs bl l ws').v = X.v := rfl
  have hbsc : ∀ c, c ≠ bl → (X.withWs bl l ws').t.bs !! c = X.t.bs !! c := by
    intro c hc; rw [withWs_bs_at]; cases X.t.bs !! c <;> simp [hc]
  have hrl : (X.withWs bl l ws').t.bs !! X.rl = X.t.bs !! X.rl := hbsc _ (Ne.symm hroot)
  have hfuel : (X.withWs bl l ws').fuel = X.fuel := by
    unfold WX.fuel WX.withWs; simp only
    cases h : X.t.bs !! bl with
    | none => rfl
    | some B => rw [GMap.map_size_insert_Some _ _ _ _ h]
  have hlt_rl : ∀ pid, ltree (X.withWs bl l ws') X.rl pid = ltree X X.rl pid := by
    intro pid; simp only [ltree, hrl]; rfl
  have hroots : rootEnts (X.withWs bl l ws') = rootEnts X := by
    unfold rootEnts WX.leaves WX.rootPid
    simp only [show (X.withWs bl l ws').rl = X.rl from rfl]
    rw [hfuel, hrl]
    have e : ∀ n pid, lleaves (ltree (X.withWs bl l ws')) X.rl n pid = lleaves (ltree X) X.rl n pid := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih => intro pid; simp only [lleaves, hlt_rl, ih]
    rw [e]
  have hbkt : ∀ n, bktLoc (X.withWs bl l ws') n = bktLoc X n := by
    intro n; unfold bktLoc; rw [show (X.withWs bl l ws').rl = X.rl from rfl, hrl]
  refine lCovers_congr X (X.withWs bl l ws') rfl hroots hbkt ?_ ?_
  · intro c; rw [withWs_bs_at]; cases X.t.bs !! c <;> simp
  · intro c _
    have hshape : ∀ pid, shp (ltree (X.withWs bl l ws') c pid) = shp (ltree X c pid) := by
      intro pid
      by_cases hc : c = bl
      · subst hc
        unfold ltree
        rw [withWs_bs_at, hvv]
        cases hB : X.t.bs !! c with
        | none => rfl
        | some B =>
          simp only [Option.map_some, ↓reduceIte]
          rw [show resolve (brecWithWs B l ws') pid = resolve B pid from rfl,
            show wpageAt X.v (brecWithWs B l ws') pid = wpageAt X.v B pid from rfl]
          cases hr : resolve B pid with
          | none => rfl
          | some l0 =>
            simp only
            rw [brecWithWs_ns]
            cases hrl0 : B.ns !! l0 with
            | none => rfl
            | some r0 =>
              by_cases hl0 : l0 = l
              · subst hl0
                have := hleaf B r0 hB hrl0
                simp [shp, this]
              · simp [hl0]
      · unfold ltree; rw [hbsc c hc, hvv]
    have hpos : (X.withWs bl l ws').positions c = X.positions c := by
      unfold WX.positions
      have hrp : (X.withWs bl l ws').rootPid c = X.rootPid c := by
        unfold WX.rootPid; rw [withWs_bs_at]
        cases X.t.bs !! c <;> simp only [Option.map_none, Option.map_some]
        split <;> rfl
      rw [hfuel, hrp]
      exact lposF_congr _ _ c hshape _ _
    unfold WX.extents
    rw [hpos]
    congr 1
    funext pid
    unfold WX.posExtent
    rw [withWs_bs_at, hvv]
    cases hB : X.t.bs !! c with
    | none => rfl
    | some B =>
      simp only [Option.map_some]
      by_cases hc : c = bl
      · simp only [hc, ↓reduceIte]
        rw [show resolve (brecWithWs B l ws') pid = resolve B pid from rfl]
        cases hr : resolve B pid with
        | none => rfl
        | some l0 =>
          simp only
          rw [brecWithWs_ns]
          cases B.ns !! l0 with
          | none => rfl
          | some r0 => by_cases hl0 : l0 = l <;> simp [hl0]
      · simp only [hc, ↓reduceIte]

/-- The page id a position's extent is of (`WX.posExtent`'s `id`). -/
def posIdOf (B : BRec) (pid : w64) : w64 :=
  match resolve B pid with
  | some l => ((B.ns !! l).map fun r => r.nv.pgid').getD 0
  | none => pid


theorem posExtent_def (X : WX) (c : Loc) (pid : w64) :
    X.posExtent c pid = match X.t.bs !! c with
      | none => none
      | some B => if posIdOf B pid = W64 0 then none
        else (X.v.pages !! (posIdOf B pid).toNat).map fun pg => (posIdOf B pid, 1 + pageOverflow pg) := by
  unfold WX.posExtent posIdOf; rfl

theorem posExtent_eq (X X' : WX) (c : Loc) (pid : w64) (hv : X'.v = X.v)
    (h : (X'.t.bs !! c).map (fun B => posIdOf B pid) = (X.t.bs !! c).map (fun B => posIdOf B pid)) :
    X'.posExtent c pid = X.posExtent c pid := by
  rw [posExtent_def, posExtent_def, hv]
  cases h1 : X'.t.bs !! c with
  | none =>
    cases h2 : X.t.bs !! c with
    | none => rfl
    | some B => rw [h1, h2] at h; simp at h
  | some B' =>
    cases h2 : X.t.bs !! c with
    | none => rw [h1, h2] at h; simp at h
    | some B =>
      rw [h1, h2] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [h]

/-- The page a materialization reads from a file bucket has the position's id (`treeWF`). -/
theorem nodeAdded_pgid (X : WX) (hok : wOK X) (bl : Loc) (B : BRec) (pgid : w64) (parent : Loc)
    (pa : Loc) (pg : List w8) (hB : X.t.bs !! bl = some B) (hpos : matPos X bl pgid parent)
    (hpg : wpageAt X.v B pgid = some (pa, pg)) (hin : B.ib.root' ≠ W64 0) :
    (pageHdr pg).id' = pgid := by
  have hc := wOK_bktClean X hok bl B hB
  have hpg' : X.v.pages !! pgid.toNat = some pg := by
    unfold wpageAt at hpg; rw [if_neg hin] at hpg
    cases h : X.v.pages !! pgid.toNat with
    | none => rw [h] at hpg; cases hpg
    | some pg' => rw [h] at hpg; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpg
                  rw [hpg.2]
  have htw : treeWF X.v.pages X.t.mv.pgid'.toNat pgid.toNat := by
    obtain ⟨B1, hB1, hp⟩ := hpos
    rw [hB] at hB1; cases hB1
    rcases hp with ⟨-, hrn, rfl⟩ | ⟨i, r, w, hr, hleaf, hw, hwp, hnm⟩
    · exact (hc.2.1 hin).2 hrn
    · have hn := hc.2.2.2.2.2.2.2.1 parent r hr
      have hb := hn.2.2.2.2.2.2.2.2.2.2.2.2.1 hleaf
      have := (hb.2.2 w (List.mem_of_getElem? hw)).2.2
      rw [hwp] at this; exact this hnm
  cases htw with
  | page root pg2 h2 hlt hp hid hlen hptw =>
    rw [hpg'] at hp; cases hp
    apply BitVec.eq_of_toNat_eq
    exact hid

/-- `flView_nodeAdded` (`Model/WOps`). -/
theorem flView_nodeAdded' (X X' : WX) (fl : FLPg) (bl l : Loc) (pgid : w64) (parent : Loc)
    (hv : flView X fl) (hok : wOK X) (h : nodeAdded X X' bl l pgid parent)
    (hpos : matPos X bl pgid parent) : flView X' fl := by
  have hf := wOK_matFresh X X' bl l pgid parent hok h hpos
  obtain ⟨hroot, hbkt, -, hvv, hfuel, hrp, -, hbs⟩ :=
    nodeAdded_facts X X' bl l pgid parent h hf (wOK_inlineLeaf X bl pgid hok)
  have hlt := ltree_nodeAdded' X X' bl l pgid parent h hf
  refine flView_congr X X' fl hvv ?_ hv
  refine lCovers_congr X X' hvv hroot hbkt hbs ?_
  intro c hcs
  obtain ⟨B, pa, pg, r, ns', bv', hB, hpg, hnm, hl0, hlo, hrb, hrp0, hrid, hrleaf, hru, hrs, hrcs,
    hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hcase, hX'⟩ := h
  obtain ⟨hfnm, hfroot⟩ := hf B hB
  -- the records of the other positions' nodes keep their page ids
  have hns_pg : ∀ l0, l0 ≠ l → (ns' !! l0).map (fun r => r.nv.pgid') = (B.ns !! l0).map (fun r => r.nv.pgid') := by
    intro l0 hl0'
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrpp, -, -, -, -, -, -, hnv, rfl⟩
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
      have hshp0 : shp (ltree X c (W64 0)) = none := by
        have hpg0 : pgid = W64 0 := by
          unfold wpageAt at hpg; rw [if_pos hin] at hpg; split at hpg
          · assumption
          · simp at hpg
        subst hpg0
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
      unfold WX.extents WX.positions
      rw [hfuel, hrp, hrp0', hpos' _ _ hshp0, hpos' _ _ hshp0']
      split
      · rfl
      · simp only [List.filterMap_cons, List.filterMap_nil]
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
          have hpg0 : pgid = W64 0 := by
            unfold wpageAt at hpg; rw [if_pos hin] at hpg; split at hpg
            · assumption
            · simp at hpg
          subst hpg0
          have hpgB : pg = B.ipg := by
            unfold wpageAt at hpg; simp only [hin, ↓reduceIte, Option.some.injEq,
              Prod.mk.injEq] at hpg
            exact hpg.2.symm
          obtain ⟨-, -, hg⟩ := (wOK_bktClean X hok c B hB).1 hin hrn
          rw [hpgB]
          apply BitVec.eq_of_toNat_eq
          exact hg.1
        · rw [hbv]; simp only [hrn, ↓reduceIte]
    · -- a file bucket: every position
      have hshape : ∀ pid, shp (ltree X' c pid) = shp (ltree X c pid) := fun pid =>
        shp_of_ldat _ _ (hlt c pid (fun _ B1 hB1 hin1 => by rw [hB] at hB1; cases hB1; exact absurd hin1 hin))
      have hpos2 : X'.positions c = X.positions c := by
        unfold WX.positions; rw [hfuel, hrp]; exact lposF_congr _ _ c hshape _ _
      unfold WX.extents
      rw [hpos2]
      congr 1
      funext pid
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
          rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', -, -, -, -, -, -, -, -, rfl⟩ <;> simp
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
    unfold WX.extents
    rw [hpos2]
    congr 1
    funext pid
    apply posExtent_eq X X' c pid hvv
    rw [hbsc c hcb]

end flview

end Write

end bbolt
end EtcdGrove
end Perennial
