/-
`derefStep` keeps what `derefRel` asks to be kept (U9b, `notes/bbolt-proof-plan.md`; pure): the
nodes by data, the logical tree by data, the writer's data; and the coverage contract
(`derefOK`) from the buckets' coverage.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.DerefModel
public import Proof.go_etcd_io.bbolt.Rebalance.Objs
public import Proof.go_etcd_io.bbolt.Inv.WtxHeap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rel
variable [GooseExts]

theorem derefStep_node {X X' : WX} (h : derefStep X X') (bl l : Loc) :
    (X'.node bl l).map (fun r => (r.ws.map wDat, r.key, r.nv.pgid', r.nv.isLeaf')) =
      (X.node bl l).map (fun r => (r.ws.map wDat, r.key, r.nv.pgid', r.nv.isLeaf')) := by
  unfold WX.node
  have hb := derefStep_bs h bl
  cases hB : X.t.bs !! bl with
  | none => rw [hB] at hb; rw [optRel_none_l hb]
  | some B =>
    rw [hB] at hb
    obtain ⟨B', hB', hs⟩ := optRel_some_l hb
    rw [hB']
    simp only [Option.bind_some]
    have hn := hs.2 l
    cases hr : B.ns !! l with
    | none => rw [hr] at hn; rw [optRel_none_l hn]
    | some r =>
      rw [hr] at hn
      obtain ⟨r', hr', hrs⟩ := optRel_some_l hn
      rw [hr']
      obtain ⟨hnv, -, hkey, -, -, hws⟩ := nodeStep_nv hrs
      simp only [Option.map_some, hws, hkey]
      rw [hnv]

/-- The bucket's view of a position (`resolve`, `wpageAt`) is kept by a step. -/
theorem bktStep_resolve {B B' : BRec} (h : bktStep B B') (pid : w64) :
    resolve B' pid = resolve B pid := by
  have hf := bktStep_fields h
  unfold resolve; rw [hf.1, hf.2.1, hf.2.2.1]

theorem bktStep_wpageAt {B B' : BRec} (h : bktStep B B') (v : View) (pid : w64) :
    wpageAt v B' pid = wpageAt v B pid := by
  have hf := bktStep_fields h
  unfold wpageAt; rw [hf.1, hf.2.1, hf.2.2.2.2.1]

/-- The logical tree, by data. -/
def ldat (o : Option (Bool × List WEntry)) : Option (Bool × List (w32 × w64 × List w8 × List w8)) :=
  o.map fun x => (x.1, x.2.map wDat)

theorem derefStep_ltree {X X' : WX} (h : derefStep X X') (bl : Loc) (pid : w64) :
    ldat (ltree X' bl pid) = ldat (ltree X bl pid) := by
  unfold ltree
  have hb := derefStep_bs h bl
  cases hB : X.t.bs !! bl with
  | none => rw [hB] at hb; rw [optRel_none_l hb]
  | some B =>
    rw [hB] at hb
    obtain ⟨B', hB', hs⟩ := optRel_some_l hb
    rw [hB']
    simp only
    rw [bktStep_resolve hs, bktStep_wpageAt hs, h.1]
    cases hres : resolve B pid with
    | none => rfl
    | some l =>
      simp only
      have hn := hs.2 l
      cases hr : B.ns !! l with
      | none => rw [hr] at hn; rw [optRel_none_l hn]
      | some r =>
        rw [hr] at hn
        obtain ⟨r', hr', hrs⟩ := optRel_some_l hn
        rw [hr']
        obtain ⟨hnv, -, -, -, -, hws⟩ := nodeStep_nv hrs
        simp only [ldat, Option.map_some, hws]
        rw [hnv]

theorem flatMap_pgid_map {β γ : Type} (F : β → γ) (G1 G2 : w64 → List β) (ws1 ws2 : List WEntry)
    (hpg : ws2.map WEntry.pgid = ws1.map WEntry.pgid) (hG : ∀ p, (G2 p).map F = (G1 p).map F) :
    (ws2.flatMap (fun w => G2 w.pgid)).map F = (ws1.flatMap (fun w => G1 w.pgid)).map F := by
  induction ws1 generalizing ws2 with
  | nil => cases ws2 <;> simp_all
  | cons w ws ih =>
    cases ws2 with
    | nil => simp at hpg
    | cons w2 ws2 =>
      simp only [List.map_cons, List.cons.injEq] at hpg
      simp only [List.flatMap_cons, List.map_append]
      rw [hpg.1, hG, ih _ hpg.2]

/-- The leaves, by data, of two logical trees equal by data. -/
theorem lleaves_ldat (L1 L2 : LTree) (hL : ∀ bl pid, ldat (L2 bl pid) = ldat (L1 bl pid))
    (bl : Loc) (n : Nat) (pid : w64) :
    (lleaves L2 bl n pid).map (List.map wDat) = (lleaves L1 bl n pid).map (List.map wDat) := by
  induction n generalizing pid with
  | zero => rfl
  | succ n ih =>
    have e := hL bl pid
    unfold lleaves
    cases h1 : L1 bl pid with
    | none =>
      rw [h1] at e
      cases h2 : L2 bl pid with
      | none => rfl
      | some x => rw [h2] at e; simp [ldat] at e
    | some x1 =>
      rw [h1] at e
      cases h2 : L2 bl pid with
      | none => rw [h2] at e; simp [ldat] at e
      | some x2 =>
        rw [h2] at e
        simp only [ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨hk, hw⟩ := e
        obtain ⟨b1, ws1⟩ := x1
        obtain ⟨b2, ws2⟩ := x2
        simp only at hk hw
        subst hk
        cases b2 with
        | true => simp [hw]
        | false =>
          have hpg : ws2.map WEntry.pgid = ws1.map WEntry.pgid := by
            have := congrArg (List.map fun d : w32 × w64 × List w8 × List w8 => d.2.1) hw
            simpa [List.map_map, wDat, Function.comp_def] using this
          have := flatMap_pgid_map (List.map wDat) (lleaves L1 bl n) (lleaves L2 bl n) ws1 ws2 hpg
            (fun p => ih p)
          simpa only [List.map_flatMap] using this

theorem size_same_dom {K V W : Type} [DecidableEq K] (m : GMap K V) (m' : GMap K W)
    (h : ∀ k, (m' !! k).isSome ↔ (m !! k).isSome) : GMap.size m' = GMap.size m := by
  rw [GMap.size_eq_length m' m.domList (GMap.nodup_dom_list m)
    (fun k => by rw [GMap.mem_dom_list, h]), GMap.size_eq_dom_list_length]

theorem derefStep_fuel {X X' : WX} (h : derefStep X X') : X'.fuel = X.fuel := by
  unfold WX.fuel
  rw [h.1, size_same_dom X.t.bs X'.t.bs (fun k => by
    have := derefStep_bs h k
    revert this
    cases X.t.bs !! k <;> cases X'.t.bs !! k <;> simp [optRel])]

theorem derefStep_rootPid {X X' : WX} (h : derefStep X X') (bl : Loc) :
    X'.rootPid bl = X.rootPid bl := by
  unfold WX.rootPid
  have hb := derefStep_bs h bl
  cases hB : X.t.bs !! bl with
  | none => rw [hB] at hb; rw [optRel_none_l hb]
  | some B =>
    rw [hB] at hb
    obtain ⟨B', hB', hs⟩ := optRel_some_l hb
    rw [hB']; simp [(bktStep_fields hs).2.1]

theorem derefStep_leaves {X X' : WX} (h : derefStep X X') (bl : Loc) :
    (X'.leaves bl).map (List.map wDat) = (X.leaves bl).map (List.map wDat) := by
  unfold WX.leaves
  rw [derefStep_fuel h, derefStep_rootPid h]
  exact lleaves_ldat _ _ (fun bl pid => derefStep_ltree h bl pid) bl _ _

/-- A list's `filterMap` through the data of its entries. -/
theorem filterMap_wDat {β : Type} (g : w32 × w64 × List w8 × List w8 → Option β)
    (L1 L2 : List (List WEntry)) (h : L2.map (List.map wDat) = L1.map (List.map wDat)) :
    L2.flatMap (fun ws => ws.filterMap (g ∘ wDat)) = L1.flatMap (fun ws => ws.filterMap (g ∘ wDat)) := by
  have : ∀ L : List (List WEntry), L.flatMap (fun ws => ws.filterMap (g ∘ wDat)) =
      (L.map (List.map wDat)).flatMap (fun ds => ds.filterMap g) := by
    intro L
    induction L with
    | nil => rfl
    | cons ws L ih => simp [ih, List.filterMap_map]
  rw [this, this, h]

theorem derefStep_lbktEnts {X X' : WX} (h : derefStep X X') (bl : Loc) :
    lbktEnts X' bl = lbktEnts X bl := by
  unfold lbktEnts
  exact filterMap_wDat (fun d => if decide (isBktFlag d.1) then none else some (d.2.2.1, d.2.2.2))
    _ _ (derefStep_leaves h bl)

theorem derefStep_rootEnts {X X' : WX} (h : derefStep X X') : rootEnts X' = rootEnts X := by
  unfold rootEnts
  rw [h.2.2.2.2.1]
  exact filterMap_wDat (fun d => if decide (isBktFlag d.1) then some (d.2.2.1, d.2.2.2) else none)
    _ _ (derefStep_leaves h X.rl)

theorem derefStep_bktLoc {X X' : WX} (h : derefStep X X') (n : GoString) :
    bktLoc X' n = bktLoc X n := by
  unfold bktLoc
  rw [h.2.2.2.2.1]
  have hb := derefStep_bs h X.rl
  cases hB : X.t.bs !! X.rl with
  | none => rw [hB] at hb; rw [optRel_none_l hb]
  | some B =>
    rw [hB] at hb
    obtain ⟨B', hB', hs⟩ := optRel_some_l hb
    rw [hB']; simp [(bktStep_fields hs).2.2.2.1]

theorem derefStep_wtxData {X X' : WX} (h : derefStep X X') : wtxData X' = wtxData X := by
  apply wtxData_rebalance X X' (derefStep_rootEnts h) (derefStep_bktLoc h)
    (fun n bl _ => derefStep_lbktEnts h bl) (by rw [h.1])

/-- **The coverage contract from the buckets' coverage**: if every reachable bucket's nodes
below its root node's root hold no view slice, no live node does. -/
theorem derefOK_of_cov (X : WX) (hd : objsDisj X.t) (hpre : derefPre X) (hreach : liveReach X)
    (hcov : ∀ bl B, X.t.bs !! bl = some B → bktReach X bl →
      ∀ rt, nodeRootIn B B.bv.rootNode' rt → covered X bl rt) :
    derefOK X := by
  intro l o ho hl
  by_cases hex : ∃ bl B, X.t.bs !! bl = some B ∧ (l = bl ∨ (B.ns !! l).isSome)
  · obtain ⟨bl, B, hB, hlb | hn⟩ := hex
    · subst hlb
      rw [objs_bkt X.t l B hd hB] at ho
      cases ho; trivial
    · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hn
      rw [objs_node X.t bl B l r hd hB hr] at ho
      cases ho
      obtain ⟨rt, hrt, hdesc⟩ := hreach.2 bl B l r hB hr hl
      have hbl := hreach.1 bl B hB (hpre.2.2.1 bl B hB).1
      exact hcov bl B hB hbl rt hrt B l r hB hdesc hr
  · have hoth : ∀ bl B, X.t.bs !! bl = some B → l ≠ bl ∧ B.ns !! l = none := by
      intro bl B hB
      refine ⟨fun h => hex ⟨bl, B, hB, Or.inl h⟩, ?_⟩
      cases h : B.ns !! l with
      | none => rfl
      | some r => exact absurd ⟨bl, B, hB, Or.inr (by simp [h])⟩ hex
    rw [objs_other X.t l hoth] at ho
    exact absurd hl (hpre.2.2.2.2 l (by simp [ho]))

end rel

end bbolt
end EtcdGrove
end Perennial
