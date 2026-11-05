/-
`Bucket.spill`'s root loop's end (U9x10, `notes/bbolt-proof-plan.md`): **the walk of a bucket of
view pages reads its tree's leaves** (`vl_lleaves_fuel`), and a plain leaf page's entries by
`lbktEnts`' filter (`vl_plain_pageWs`). Copies of `Read/WOpenWOK`'s `viewL`, `lleaves_viewL`,
`lleaves_viewL_fuel` and `plain_pageWs` (that module did not build against maintainer 13's
`posShape`, 2026-11-05; the copies import less): to be merged into them.
-/
module

public import Proof.go_etcd_io.bbolt.Write.Fuel
public import Proof.go_etcd_io.bbolt.Inv.MatReady
public import Proof.go_etcd_io.bbolt.Read.LRoutes
public import Proof.go_etcd_io.bbolt.Spill.BktPlain
public import Proof.go_etcd_io.bbolt.Rebalance.RblMat

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section viewl
variable [GooseExts]

/-- The logical tree of a bucket with no node: its view pages. -/
def vlL (v : View) (c : Loc) : LTree := fun k p =>
  if k = c then (v.pages !! p.toNat).map fun pg => (decide (pageFlags pg = leafPageFlag), pageWs pg)
  else none

theorem vl_congr (L L' : LTree) (bl : Loc) (h : ∀ q, L bl q = L' bl q) :
    ∀ n p, lleaves L bl n p = lleaves L' bl n p := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ih => intro p; simp only [lleaves, h p, ih]

theorem vl_lleaves (v : View) (c : Loc) :
    ∀ n (pid : w64), lleaves (vlL v c) c n pid = (leavesF n v.pages pid.toNat).map pageWs
  | 0, _ => rfl
  | n + 1, pid => by
    simp only [lleaves, leavesF]
    simp only [vlL, ↓reduceIte]
    cases hp : v.pages !! pid.toNat with
    | none => rfl
    | some pg =>
      simp only [Option.map_some]
      by_cases hl : pageFlags pg = leafPageFlag
      · simp [hl]
      · simp only [hl, decide_false, ite_false]
        rw [List.map_flatMap]
        unfold pageWs
        rw [List.flatMap_map]
        apply Write.flatMap_congr'
        intro i _
        have hpw : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
          unfold pageW; rw [if_neg hl]
        rw [hpw, vl_lleaves v c n, LR.branchPgid_toNat]; rfl

/-- **A bucket of view pages walks its tree's leaves** with any fuel past the pages'. -/
theorem vl_lleaves_fuel (v : View) (hv : viewWF v) (c : Loc) (pid : w64) (k : Nat) :
    lleaves (vlL v c) c (v.pages.size + 1 + k) pid =
      (treeLeaves v.pages pid.toNat).map pageWs := by
  unfold treeLeaves
  rw [← vl_lleaves]
  apply Write.lleaves_fuel_stable (vlL v c) c (Write.treeMeasure v.pages) ?_ (v.pages.size + 1) k pid
  · have := Write.treeMeasure_le v.pages pid; omega
  · intro p ws hL w hw
    simp only [vlL, ↓reduceIte] at hL
    cases hp : v.pages !! p.toNat with
    | none => rw [hp] at hL; cases hL
    | some pg =>
      rw [hp] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
      obtain ⟨hnl, rfl⟩ := hL
      unfold pageWs at hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
      rw [List.mem_range] at hi
      have hpw : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
        unfold pageW; rw [if_neg hnl]
      rw [hpw]
      have hb : pageFlags pg = branchPageFlag := by
        rcases (viewWF_page_ready v hv _ pg hp).2.2.1 with e | e
        · exact absurd e hnl
        · exact e
      exact Write.treeMeasure_child v hv p pg hp hb i hi

/-- A plain leaf page's entries through `lbktEnts`' filter are its entries. -/
theorem vl_plain_pageWs (pg : List w8) (hl : pageFlags pg = leafPageFlag)
    (hp : ∀ j < pageCount pg, leafFlags pg j % 2 = 0) :
    (pageWs pg).filterMap (fun w => if decide (isBktFlag w.flags) then none
      else some (w.key, w.value)) = leafEnts pg := by
  unfold pageWs leafEnts
  rw [List.filterMap_map]
  have key : ∀ (l : List Nat), (∀ i ∈ l, i < pageCount pg) →
      l.filterMap ((fun w : WEntry => if decide (isBktFlag w.flags) then none
        else some (w.key, w.value)) ∘ pageW pg) =
        l.map fun i => (leafKey pg i, leafValue pg i) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons i t ih =>
      intro hl'
      have hi := hl' i (by simp)
      have hf := mat_pageW_leaf pg i hl
      have hnb : ¬ isBktFlag (pageW pg i).flags := by
        rw [(notBkt_iff _), hf.1]
        have := leafFlags_lt pg i
        have e : (W32 (leafFlags pg i : Int)).toNat = leafFlags pg i := by
          simp only [BitVec.toNat_ofInt]; omega
        rw [e]; exact hp i hi
      rw [List.filterMap_cons, List.map_cons]
      simp only [Function.comp_def, hnb, decide_false, Bool.false_eq_true, ↓reduceIte, hf.2.2.1,
        hf.2.2.2]
      rw [← ih (fun j hj => hl' j (List.mem_cons_of_mem _ hj))]
      rfl
  exact key _ (fun i hi => List.mem_range.1 hi)

end viewl

end Spill

end bbolt
end EtcdGrove
end Perennial
