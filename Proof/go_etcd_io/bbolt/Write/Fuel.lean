/-
U7's (`notes/bbolt-proof-plan.md`) `wOK_leaves_fuel`: a well-formed writer's logical tree has the
base tree's branch shape (`txPg`: a branch node's children are its page's), whose subtrees shrink
strictly (`viewUnique`: no branch is in its child's subtree), so the walk ends within the view's
page count and more fuel walks the same leaves.
-/
module

public import Proof.go_etcd_io.bbolt.Write.WOk
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section fuel
variable [GooseExts]

theorem flatMap_congr' {α β : Type} (ws : List α) (f g : α → List β)
    (h : ∀ w ∈ ws, f w = g w) : ws.flatMap f = ws.flatMap g := by
  induction ws with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.flatMap_cons, h a List.mem_cons_self,
      ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]

/-- **More fuel walks the same leaves** once a measure decreases along branches below the fuel. -/
theorem lleaves_fuel_stable (L : LTree) (bl : Loc) (μ : w64 → Nat)
    (hdec : ∀ pid ws, L bl pid = some (false, ws) → ∀ w ∈ ws, μ w.pgid < μ pid) :
    ∀ n k pid, μ pid < n → lleaves L bl (n + k) pid = lleaves L bl n pid
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, pid, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [lleaves]
    cases hL : L bl pid with
    | none => rfl
    | some x =>
      obtain ⟨lf, ws⟩ := x
      cases lf with
      | true => rfl
      | false =>
        simp only
        apply flatMap_congr'
        intro w hw
        exact lleaves_fuel_stable L bl μ hdec n k w.pgid (by have := hdec pid ws hL w hw; omega)

theorem len_filter_le {α : Type} (L : List α) (p q : α → Bool)
    (hpq : ∀ x ∈ L, p x = true → q x = true) : (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih' := ih (fun y hy => hpq y (List.mem_cons_of_mem _ hy))
    have ha := hpq a List.mem_cons_self
    simp only [List.filter_cons]
    cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

theorem len_filter_lt {α : Type} (L : List α) (p q : α → Bool) (hpq : ∀ x ∈ L, p x = true → q x = true)
    (x : α) (hx : x ∈ L) (hq : q x = true) (hp : p x = false) :
    (L.filter p).length < (L.filter q).length := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    have hpq' : ∀ y ∈ L, p y = true → q y = true := fun y hy => hpq y (List.mem_cons_of_mem _ hy)
    have hle := len_filter_le L p q hpq'
    have ha := hpq a List.mem_cons_self
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp only [hp, hq]; simp; omega
    · have := ih hpq' hx'
      cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

/-- The view's pages' measure: the number of pages of the tree from `pid`. -/
def treeMeasure (P : Pages) (pid : w64) : Nat :=
  open Classical in
  ((P.toList.map Prod.fst).filter fun d => decide (treeHas P pid.toNat d)).length

theorem treeMeasure_le (P : Pages) (pid : w64) : treeMeasure P pid ≤ P.size := by
  unfold treeMeasure GMap.size
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- A branch page's child has fewer pages in its tree (`viewUnique`). -/
theorem treeMeasure_child (v : View) (hv : viewWF v) (pid : w64) (pg : List w8)
    (hpg : v.pages !! pid.toNat = some pg) (hb : pageFlags pg = branchPageFlag) (i : Nat)
    (hi : i < pageCount pg) :
    treeMeasure v.pages (W64 (branchPgid pg i : Int)) < treeMeasure v.pages pid := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hP : v.pages = C.pages := by rw [← hvC]; rfl
  have hu := hok.1.2.1.2
  have hpgC : C.pages !! pid.toNat = some pg := by rw [← hP]; exact hpg
  have hnot := (hu.1 pid.toNat pg hpgC hb).2 i hi
  have hc : (W64 (branchPgid pg i : Int)).toNat = branchPgid pg i := by
    unfold branchPgid; simp
  classical
  unfold treeMeasure
  rw [hc]
  apply len_filter_lt _ _ _ _ pid.toNat
  · rw [List.mem_map]; exact ⟨(pid.toNat, pg), (GMap.mem_toList _ _ _).2 hpg, rfl⟩
  · simp only [decide_eq_true_eq]; exact treeHas.root _ pg hpg
  · simp only [decide_eq_false_iff_not]; rw [hP]; exact hnot
  · intro d _ hd
    simp only [decide_eq_true_eq] at hd ⊢
    exact treeHas.sub _ pg d hpg (pageHas.child pg i d hb hi hd)

/-- **The walk of a well-formed writer's tree ends within its fuel** (the shared lemma, batch 31; its
stub in `Model/LTree` is deleted): more fuel walks the same leaves. -/
theorem wOK_leaves_fuel' (X : WX) (bl : Loc) (hok : wOK X) (k : Nat) :
    lleaves (ltree X) bl (X.fuel + k) (X.rootPid bl) = X.leaves bl := by
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  unfold WX.leaves
  apply lleaves_fuel_stable (ltree X) bl (treeMeasure X.v.pages) _ X.fuel k
  · have := treeMeasure_le X.v.pages (X.rootPid bl)
    unfold WX.fuel; omega
  intro pid ws hL w hw
  unfold ltree at hL
  cases hB : X.t.bs !! bl with
  | none => rw [hB] at hL; cases hL
  | some B =>
    rw [hB] at hL
    simp only at hL
    have hc := wOK_bktClean X hok bl B hB
    cases hr : resolve B pid with
    | some l =>
      rw [hr] at hL
      simp only at hL
      cases hrl : B.ns !! l with
      | none => rw [hrl] at hL; cases hL
      | some r =>
        rw [hrl] at hL
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
        obtain ⟨hleaf, rfl⟩ := hL
        by_cases hin : B.ib.root' = W64 0
        · have := hc.2.2.2.2.2.2.1 hin l r hrl; rw [hleaf] at this; cases this
        · have hnm : B.nm !! pid = some l := by unfold resolve at hr; rwa [if_neg hin] at hr
          obtain ⟨-, r', hr', hpid⟩ := hc.2.2.2.2.1 pid l hnm
          rw [hrl] at hr'; cases hr'
          obtain ⟨-, pg, hpg, hbr, hlen, hws⟩ := ((hok.2.2.1 bl B hB l r hrl).2 hleaf)
          rw [hpid] at hpg
          obtain ⟨i, hi, he⟩ := List.getElem_of_mem hw
          have hwi : r.ws[i]? = some w := by rw [List.getElem?_eq_getElem hi]; exact congrArg _ he
          rw [hws i w hwi]
          exact treeMeasure_child X.v hv pid pg hpg hbr i (by rw [← hlen]; exact hi)
    | none =>
      rw [hr] at hL
      simp only at hL
      cases hp : wpageAt X.v B pid with
      | none => rw [hp] at hL; cases hL
      | some x =>
        obtain ⟨pa, pg⟩ := x
        rw [hp] at hL
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
        obtain ⟨hnl, rfl⟩ := hL
        by_cases hin : B.ib.root' = W64 0
        · have hrn : B.bv.rootNode' = null := by
            unfold resolve at hr; rw [if_pos hin] at hr; split at hr
            · assumption
            · cases hr
          have := wOK_inlineLeaf X bl pid hok B pa pg hB hin hrn hp
          exact absurd this hnl
        · have hpg : X.v.pages !! pid.toNat = some pg := by
            unfold wpageAt at hp; rw [if_neg hin] at hp
            cases h : X.v.pages !! pid.toNat with
            | none => rw [h] at hp; cases hp
            | some pg' => rw [h] at hp; simp only [Option.map_some, Option.some.injEq,
                            Prod.mk.injEq] at hp; rw [hp.2]
          have hbr : pageFlags pg = branchPageFlag := by
            rcases (Read.viewWF_page X.v hv _ pg hpg).2.2.2 with h | h
            · exact h
            · exact absurd h hnl
          unfold pageWs at hw
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
          rw [List.mem_range] at hi
          have : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
            unfold pageW; simp [hnl]
          rw [this]
          exact treeMeasure_child X.v hv pid pg hpg hbr i hi

end fuel

end Write

end bbolt
end EtcdGrove
end Perennial
