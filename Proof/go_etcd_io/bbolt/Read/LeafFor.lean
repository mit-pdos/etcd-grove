/-
U6 (`notes/bbolt-proof-plan.md`): the writer's search lemma `lRoutes_leafFor` (`Model/WOps`), as
`lRoutes_leafFor'`: after `Cursor.node` materialized a routed stack's path (`matGrow`), the node at
its last position is a leaf whose bounds hold the key. Materialization keeps `wOK` and the logical
tree by data along the route (`Write.wOK_nodeAdded`, `Write.ltree_nodeAdded'`), so the route is one
of the grown writer, whose walk (`LR.route_main`) gives the leaf's bounds.
-/
module

public import Proof.go_etcd_io.bbolt.Read.LRoutes
public import Proof.go_etcd_io.bbolt.Write.MatGrow

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace LR

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write

section leaffor
variable [GooseExts]

theorem map_wDat_getD (ws ws' : List WEntry) (h : ws'.map wDat = ws.map wDat) (i : Nat) :
    (ws'.getD i default).key = (ws.getD i default).key ∧
      (ws'.getD i default).pgid = (ws.getD i default).pgid := by
  have hl : ws'.length = ws.length := by simpa using congrArg List.length h
  by_cases hi : i < ws.length
  · have hi' : i < ws'.length := by omega
    have e := congrArg (fun l => l[i]?) h
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
      Option.map_some, Option.some.injEq] at e
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi']
    simp only [Option.getD_some]
    unfold wDat at e
    simp only [Prod.mk.injEq] at e
    exact ⟨e.2.2.1, e.2.1⟩
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    exact ⟨rfl, rfl⟩

/-- A route is one of any logical tree with the same data along it. -/
theorem lRoute_ldat (L L' : LTree) (bl : Loc) (k : List w8) :
    ∀ pids, lRoute L bl k pids → (∀ p ∈ pids, ldat (L' bl p) = ldat (L bl p)) →
      lRoute L' bl k pids
  | [], h, _ => h.elim
  | [p], ⟨ws, hL⟩, hd => by
    have e := hd p (List.mem_singleton_self p)
    rw [hL] at e
    cases hL' : L' bl p with
    | none => rw [hL'] at e; cases e
    | some x =>
      obtain ⟨lf, ws'⟩ := x
      rw [hL'] at e
      simp only [ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      exact ⟨ws', by rw [hL', e.1]⟩
  | p :: q :: rest, ⟨ws, i, hL, hi, h0, h1, hq, hr⟩, hd => by
    have e := hd p List.mem_cons_self
    rw [hL] at e
    cases hL' : L' bl p with
    | none => rw [hL'] at e; cases e
    | some x =>
      obtain ⟨lf, ws'⟩ := x
      rw [hL'] at e
      simp only [ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, hm⟩ := e
      have hl : ws'.length = ws.length := by simpa using congrArg List.length hm
      refine ⟨ws', i, hL', by omega, ?_, ?_, ?_,
        lRoute_ldat L L' bl k (q :: rest) hr (fun p' hp' => hd p' (List.mem_cons_of_mem _ hp'))⟩
      · rw [(map_wDat_getD ws ws' hm i).1]; exact h0
      · intro h; rw [(map_wDat_getD ws ws' hm (i + 1)).1]; exact h1 (by omega)
      · rw [(map_wDat_getD ws ws' hm i).2]; exact hq

/-- A route from an inline bucket's root is its root alone (position `0`). -/
theorem wOK_route_inline (X : WX) (bl : Loc) (B : BRec) (hok : wOK X)
    (hB : X.t.bs !! bl = some B) (hin : B.ib.root' = W64 0) (k : List w8) (pids : List w64)
    (hr : lRoute (ltree X) bl k pids) (hh : pids.head? = some (X.rootPid bl)) :
    ∀ p ∈ pids, p = W64 0 := by
  obtain ⟨bnd, hbk⟩ := (hok.2.1 bl B hB).1
  have hc := wOK_bktClean X hok bl B hB
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  cases pids with
  | nil => cases hh
  | cons p rest =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    cases rest with
    | cons q rest =>
      obtain ⟨ws, _, hL, -⟩ := hr
      exact absurd hL (inl_noBranch X bl B bnd _ hB hc hbk hv hin p ws)
    | nil =>
      intro p' hp'
      rw [List.mem_singleton] at hp'
      rw [hp', hh, rootPid_eq X bl B bnd _ hB hc hbk hv, hin]

/-- **Materializations keep a route from the root** (and `wOK`). -/
theorem matGrow_route (k : List w8) (pids : List w64) :
    ∀ X X' bl, matGrow X X' bl → wOK X → lRoute (ltree X) bl k pids →
      pids.head? = some (X.rootPid bl) →
      wOK X' ∧ lRoute (ltree X') bl k pids ∧ pids.head? = some (X'.rootPid bl) := by
  intro X X' bl h
  induction h with
  | refl X bl => intro hok hr hh; exact ⟨hok, hr, hh⟩
  | step X Y Z bl l pgid parent hadd hpos _ ih =>
    intro hok hr hh
    have hY := Write.wOK_nodeAdded X Y bl l pgid parent hok hadd hpos
    have hf := wOK_matFresh X Y bl l pgid parent hok hadd hpos
    have hadd' := hadd
    obtain ⟨B, pa, pg, r, ns', bv', hB, hpg, hnm, hl0, hlo, hrb, hrp, hrid, hrleaf, hru, hrs,
      hrcs, hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase, hX'⟩ := hadd'
    have hrp0 : Y.rootPid bl = X.rootPid bl := by
      rw [hX']; unfold WX.rootPid; simp only [GMap.lookup_insert, hB]; rfl
    have hdat : ∀ p ∈ pids, ldat (ltree Y bl p) = ldat (ltree X bl p) := fun p hp =>
      ltree_nodeAdded' X Y bl l pgid parent hadd hf bl p
        (fun _ B' hB' hin => wOK_route_inline X bl B' hok hB' hin k pids hr hh p hp)
    exact ih hY (lRoute_ldat _ _ bl k pids hr hdat) (by rw [hrp0]; exact hh)

end leaffor

end LR

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write LR in
/-- **`lRoutes_leafFor`** (`Model/WOps`), proved: after `Cursor.node` materialized the stack's
path, the node at its last position is the leaf where `k` lands. -/
theorem lRoutes_leafFor' [GooseExts] (X X' : WX) (bl l : Loc) (els : List elemRef)
    (pids : List w64) (k : List w8) (hok : wOK X) (hp : lPath X bl els pids)
    (hr : lRoutes X bl els pids k) (hg : matGrow X X' bl) (hl : ∃ B, X'.t.bs !! bl = some B ∧
      ∃ pid, pids.getLast? = some pid ∧ resolve B pid = some l) :
    leafFor X' bl k l := by
  obtain ⟨hok', hR', hh'⟩ := LR.matGrow_route k pids X X' bl hg hok
    (LR.lRoute_of X bl els pids k hp hr) hp.2.2.1
  obtain ⟨B, hB, pid, hgl, hres⟩ := hl
  obtain ⟨bnd, hbk⟩ := (hok'.2.1 bl B hB).1
  have hc := Write.wOK_bktClean X' hok' bl B hB
  have hv : viewWF X'.v := hok'.2.2.2.2.2.2.2
  obtain ⟨last, b', ws, hgl', hL, -, hI, hk⟩ :=
    LR.route_main X' bl B bnd _ hB hc hbk hv k pids hR' hh'
  rw [hgl] at hgl'
  cases hgl'
  rcases hI with ⟨m, rm, hm, hrm, hbm⟩ | ⟨hin, htk, hfree⟩ | ⟨-, hin, hrn⟩
  · rw [hres] at hm
    cases hm
    rw [LR.ltreeB X' bl B bnd _ hB hc hbk hv, hres] at hL
    simp only [hrm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
    exact ⟨B, rm, bnd, hB, hrm, hL.1, hbk, by rw [hbm]; exact hk⟩
  · obtain ⟨pg, hpg⟩ := LR.treeKeys_some _ _ _ _ htk
    have := hfree _ (treeHas.root _ pg hpg)
    rw [LR.w64_toNat_eq, ← LR.res_nm X' bl B bnd _ hB hc hbk hv hin, hres] at this
    cases this
  · unfold resolve at hres
    rw [if_pos hin, if_pos hrn] at hres
    cases hres
