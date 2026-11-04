/-
`Bucket.spill`'s root loop's end (U9x9, `notes/bbolt-proof-plan.md`): **a cached child without
a node covers its tree's own pages by its positions** (`nilBkt_coverW`). With no node (`nm = ∅`)
and a root page, the walk of the child reads pages only, so every own page of its tree (`ownHas`
from the root page) is a position of its finite logical tree (`rtOK`), and its extent is the
page's: the converse of `BktEndCov.walkCov_pages` for such a bucket. Used for the root's own
slots at the end (`Lroot`): a slot of the old value of a child the loop skipped (`nilc`) is
covered at the start by that child's positions.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktSlotCov
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeSteps
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX
public import Proof.go_etcd_io.bbolt.Write.DataBnd

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section nilpos
variable [GooseExts]

theorem ltIsL_get {L : LTree} {bl : Loc} : ∀ {ws : List WEntry} {cs : List RTree},
    ltIsL L bl ws cs → ∀ i (hi : i < ws.length), ∃ t ∈ cs, t.pid = ws[i].pgid ∧ ltIs L bl t
  | [], [], _, i, hi => by simp at hi
  | _ :: _, t :: _, h, 0, _ => by
    simp only [ltIsL] at h; exact ⟨t, List.mem_cons_self, h.1, h.2.1⟩
  | _ :: _, _ :: _, h, i + 1, hi => by
    simp only [ltIsL] at h
    obtain ⟨t', ht', h1, h2⟩ := ltIsL_get h.2.2 i (by simpa using hi)
    exact ⟨t', List.mem_cons_of_mem _ ht', by simpa using h1, h2⟩
  | [], _ :: _, h, _, _ => by simp only [ltIsL] at h
  | _ :: _, [], h, _, _ => by simp only [ltIsL] at h

theorem pos_sub_posL : ∀ {cs : List RTree} {t : RTree}, t ∈ cs → ∀ x ∈ t.pos, x ∈ RTree.posL cs
  | [], _, h, _, _ => by cases h
  | _ :: _, _, h, x, hx => by
    rw [RTree.posL]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (pos_sub_posL h x hx)

theorem pid_mem_pos (t : RTree) : t.pid ∈ t.pos := by
  cases t with
  | mk p lf ws cs => cases lf <;> simp [RTree.pos, RTree.pid]

open RTree in
mutual
/-- A subtree's position is a position of the tree. -/
theorem subs_pid_mem_pos {L : LTree} {bl : Loc} : ∀ (t s : RTree), ltIs L bl t → s ∈ t.subs →
    s.pid ∈ t.pos
  | .mk p lf ws cs, s, h, hs => by
    simp only [subs, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact pid_mem_pos _
    · cases lf with
      | true =>
        simp only [ltIs] at h; rw [h.2] at hs; simp [subsL] at hs
      | false =>
        simp only [ltIs] at h
        simp only [pos]
        exact List.mem_cons_of_mem _ (subsL_pid_mem_posL ws cs s h.2 hs)
theorem subsL_pid_mem_posL {L : LTree} {bl : Loc} : ∀ (ws : List WEntry) (cs : List RTree)
    (s : RTree), ltIsL L bl ws cs → s ∈ subsL cs → s.pid ∈ posL cs
  | [], [], s, _, hs => by simp [subsL] at hs
  | _ :: ws, t :: ts, s, h, hs => by
    simp only [ltIsL] at h
    simp only [subsL, List.mem_append] at hs
    simp only [posL, List.mem_append]
    rcases hs with hs | hs
    · exact Or.inl (subs_pid_mem_pos t s h.2.1 hs)
    · exact Or.inr (subsL_pid_mem_posL ws ts s h.2.2 hs)
  | [], _ :: _, _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, h, _ => by simp only [ltIsL] at h
end

/-- **The walk's positions are closed under a branch's children.** -/
theorem pos_child {L : LTree} {bl : Loc} {t : RTree} (ht : ltIs L bl t) {p : w64}
    (hp : p ∈ t.pos) {ws : List WEntry} (hL : L bl p = some (false, ws)) {i : Nat}
    (hi : i < ws.length) : ws[i].pgid ∈ t.pos := by
  obtain ⟨s, hs, rfl⟩ := RTree.pos_subs t p hp
  have hls := ltIs_subs L bl t s ht hs
  cases s with
  | mk q lf ws' cs =>
    cases lf with
    | true =>
      obtain ⟨h1, -⟩ := hls
      simp only [RTree.pid] at hL; rw [hL] at h1; simp at h1
    | false =>
      obtain ⟨h1, h2⟩ := hls
      simp only [RTree.pid] at hL; rw [hL] at h1
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h1
      subst h1
      obtain ⟨c, hc, hcp, -⟩ := ltIsL_get h2 i hi
      rw [← hcp]
      exact subs_pid_mem_pos t c ht (RTree.subs_trans t _ hs c
        (RTree.child_mem_subs q false ws cs c hc c (RTree.self_mem_subs c)))

/-- **Every own page under a position of a page-backed walk is a position.** -/
theorem pos_own {L : LTree} {bl : Loc} {P : Pages} {t : RTree} (ht : ltIs L bl t) {r d : Nat}
    (h : ownHas P r d) : ∀ p : w64, p.toNat = r → p ∈ t.pos →
      (∀ (x : w64) pg, ownHas P r x.toNat → P !! x.toNat = some pg →
        L bl x = some (decide (pageFlags pg = leafPageFlag), pageWs pg)) →
      W64 (d : Int) ∈ t.pos := by
  induction h with
  | root r pg hpg =>
    intro p hp hmem _
    rw [← hp, Write.w64_toNat_eq]; exact hmem
  | child r pg i d hpg hfl hi hrest ih =>
    intro p hp hmem hL
    have hnl : pageFlags pg ≠ leafPageFlag := by rw [hfl]; decide
    have hLp := hL p pg (by rw [hp]; exact ownHas.root r pg hpg) (by rw [hp]; exact hpg)
    rw [show decide (pageFlags pg = leafPageFlag) = false from decide_eq_false hnl] at hLp
    have hi' : i < (pageWs pg).length := by rw [Write.pageWs_len]; exact hi
    have hpgid : (pageWs pg)[i].pgid = W64 (branchPgid pg i : Int) := by
      have := Write.pageWs_getD pg i hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some] at this
      rw [this]; exact (Write.pageW_branch pg i hnl).2
    have hc := pos_child ht hmem hLp hi'
    rw [hpgid] at hc
    exact ih _ (Write.branchPgid_toNat pg i) hc
      (fun x pg' ho hx => hL x pg' (ownHas.child r pg i _ hpg hfl hi ho) hx)

/-- A bucket with no node and a root page: its walk reads the view's pages. -/
theorem ltree_nilBkt {X : WX} {c : Loc} {C : BRec} (hC : X.t.bs !! c = some C) (hnm : C.nm = ∅)
    (h0 : C.ib.root' ≠ W64 0) (p : w64) (pg : List w8) (hpg : X.v.pages !! p.toNat = some pg) :
    ltree X c p = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
  have hr : resolve C p = none := by unfold resolve; rw [if_neg h0, hnm]; rfl
  unfold ltree; rw [hC]; simp only; rw [hr]
  unfold wpageAt; rw [if_neg h0, hpg]; rfl

/-- **A bucket with no node and a root page: every own page of its tree is a position.** -/
theorem nilBkt_pos {X : WX} {c : Loc} {C : BRec} (hC : X.t.bs !! c = some C) (hnm : C.nm = ∅)
    (h0 : C.ib.root' ≠ W64 0) (hrt : rtOK X c) {d : Nat}
    (hd : ownHas X.v.pages C.ib.root'.toNat d) : W64 (d : Int) ∈ X.positions c := by
  obtain ⟨t, ht, htp, hth, -⟩ := hrt
  rw [positions_rt X c t ht htp hth]
  have hrp : X.rootPid c = C.ib.root' := by unfold WX.rootPid; rw [hC]; rfl
  exact pos_own ht hd t.pid (by rw [htp, hrp]) (pid_mem_pos t)
    (fun p pg _ hpg => ltree_nilBkt hC hnm h0 p pg hpg)

/-- **A bucket with no node covers its tree's own pages' slots by its positions.** -/
theorem nilBkt_coverW {X : WX} {c : Loc} {C : BRec} (hC : X.t.bs !! c = some C) (hnm : C.nm = ∅)
    (h0 : C.ib.root' ≠ W64 0) (hrt : rtOK X c) {d : Nat}
    (hd : ownHas X.v.pages C.ib.root'.toNat d) (h2 : 2 ≤ d) (h64 : d < 2 ^ 64) {pg : List w8}
    (hpg : X.v.pages !! d = some pg) {s : Nat} (h1 : d ≤ s) (h3 : s < d + (1 + pageOverflow pg)) :
    coverW X s (.pos c (W64 (d : Int))) := by
  have hdn : (W64 (d : Int)).toNat = d := w64_cast_toNat h64
  have hne : W64 (d : Int) ≠ W64 0 := by
    intro e; have := congrArg BitVec.toNat e; rw [hdn] at this; simp at this; omega
  have hr : resolve C (W64 (d : Int)) = none := by unfold resolve; rw [if_neg h0, hnm]; rfl
  refine ⟨by rw [hC]; simp, nilBkt_pos hC hnm h0 hrt hd, (W64 (d : Int), 1 + pageOverflow pg),
    ?_, by rw [hdn]; exact h1, by rw [hdn]; exact h3⟩
  unfold WX.posExtent; rw [hC]; simp only; rw [hr]; simp only
  rw [if_neg hne, hdn, hpg]; rfl

end nilpos

end Spill

end bbolt
end EtcdGrove
end Perennial
