/-
`rebalance`'s three steps on the logical tree (U8b, `notes/bbolt-proof-plan.md`), over any
`LTree` (`L` before, `L'` after, equal off the positions the step changes):
- **merge** (`rt_merge`): the parent `P`'s entries `k`, `k + 1` (positions `A`, `R`, of one kind)
  become one, `A`'s, holding `A`'s entries then `R`'s; `R` is gone;
- **removal** (`rt_remove`): the parent `P`'s entry `k`, an empty leaf `E`, is gone;
- **root collapse** (`rt_collapse`): the root `P`, a branch of one entry (position `C`), takes
  `C`'s kind and entries; `C` is gone.

Each keeps the leaves' entries (flattened: the data), does not grow the height, keeps the leaves
at one depth (one less after a collapse), and keeps the positions but the one gone. The changed
positions occur where the step expects them: a child position `A`, `R`, `E`, `C` only under `P`
(`RTree.edge`), which the bucket's records give (`Rebalance/RTreeX.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RTreeRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section steps
variable [GooseExts]
set_option linter.unusedSectionVars false

namespace RTree

mutual
/-- Every subtree (the tree itself first). -/
def subs : RTree → List RTree
  | mk p lf ws cs => mk p lf ws cs :: subsL cs
def subsL : List RTree → List RTree
  | [] => []
  | t :: ts => subs t ++ subsL ts
end

/-- `c` is the position of a child of a branch at position `x` in `t`. -/
def edge (t : RTree) (x c : w64) : Prop :=
  ∃ s ∈ t.subs, s.pid = x ∧ s.lf = false ∧ c ∈ s.cs.map RTree.pid

end RTree

open RTree

/-- The data, height, depths and positions `t'` keeps of `t`, the position `gone` removed
(`dd` the depth change of the leaves: `0`, or `1` for a collapse). -/
def rtKept (t t' : RTree) (gone : w64) (dd : Nat) : Prop :=
  t'.pid = t.pid ∧ t'.lvs.flatten = t.lvs.flatten ∧ t'.ht ≤ t.ht ∧
  (∀ D, (∀ x ∈ t.dps 0, x = D) → ∀ x ∈ t'.dps 0, x = D - dd) ∧
  (∀ x ∈ t'.pos, x ∈ t.pos ∧ x ≠ gone) ∧ (∀ x ∈ t.pos, x ≠ gone → x ∈ t'.pos)

/-! ## Helpers: subtrees, sizes, positions -/

namespace RTree

mutual
/-- The number of nodes. -/
def sz : RTree → Nat
  | mk _ _ _ cs => szL cs + 1
def szL : List RTree → Nat
  | [] => 0
  | t :: ts => sz t + szL ts
end

theorem le_szL_of_mem : ∀ (cs : List RTree) (c : RTree), c ∈ cs → sz c ≤ szL cs
  | [], c, h => by simp at h
  | t :: ts, c, h => by
    simp only [List.mem_cons] at h
    simp only [szL]
    rcases h with rfl | h
    · omega
    · have := le_szL_of_mem ts c h; omega

theorem sz_child (p : w64) (lf : Bool) (ws : List WEntry) (cs : List RTree) (c : RTree)
    (h : c ∈ cs) : sz c < sz (mk p lf ws cs) := by
  have := le_szL_of_mem cs c h; simp only [sz]; omega

theorem mem_subsL (cs : List RTree) (s : RTree) : s ∈ subsL cs ↔ ∃ c ∈ cs, s ∈ c.subs := by
  induction cs with
  | nil => simp [subsL]
  | cons t ts ih => simp [subsL, ih]

theorem mem_posL (cs : List RTree) (x : w64) : x ∈ posL cs ↔ ∃ c ∈ cs, x ∈ c.pos := by
  induction cs with
  | nil => simp [posL]
  | cons t ts ih => simp [posL, ih]

theorem self_mem_subs (t : RTree) : t ∈ t.subs := by
  cases t; simp [subs]

theorem child_mem_subs (p : w64) (lf : Bool) (ws : List WEntry) (cs : List RTree) (c : RTree)
    (h : c ∈ cs) (s : RTree) (hs : s ∈ c.subs) : s ∈ (mk p lf ws cs).subs := by
  simp only [subs, List.mem_cons, mem_subsL]
  exact Or.inr ⟨c, h, hs⟩

mutual
theorem sz_subs : ∀ (t s : RTree), s ∈ t.subs → sz s ≤ sz t
  | mk p lf ws cs, s, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · have := sz_subsL cs s h; simp only [sz]; omega
theorem sz_subsL : ∀ (cs : List RTree) (s : RTree), s ∈ subsL cs → sz s ≤ szL cs
  | [], s, h => by simp [subsL] at h
  | t :: ts, s, h => by
    simp only [subsL, List.mem_append] at h
    simp only [szL]
    rcases h with h | h
    · have := sz_subs t s h; omega
    · have := sz_subsL ts s h; omega
end

mutual
theorem subs_trans : ∀ (t c : RTree), c ∈ t.subs → ∀ s ∈ c.subs, s ∈ t.subs
  | mk p lf ws cs, c, h, s, hs => by
    simp only [subs, List.mem_cons] at h
    rcases h with rfl | h
    · exact hs
    · simp only [subs, List.mem_cons]
      exact Or.inr (subsL_trans cs c h s hs)
theorem subsL_trans : ∀ (cs : List RTree) (c : RTree), c ∈ subsL cs → ∀ s ∈ c.subs, s ∈ subsL cs
  | [], c, h, _, _ => by simp [subsL] at h
  | t :: ts, c, h, s, hs => by
    simp only [subsL, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (subs_trans t c h s hs)
    · exact Or.inr (subsL_trans ts c h s hs)
end

theorem edge_mono (t c : RTree) (hc : c ∈ t.subs) (x y : w64) (h : edge c x y) : edge t x y := by
  obtain ⟨s, hs, h1, h2, h3⟩ := h
  exact ⟨s, subs_trans t c hc s hs, h1, h2, h3⟩

mutual
theorem pos_subs : ∀ (t : RTree) (x : w64), x ∈ t.pos → ∃ s ∈ t.subs, s.pid = x
  | mk p true ws cs, x, h => by
    simp only [pos, List.mem_singleton] at h
    exact ⟨_, self_mem_subs _, h.symm⟩
  | mk p false ws cs, x, h => by
    simp only [pos, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨_, self_mem_subs _, h.symm⟩
    · obtain ⟨s, hs, hp⟩ := posL_subs cs x h
      exact ⟨s, by simp only [subs, List.mem_cons]; exact Or.inr hs, hp⟩
theorem posL_subs : ∀ (cs : List RTree) (x : w64), x ∈ posL cs → ∃ s ∈ subsL cs, s.pid = x
  | [], x, h => by simp [posL] at h
  | t :: ts, x, h => by
    simp only [posL, List.mem_append] at h
    simp only [subsL, List.mem_append]
    rcases h with h | h
    · obtain ⟨s, hs, hp⟩ := pos_subs t x h; exact ⟨s, Or.inl hs, hp⟩
    · obtain ⟨s, hs, hp⟩ := posL_subs ts x h; exact ⟨s, Or.inr hs, hp⟩
end

end RTree

open RTree

mutual
theorem ltIs_subs (L : LTree) (bl : Loc) : ∀ (t s : RTree), ltIs L bl t → s ∈ t.subs → ltIs L bl s
  | .mk p lf ws cs, s, h, hs => by
    simp only [subs, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact h
    · cases lf with
      | true =>
        simp only [ltIs] at h; rw [h.2] at hs; simp [subsL] at hs
      | false =>
        simp only [ltIs] at h
        exact ltIsL_subs L bl ws cs s h.2 hs
theorem ltIsL_subs (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree) (s : RTree),
    ltIsL L bl ws cs → s ∈ subsL cs → ltIs L bl s
  | [], [], s, _, hs => by simp [subsL] at hs
  | w :: ws, t :: ts, s, h, hs => by
    simp only [ltIsL] at h
    simp only [subsL, List.mem_append] at hs
    rcases hs with hs | hs
    · exact ltIs_subs L bl t s h.2.1 hs
    · exact ltIsL_subs L bl ws ts s h.2.2 hs
  | [], _ :: _, _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, h, _ => by simp only [ltIsL] at h
end

theorem ltIsL_mem (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree),
    ltIsL L bl ws cs → ∀ c ∈ cs, ltIs L bl c ∧ ∃ w ∈ ws, c.pid = w.pgid
  | [], [], _, c, hc => by simp at hc
  | w :: ws, t :: ts, h, c, hc => by
    simp only [ltIsL] at h
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨h.2.1, w, List.mem_cons_self .., h.1⟩
    · obtain ⟨h1, w', hw', h2⟩ := ltIsL_mem L bl ws ts h.2.2 c hc
      exact ⟨h1, w', List.mem_cons_of_mem _ hw', h2⟩
  | [], _ :: _, h, _, _ => by simp only [ltIsL] at h
  | _ :: _, [], h, _, _ => by simp only [ltIsL] at h

mutual
/-- A subtree is the tree, or a child of a branch of it. -/
theorem sub_cases (L : LTree) (bl : Loc) : ∀ (t s : RTree), ltIs L bl t → s ∈ t.subs →
    s = t ∨ ∃ y ∈ t.subs, y.lf = false ∧ s ∈ y.cs
  | .mk p lf ws cs, s, h, hs => by
    simp only [subs, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact Or.inl rfl
    · cases lf with
      | true =>
        simp only [ltIs] at h; rw [h.2] at hs; simp [subsL] at hs
      | false =>
        simp only [ltIs] at h
        right
        rcases sub_casesL L bl ws cs s h.2 hs with ⟨c, hc, rfl⟩ | ⟨y, hy, h1, h2⟩
        · exact ⟨_, self_mem_subs _, rfl, hc⟩
        · exact ⟨y, by simp only [subs, List.mem_cons]; exact Or.inr hy, h1, h2⟩
theorem sub_casesL (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree) (s : RTree),
    ltIsL L bl ws cs → s ∈ subsL cs →
    (∃ c ∈ cs, s = c) ∨ ∃ y ∈ subsL cs, y.lf = false ∧ s ∈ y.cs
  | [], [], s, _, hs => by simp [subsL] at hs
  | w :: ws, t :: ts, s, h, hs => by
    simp only [ltIsL] at h
    simp only [subsL, List.mem_append] at hs
    rcases hs with hs | hs
    · rcases sub_cases L bl t s h.2.1 hs with rfl | ⟨y, hy, h1, h2⟩
      · exact Or.inl ⟨s, List.mem_cons_self .., rfl⟩
      · exact Or.inr ⟨y, by simp only [subsL, List.mem_append]; exact Or.inl hy, h1, h2⟩
    · rcases sub_casesL L bl ws ts s h.2.2 hs with ⟨c, hc, rfl⟩ | ⟨y, hy, h1, h2⟩
      · exact Or.inl ⟨s, List.mem_cons_of_mem _ hc, rfl⟩
      · exact Or.inr ⟨y, by simp only [subsL, List.mem_append]; exact Or.inr hy, h1, h2⟩
  | [], _ :: _, _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, h, _ => by simp only [ltIsL] at h
end

/-- A subtree of `t` other than `t` is the child of an edge. -/
theorem sub_edge (L : LTree) (bl : Loc) (t s : RTree) (h : ltIs L bl t) (hs : s ∈ t.subs) :
    s = t ∨ ∃ y ∈ t.subs, edge t y.pid s.pid := by
  rcases sub_cases L bl t s h hs with h | ⟨y, hy, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, hy, ⟨y, hy, rfl, h1, List.mem_map_of_mem h2⟩⟩

mutual
theorem subs_pid_pos (L : LTree) (bl : Loc) : ∀ (t s : RTree), ltIs L bl t → s ∈ t.subs →
    s.pid ∈ t.pos
  | .mk p lf ws cs, s, h, hs => by
    simp only [subs, List.mem_cons] at hs
    rcases hs with rfl | hs
    · cases lf <;> simp [pos, RTree.pid]
    · cases lf with
      | true =>
        simp only [ltIs] at h; rw [h.2] at hs; simp [subsL] at hs
      | false =>
        simp only [ltIs] at h
        simp only [pos, List.mem_cons]
        exact Or.inr (subsL_pid_posL L bl ws cs s h.2 hs)
theorem subsL_pid_posL (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree) (s : RTree),
    ltIsL L bl ws cs → s ∈ subsL cs → s.pid ∈ posL cs
  | [], [], s, _, hs => by simp [subsL] at hs
  | w :: ws, t :: ts, s, h, hs => by
    simp only [ltIsL] at h
    simp only [subsL, List.mem_append] at hs
    simp only [posL, List.mem_append]
    rcases hs with hs | hs
    · exact Or.inl (subs_pid_pos L bl t s h.2.1 hs)
    · exact Or.inr (subsL_pid_posL L bl ws ts s h.2.2 hs)
  | [], _ :: _, _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, h, _ => by simp only [ltIsL] at h
end

/-- The positions of a subtree are positions of the tree. -/
theorem subs_pos (L : LTree) (bl : Loc) (t s : RTree) (h : ltIs L bl t) (hs : s ∈ t.subs)
    (x : w64) (hx : x ∈ s.pos) : x ∈ t.pos := by
  obtain ⟨s', hs', rfl⟩ := pos_subs s x hx
  exact subs_pid_pos L bl t s' h (subs_trans t s hs s' hs')

/-- A tree's positions: its root's, then its children's. -/
theorem pos_eq (L : LTree) (bl : Loc) (t : RTree) (h : ltIs L bl t) :
    t.pos = t.pid :: posL t.cs := by
  cases t with
  | mk p lf ws cs =>
    cases lf with
    | true => simp only [ltIs] at h; rw [h.2]; simp [pos, posL, RTree.pid, RTree.cs]
    | false => simp [pos, RTree.pid, RTree.cs]

mutual
/-- **The frame of a tree's walk.** -/
theorem ltIs_frame (L L' : LTree) (bl : Loc) : ∀ t : RTree, ltIs L bl t →
    (∀ q ∈ t.pos, L' bl q = L bl q) → ltIs L' bl t
  | .mk p true ws cs, h, hfr => by
    simp only [ltIs] at h ⊢
    rw [hfr p (by simp [pos])]; exact h
  | .mk p false ws cs, h, hfr => by
    simp only [ltIs] at h ⊢
    rw [hfr p (by simp [pos])]
    exact ⟨h.1, ltIsL_frame L L' bl ws cs h.2 (fun q hq => hfr q (by simp [pos, hq]))⟩
theorem ltIsL_frame (L L' : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree),
    ltIsL L bl ws cs → (∀ q ∈ posL cs, L' bl q = L bl q) → ltIsL L' bl ws cs
  | [], [], _, _ => by simp only [ltIsL]
  | w :: ws, t :: ts, h, hfr => by
    simp only [ltIsL] at h ⊢
    exact ⟨h.1, ltIs_frame L L' bl t h.2.1 (fun q hq => hfr q (by simp [posL, hq])),
      ltIsL_frame L L' bl ws ts h.2.2 (fun q hq => hfr q (by simp [posL, hq]))⟩
  | [], _ :: _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], h, _ => by simp only [ltIsL] at h
end

/-! ## Helpers: the surgery's positions -/

mutual
theorem pos_rep_S (p : w64) (S : w64 → Prop) (u : RTree) : ∀ (t : RTree) (x : w64),
    repOK p S t → x ∈ (rep p u t).pos → S x → x ∈ u.pos
  | .mk q lf ws cs, x, hok, hx, hS => by
    simp only [rep] at hx
    split at hx
    · exact hx
    · next hqp =>
      simp only [repOK] at hok
      rcases hok with hok | ⟨hq, hok⟩
      · exact absurd hok hqp
      cases lf with
      | true =>
        simp only [pos, List.mem_singleton] at hx; subst hx; exact absurd hS hq
      | false =>
        simp only [pos, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd hS hq
        · exact posL_rep_S p S u cs x hok hx hS
theorem posL_rep_S (p : w64) (S : w64 → Prop) (u : RTree) : ∀ (cs : List RTree) (x : w64),
    repOKL p S cs → x ∈ posL (repL p u cs) → S x → x ∈ u.pos
  | [], x, _, hx, _ => by simp [repL, posL] at hx
  | t :: ts, x, hok, hx, hS => by
    simp only [repOKL] at hok
    simp only [repL, posL, List.mem_append] at hx
    rcases hx with hx | hx
    · exact pos_rep_S p S u t x hok.1 hx hS
    · exact posL_rep_S p S u ts x hok.2 hx hS
end

mutual
theorem pos_rep_has (L : LTree) (bl : Loc) (p : w64) (u : RTree) : ∀ (t s : RTree),
    ltIs L bl t → s ∈ t.subs → s.pid = p → ∀ x ∈ u.pos, x ∈ (rep p u t).pos
  | .mk q lf ws cs, s, h, hs, hsp, x, hx => by
    simp only [rep]
    split
    · exact hx
    · next hqp =>
      simp only [subs, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact absurd hsp hqp
      cases lf with
      | true => simp only [ltIs] at h; rw [h.2] at hs; simp [subsL] at hs
      | false =>
        simp only [ltIs] at h
        simp only [pos, List.mem_cons]
        exact Or.inr (posL_rep_has L bl p u ws cs s h.2 hs hsp x hx)
theorem posL_rep_has (L : LTree) (bl : Loc) (p : w64) (u : RTree) : ∀ (ws : List WEntry)
    (cs : List RTree) (s : RTree), ltIsL L bl ws cs → s ∈ subsL cs → s.pid = p →
    ∀ x ∈ u.pos, x ∈ posL (repL p u cs)
  | [], [], s, _, hs, _, _, _ => by simp [subsL] at hs
  | w :: ws, t :: ts, s, h, hs, hsp, x, hx => by
    simp only [ltIsL] at h
    simp only [subsL, List.mem_append] at hs
    simp only [repL, posL, List.mem_append]
    rcases hs with hs | hs
    · exact Or.inl (pos_rep_has L bl p u t s h.2.1 hs hsp x hx)
    · exact Or.inr (posL_rep_has L bl p u ws ts s h.2.2 hs hsp x hx)
  | [], _ :: _, _, h, _, _, _, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, h, _, _, _, _ => by simp only [ltIsL] at h
end

/-! ## Helpers: lists of children -/

theorem ltIsL_append (L : LTree) (bl : Loc) : ∀ (ws1 ws2 : List WEntry) (cs1 cs2 : List RTree),
    ltIsL L bl ws1 cs1 → ltIsL L bl ws2 cs2 → ltIsL L bl (ws1 ++ ws2) (cs1 ++ cs2)
  | [], _, [], _, _, h2 => h2
  | w :: ws, ws2, t :: ts, cs2, h1, h2 => by
    simp only [ltIsL] at h1
    simp only [List.cons_append, ltIsL]
    exact ⟨h1.1, h1.2.1, ltIsL_append L bl ws ws2 ts cs2 h1.2.2 h2⟩
  | [], _, _ :: _, _, h, _ => by simp only [ltIsL] at h
  | _ :: _, _, [], _, h, _ => by simp only [ltIsL] at h

theorem ltIsL_append_inv (L : LTree) (bl : Loc) : ∀ (ws1 ws2 : List WEntry) (cs : List RTree),
    ltIsL L bl (ws1 ++ ws2) cs →
    ∃ cs1 cs2, cs = cs1 ++ cs2 ∧ ltIsL L bl ws1 cs1 ∧ ltIsL L bl ws2 cs2
  | [], _, cs, h => ⟨[], cs, rfl, by simp only [ltIsL], h⟩
  | w :: ws, ws2, t :: ts, h => by
    simp only [List.cons_append, ltIsL] at h
    obtain ⟨cs1, cs2, rfl, h1, h2⟩ := ltIsL_append_inv L bl ws ws2 ts h.2.2
    exact ⟨t :: cs1, cs2, rfl, ⟨h.1, h.2.1, h1⟩, h2⟩
  | _ :: _, _, [], h => by simp only [List.cons_append, ltIsL] at h

theorem lvsL_append (cs1 cs2 : List RTree) : lvsL (cs1 ++ cs2) = lvsL cs1 ++ lvsL cs2 := by
  induction cs1 with
  | nil => rfl
  | cons t ts ih => simp [lvsL, ih]

theorem posL_append (cs1 cs2 : List RTree) : posL (cs1 ++ cs2) = posL cs1 ++ posL cs2 := by
  induction cs1 with
  | nil => rfl
  | cons t ts ih => simp [posL, ih]

theorem dpsL_append (d : Nat) (cs1 cs2 : List RTree) :
    dpsL d (cs1 ++ cs2) = dpsL d cs1 ++ dpsL d cs2 := by
  induction cs1 with
  | nil => rfl
  | cons t ts ih => simp [dpsL, ih]

theorem htL_append (cs1 cs2 : List RTree) : htL (cs1 ++ cs2) = max (htL cs1) (htL cs2) := by
  induction cs1 with
  | nil => simp [htL]
  | cons t ts ih => simp only [List.cons_append, htL, ih]; omega

mutual
theorem dps_succ : ∀ (t : RTree) (d x : Nat), x ∈ t.dps d → x + 1 ∈ t.dps (d + 1)
  | .mk p true ws cs, d, x, h => by simp only [dps, List.mem_singleton] at h ⊢; omega
  | .mk p false ws cs, d, x, h => by
    simp only [dps] at h ⊢; exact dpsL_succ cs (d + 1) x h
theorem dpsL_succ : ∀ (cs : List RTree) (d x : Nat), x ∈ dpsL d cs → x + 1 ∈ dpsL (d + 1) cs
  | [], d, x, h => by simp [dpsL] at h
  | t :: ts, d, x, h => by
    simp only [dpsL, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (dps_succ t d x h)
    · exact Or.inr (dpsL_succ ts d x h)
end

theorem split1 : ∀ (l : List WEntry) (k : Nat) (a : WEntry), l[k]? = some a →
    ∃ pre post, l = pre ++ a :: post ∧ pre.length = k
  | [], _, _, h => by simp at h
  | x :: l, 0, a, h => by simp at h; exact ⟨[], l, by simp [h], rfl⟩
  | x :: l, k + 1, a, h => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨pre, post, rfl, hl⟩ := split1 l k a h
    exact ⟨x :: pre, post, rfl, by simp [hl]⟩

theorem split2 (l : List WEntry) (k : Nat) (a b : WEntry) (ha : l[k]? = some a)
    (hb : l[k + 1]? = some b) : ∃ pre post, l = pre ++ a :: b :: post ∧ pre.length = k := by
  obtain ⟨pre, post, rfl, hl⟩ := split1 l k a ha
  cases post with
  | nil => subst hl; simp at hb
  | cons y post =>
    subst hl
    rw [List.getElem?_append_right (by omega)] at hb
    simp at hb; subst hb
    exact ⟨pre, post, rfl, rfl⟩

/-! ## Helpers: the shape at a position, occurrences -/

theorem ltIs_node (L : LTree) (bl : Loc) (s : RTree) (p : w64) (lf : Bool) (ws : List WEntry)
    (h : ltIs L bl s) (hp : s.pid = p) (hL : L bl p = some (lf, ws)) :
    ∃ cs, s = mk p lf ws cs ∧ (lf = true → cs = []) ∧ (lf = false → ltIsL L bl ws cs) := by
  cases s with
  | mk q lf' ws' cs =>
    simp only [RTree.pid] at hp
    subst hp
    cases lf' <;> simp only [ltIs] at h <;> rw [hL] at h <;> obtain ⟨h1, h2⟩ := h <;>
      cases h1 <;> exact ⟨cs, rfl, by simp_all, by simp_all⟩

/-- **The surgery keeps the data, height, depths and positions** when `u` keeps those of the
subtree `s0` at `P` (but the position `gone`). -/
theorem rep_kept (L L' : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t) (P : w64)
    (S : w64 → Prop) (u s0 : RTree) (gone : w64)
    (hL : ∀ q, ¬ S q → L' bl q = L bl q) (hu : ltIs L' bl u) (hup : u.pid = P)
    (hs0 : s0 ∈ t.subs) (hs0l : ltIs L bl s0) (hs0p : s0.pid = P)
    (hok : repOK P S t) (hgone : S gone)
    (hlv : u.lvs.flatten = s0.lvs.flatten) (hht : u.ht ≤ s0.ht)
    (hdp : ∀ k x, x ∈ u.dps k → x ∈ s0.dps k)
    (hpos1 : ∀ x ∈ u.pos, x ∈ s0.pos ∧ x ≠ gone) (hpos2 : ∀ x ∈ s0.pos, x ≠ gone → x ∈ u.pos) :
    ltIs L' bl (rep P u t) ∧ rtKept t (rep P u t) gone 0 := by
  have hdet : ∀ s, ltIs L bl s → s.pid = P → s = s0 := fun s hs hp =>
    ltIs_det L bl s s0 hs hs0l (by rw [hp, hs0p])
  refine ⟨ltIs_rep L L' bl P S u hL hu hup t ht hok, RTree.pid_rep P u hup t, ?_, ?_, ?_, ?_, ?_⟩
  · exact lvs_rep L bl P u (fun s hs hp => by rw [hdet s hs hp]; exact hlv) t ht
  · exact ht_rep L bl P u (fun s hs hp => by rw [hdet s hs hp]; exact hht) t ht
  · intro D hD x hx
    rw [Nat.sub_zero]
    exact dps_rep L bl P u D (fun s k hs hp hsD y hy => by
      rw [hdet s hs hp] at hsD; exact hsD y (hdp k y hy)) t 0 ht hD x hx
  · intro x hx
    rcases pos_rep P u t x hx with h | h
    · refine ⟨h, fun hxg => ?_⟩
      subst hxg
      exact (hpos1 x (pos_rep_S P S u t x hok hx hgone)).2 rfl
    · exact ⟨subs_pos L bl t s0 ht hs0 x (hpos1 x h).1, (hpos1 x h).2⟩
  · intro x hx hxg
    rcases pos_rep_back L bl P u t x ht hx with h | ⟨s, hs, hp, hxs⟩
    · exact h
    · rw [hdet s hs hp] at hxs
      exact pos_rep_has L bl P u t s0 ht hs0 hs0p x (hpos2 x hxs hxg)

theorem frame_kept (L L' : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t) (gone : w64)
    (hfr : ∀ q ∈ t.pos, L' bl q = L bl q) (hg : gone ∉ t.pos) :
    ltIs L' bl t ∧ rtKept t t gone 0 :=
  ⟨ltIs_frame L L' bl t ht hfr, rfl, rfl, Nat.le_refl _,
    fun D hD x hx => by rw [Nat.sub_zero]; exact hD x hx,
    fun x hx => ⟨hx, fun h => hg (h ▸ hx)⟩, fun x hx _ => hx⟩

/-- **Below the subtree at `P`, the positions `T` (each a child only of `P`) occur only at a
subtree's root, and `P` not at all** (a tree does not contain itself strictly). -/
theorem avoid (L : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t) (P : w64) (T : w64 → Prop)
    (hedge : ∀ x c, edge t x c → T c → x = P) (s0 : RTree) (hs0l : ltIs L bl s0)
    (hs0p : s0.pid = P) (c : RTree) (hc : c ∈ t.subs) (hcs : sz c < sz s0) :
    ∀ q ∈ c.pos, q ≠ P ∧ (T q → q = c.pid) := by
  have hcl := ltIs_subs L bl t c ht hc
  have noP : ∀ y ∈ c.subs, y.pid ≠ P := by
    intro y hy hyp
    have := ltIs_det L bl y s0 (ltIs_subs L bl c y hcl hy) hs0l (by rw [hyp, hs0p])
    subst this
    have := sz_subs c y hy; omega
  intro q hq
  obtain ⟨y, hy, rfl⟩ := pos_subs c q hq
  refine ⟨noP y hy, fun hT => ?_⟩
  rcases sub_edge L bl c y hcl hy with rfl | ⟨z, hz, he⟩
  · rfl
  · exact absurd (hedge _ _ (edge_mono t c hc _ _ he) hT) (noP z hz)

theorem avoidL (L : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t) (P : w64) (T : w64 → Prop)
    (hedge : ∀ x c, edge t x c → T c → x = P) (s0 : RTree) (hs0l : ltIs L bl s0)
    (hs0p : s0.pid = P) (cs : List RTree)
    (hcs : ∀ c ∈ cs, c ∈ t.subs ∧ sz c < sz s0 ∧ ¬ T c.pid) :
    ∀ q ∈ posL cs, q ≠ P ∧ ¬ T q := by
  intro q hq
  rw [mem_posL] at hq
  obtain ⟨c, hc, hq⟩ := hq
  obtain ⟨h1, h2, h3⟩ := hcs c hc
  have := avoid L bl t ht P T hedge s0 hs0l hs0p c h1 h2 q hq
  exact ⟨this.1, fun hT => h3 (this.2 hT ▸ hT)⟩

/-- With no subtree at `P`, no position of `T` (not the root) occurs. -/
theorem absent (L : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t) (P : w64) (T : w64 → Prop)
    (hedge : ∀ x c, edge t x c → T c → x = P) (hroot : ¬ T t.pid)
    (hno : ∀ s ∈ t.subs, s.pid ≠ P) : ∀ q ∈ t.pos, q ≠ P ∧ ¬ T q := by
  intro q hq
  obtain ⟨y, hy, rfl⟩ := pos_subs t q hq
  refine ⟨hno y hy, fun hT => ?_⟩
  rcases sub_edge L bl t y ht hy with rfl | ⟨z, hz, he⟩
  · exact hroot hT
  · exact hno z hz (hedge _ _ he hT)

mutual
theorem repOK_of (L : LTree) (bl : Loc) (t : RTree) (P : w64) (T : w64 → Prop)
    (hedge : ∀ x c, edge t x c → T c → x = P) :
    ∀ c : RTree, c ∈ t.subs → ltIs L bl c → (c.pid = P ∨ ¬ T c.pid) →
      repOK P (fun q => q = P ∨ T q) c
  | .mk q lf ws cs, hc, hl, hq => by
    simp only [repOK]
    by_cases hqP : q = P
    · exact Or.inl hqP
    · right
      simp only [RTree.pid] at hq
      refine ⟨fun h => h.elim hqP (hq.resolve_left hqP), ?_⟩
      cases lf with
      | true => simp only [ltIs] at hl; rw [hl.2]; simp only [repOKL]
      | false =>
        simp only [ltIs] at hl
        exact repOKL_of L bl t P T hedge ws cs hl.2 (fun c' hc' =>
          ⟨subs_trans t _ hc c' (child_mem_subs q false ws cs c' hc' c' (self_mem_subs c')),
            fun hT => hqP (hedge q c'.pid ⟨_, hc, rfl, rfl, List.mem_map_of_mem hc'⟩ hT)⟩)
theorem repOKL_of (L : LTree) (bl : Loc) (t : RTree) (P : w64) (T : w64 → Prop)
    (hedge : ∀ x c, edge t x c → T c → x = P) :
    ∀ (ws : List WEntry) (cs : List RTree), ltIsL L bl ws cs →
      (∀ c ∈ cs, c ∈ t.subs ∧ ¬ T c.pid) → repOKL P (fun q => q = P ∨ T q) cs
  | [], [], _, _ => by simp only [repOKL]
  | w :: ws, c :: cs, h, hc => by
    simp only [ltIsL] at h
    simp only [repOKL]
    have := hc c (List.mem_cons_self ..)
    exact ⟨repOK_of L bl t P T hedge c this.1 h.2.1 (Or.inr this.2),
      repOKL_of L bl t P T hedge ws cs h.2.2 (fun c' h' => hc c' (List.mem_cons_of_mem _ h'))⟩
  | [], _ :: _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], h, _ => by simp only [ltIsL] at h
end


theorem pos_mk_br (p : w64) (ws : List WEntry) (cs : List RTree) :
    (mk p false ws cs).pos = p :: posL cs := rfl

theorem posL_cons (t : RTree) (ts : List RTree) : posL (t :: ts) = t.pos ++ posL ts := rfl

theorem nodup_split2 (pre post : List WEntry) (a b : WEntry)
    (h : ((pre ++ a :: b :: post).map WEntry.pgid).Nodup) :
    ∀ w ∈ pre ++ post, w.pgid ≠ a.pgid ∧ w.pgid ≠ b.pgid := by
  rw [List.map_append, List.nodup_append] at h
  obtain ⟨-, h2, h3⟩ := h
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact ⟨h3 _ (List.mem_map_of_mem hw) _ (by simp), h3 _ (List.mem_map_of_mem hw) _ (by simp)⟩
  · have hm : w.pgid ∈ post.map WEntry.pgid := List.mem_map_of_mem hw
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at h2
    exact ⟨fun he => h2.1 (Or.inr (he ▸ hm)), fun he => h2.2.1 (he ▸ hm)⟩

theorem nodup_split1 (pre post : List WEntry) (a : WEntry)
    (h : ((pre ++ a :: post).map WEntry.pgid).Nodup) :
    ∀ w ∈ pre ++ post, w.pgid ≠ a.pgid := by
  rw [List.map_append, List.nodup_append] at h
  obtain ⟨-, h2, h3⟩ := h
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact h3 _ (List.mem_map_of_mem hw) _ (by simp)
  · have hm : w.pgid ∈ post.map WEntry.pgid := List.mem_map_of_mem hw
    simp only [List.map_cons, List.nodup_cons] at h2
    exact fun he => h2.1 (he ▸ hm)

/-- The children of `s0 = mk P lf ws cs` (a subtree of `t`) whose positions are not in `T`
avoid `P` and `T`. -/
theorem kids_avoid (L : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t) (P : w64)
    (T : w64 → Prop) (hedge : ∀ x c, edge t x c → T c → x = P) (lf : Bool) (ws : List WEntry)
    (cs : List RTree) (hs0 : mk P lf ws cs ∈ t.subs) (hs0l : ltIs L bl (mk P lf ws cs))
    (cs' : List RTree) (hsub : ∀ c ∈ cs', c ∈ cs) (hT : ∀ c ∈ cs', ¬ T c.pid) :
    ∀ q ∈ posL cs', q ≠ P ∧ ¬ T q :=
  avoidL L bl t ht P T hedge _ hs0l rfl cs' (fun c hc =>
    ⟨subs_trans t _ hs0 c (child_mem_subs P lf ws cs c (hsub c hc) c (self_mem_subs c)),
      sz_child P lf ws cs c (hsub c hc), hT c hc⟩)

/-- The grandchildren under a branch child `a = mk x false wa ca` (`x ≠ P`) of `s0`. -/
theorem gkids_avoid (L : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t) (P : w64)
    (T : w64 → Prop) (hedge : ∀ x c, edge t x c → T c → x = P) (lf : Bool) (ws : List WEntry)
    (cs : List RTree) (hs0 : mk P lf ws cs ∈ t.subs) (hs0l : ltIs L bl (mk P lf ws cs))
    (x : w64) (wa : List WEntry) (ca : List RTree) (ha : mk x false wa ca ∈ cs) (hxP : x ≠ P) :
    ∀ q ∈ posL ca, q ≠ P ∧ ¬ T q := by
  have has : mk x false wa ca ∈ t.subs :=
    subs_trans t _ hs0 _ (child_mem_subs P lf ws cs _ ha _ (self_mem_subs _))
  refine avoidL L bl t ht P T hedge _ hs0l rfl ca (fun c hc => ⟨?_, ?_, ?_⟩)
  · exact subs_trans t _ has c (child_mem_subs x false wa ca c hc c (self_mem_subs c))
  · have := sz_child x false wa ca c hc
    have := sz_child P lf ws cs _ ha
    omega
  · exact fun hT => hxP (hedge x c.pid ⟨_, has, rfl, rfl, List.mem_map_of_mem hc⟩ hT)

/-- **The merge** of `P`'s children `k` (position `A`) and `k + 1` (`R`), of one kind `lf`
(`P`'s entries' positions distinct, `hnd`: else a second entry at `A` would see the merged
node twice). -/
theorem rt_merge (L L' : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t)
    (P A R : w64) (k : Nat) (wsP wsA wsR : List WEntry) (lf : Bool) (wa wr : WEntry)
    (hPA : P ≠ A) (hPR : P ≠ R) (hAR : A ≠ R)
    (hP : L bl P = some (false, wsP)) (hwa : wsP[k]? = some wa) (hwr : wsP[k + 1]? = some wr)
    (hnd : (wsP.map WEntry.pgid).Nodup)
    (hA : wa.pgid = A) (hR : wr.pgid = R)
    (hLA : L bl A = some (lf, wsA)) (hLR : L bl R = some (lf, wsR))
    (h'P : L' bl P = some (false, wsP.eraseIdx (k + 1)))
    (h'A : L' bl A = some (lf, wsA ++ wsR))
    (hfr : ∀ q, q ≠ P → q ≠ A → q ≠ R → L' bl q = L bl q)
    (hroot : t.pid ≠ A ∧ t.pid ≠ R) (hedge : ∀ x c, edge t x c → (c = A ∨ c = R) → x = P) :
    ∃ t', ltIs L' bl t' ∧ rtKept t t' R 0 := by
  have hfr' : ∀ q, q ≠ P → ¬ (q = A ∨ q = R) → L' bl q = L bl q :=
    fun q h1 h2 => hfr q h1 (fun h => h2 (Or.inl h)) (fun h => h2 (Or.inr h))
  by_cases hex : ¬ ∃ s0 ∈ t.subs, s0.pid = P
  · have hno : ∀ s ∈ t.subs, s.pid ≠ P := fun s hs hp => hex ⟨s, hs, hp⟩
    have hab := absent L bl t ht P _ hedge (by rintro (h | h) <;> first | exact hroot.1 h | exact hroot.2 h) hno
    exact ⟨t, frame_kept L L' bl t ht R (fun q hq => hfr' q (hab q hq).1 (hab q hq).2)
      (fun h => (hab R h).2 (Or.inr rfl))⟩
  obtain ⟨s0, hs0, hs0p⟩ := Classical.not_not.mp hex
  have hs0l := ltIs_subs L bl t s0 ht hs0
  obtain ⟨wpre, wpost, rfl, hlen⟩ := split2 wsP k wa wr hwa hwr
  have hnd' := nodup_split2 wpre wpost wa wr hnd
  rw [hA, hR] at hnd'
  obtain ⟨cs0, rfl, -, hcs0⟩ := ltIs_node L bl s0 P false _ hs0l hs0p hP
  have hcs0 := hcs0 rfl
  obtain ⟨cpre, c2, rfl, hpre, hc2⟩ := ltIsL_append_inv L bl wpre _ cs0 hcs0
  obtain ⟨a, r, cpost, rfl⟩ : ∃ a r cpost, c2 = a :: r :: cpost := by
    match c2, hc2 with
    | a :: r :: cpost, _ => exact ⟨a, r, cpost, rfl⟩
    | [], h => simp only [ltIsL] at h
    | [_], h => simp [ltIsL] at h
  simp only [ltIsL] at hc2
  obtain ⟨hap, hal, hrp, hrl, hpost⟩ := hc2
  obtain ⟨csA, rfl, hA1, hA2⟩ := ltIs_node L bl a A lf wsA hal (by rw [hap, hA]) hLA
  obtain ⟨csR, rfl, hR1, hR2⟩ := ltIs_node L bl r R lf wsR hrl (by rw [hrp, hR]) hLR
  let T : w64 → Prop := fun q => q = A ∨ q = R
  -- the children kept avoid `P`, `A`, `R`
  have hmem : ∀ c ∈ cpre ++ cpost, c ∈ cpre ++ mk A lf wsA csA :: mk R lf wsR csR :: cpost := by
    intro c hc; simp only [List.mem_append, List.mem_cons] at hc ⊢; grind
  have hpid : ∀ c ∈ cpre ++ cpost, ∃ w ∈ wpre ++ wpost, c.pid = w.pgid := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨-, w, hw, h⟩ := ltIsL_mem L bl _ _ hpre c hc
      exact ⟨w, List.mem_append_left _ hw, h⟩
    · obtain ⟨-, w, hw, h⟩ := ltIsL_mem L bl _ _ hpost c hc
      exact ⟨w, List.mem_append_right _ hw, h⟩
  have hkids := kids_avoid L bl t ht P T hedge false _ _ hs0 hs0l (cpre ++ cpost) hmem
    (fun c hc hT => by
      obtain ⟨w, hw, he⟩ := hpid c hc
      rw [he] at hT
      rcases hT with hT | hT
      · exact (hnd' w hw).1 hT
      · exact (hnd' w hw).2 hT)
  have hkpre : ∀ q ∈ posL cpre, q ≠ P ∧ ¬ T q :=
    fun q hq => hkids q (by rw [posL_append]; exact List.mem_append_left _ hq)
  have hkpost : ∀ q ∈ posL cpost, q ≠ P ∧ ¬ T q :=
    fun q hq => hkids q (by rw [posL_append]; exact List.mem_append_right _ hq)
  have hgA : ∀ q ∈ posL csA, q ≠ P ∧ ¬ T q := by
    cases lf
    · exact gkids_avoid L bl t ht P T hedge false _ _ hs0 hs0l A wsA csA (by simp) hPA.symm
    · rw [hA1 rfl]; simp [posL]
  have hgR : ∀ q ∈ posL csR, q ≠ P ∧ ¬ T q := by
    cases lf
    · exact gkids_avoid L bl t ht P T hedge false _ _ hs0 hs0l R wsR csR (by simp) hPR.symm
    · rw [hR1 rfl]; simp [posL]
  have hfrq : ∀ q, q ≠ P ∧ ¬ T q → L' bl q = L bl q := fun q h => hfr' q h.1 h.2
  -- the new subtree at `P`
  let m := mk A lf (wsA ++ wsR) (csA ++ csR)
  let u := mk P false (wpre ++ wa :: wpost) (cpre ++ m :: cpost)
  have hm : ltIs L' bl m := by
    cases lf
    · simp only [m, ltIs]
      exact ⟨h'A, ltIsL_append L' bl _ _ _ _
        (ltIsL_frame L L' bl _ _ (hA2 rfl) (fun q hq => hfrq q (hgA q hq)))
        (ltIsL_frame L L' bl _ _ (hR2 rfl) (fun q hq => hfrq q (hgR q hq)))⟩
    · simp only [m, ltIs]
      exact ⟨h'A, by rw [hA1 rfl, hR1 rfl]; rfl⟩
  have herase : (wpre ++ wa :: wr :: wpost).eraseIdx (k + 1) = wpre ++ wa :: wpost := by
    rw [List.eraseIdx_append_of_length_le (by omega), hlen,
      show k + 1 - k = 0 + 1 by omega]
    rfl
  have hu : ltIs L' bl u := by
    simp only [u, ltIs]
    refine ⟨by rw [h'P, herase], ltIsL_append L' bl _ _ _ _
      (ltIsL_frame L L' bl _ _ hpre (fun q hq => hfrq q (hkpre q hq))) ?_⟩
    simp only [ltIsL]
    exact ⟨by simp only [m, RTree.pid, hA], hm,
      ltIsL_frame L L' bl _ _ hpost (fun q hq => hfrq q (hkpost q hq))⟩
  have hok : repOK P (fun q => q = P ∨ T q) t :=
    repOK_of L bl t P T hedge t (self_mem_subs t) ht
      (Or.inr (by rintro (h | h) <;> first | exact hroot.1 h | exact hroot.2 h))
  have hposA := pos_eq L bl _ hal
  have hposR := pos_eq L bl _ hrl
  have hposm := pos_eq L' bl _ hm
  simp only [m, RTree.pid, RTree.cs] at hposA hposR hposm
  refine (fun H => ⟨_, H.1, H.2⟩) (rep_kept L L' bl t ht P (fun q => q = P ∨ T q) u _ R
    (fun q hq => hfr' q (fun h => hq (Or.inl h)) (fun h => hq (Or.inr h))) hu rfl hs0 hs0l rfl hok
    (Or.inr (Or.inr rfl)) ?_ ?_ ?_ ?_ ?_)
  · cases lf
    · simp [u, m, lvs, lvsL, lvsL_append, List.flatten_append]
    · simp [u, m, lvs, lvsL, lvsL_append, hA1 rfl, hR1 rfl]
  · simp only [u, m, RTree.ht, htL_append, htL]
    omega
  · intro d x hx
    cases lf
    · simp [u, m, dps, dpsL, dpsL_append] at hx ⊢
      grind
    · simp [u, m, dps, dpsL, dpsL_append] at hx ⊢
      grind
  · have hT : ∀ q, ¬ T q ↔ q ≠ A ∧ q ≠ R := fun q => by simp only [T]; constructor <;> grind
    intro x hx
    simp only [u, m] at hx
    rw [pos_mk_br, posL_append, posL_cons, hposm] at hx
    rw [pos_mk_br, posL_append, posL_cons, posL_cons, hposA, hposR]
    have h1 := hkpre x; have h2 := hkpost x; have h3 := hgA x; have h4 := hgR x
    have h5 := hT x
    simp only [List.mem_cons, List.mem_append, posL_append] at hx h1 h2 h3 h4 ⊢
    grind
  · have hT : ∀ q, ¬ T q ↔ q ≠ A ∧ q ≠ R := fun q => by simp only [T]; constructor <;> grind
    intro x hx hxR
    simp only [u, m]
    rw [pos_mk_br, posL_append, posL_cons, hposm]
    rw [pos_mk_br, posL_append, posL_cons, posL_cons, hposA, hposR] at hx
    simp only [List.mem_cons, List.mem_append, posL_append] at hx ⊢
    grind

/-- **The removal** of `P`'s child `k`, the empty leaf at position `E` (`P`'s entries' positions
distinct, `hnd`: else `E` would stay a position). -/
theorem rt_remove (L L' : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t)
    (P E : w64) (k : Nat) (wsP : List WEntry) (we : WEntry) (hPE : P ≠ E)
    (hP : L bl P = some (false, wsP)) (hwe : wsP[k]? = some we) (hE : we.pgid = E)
    (hnd : (wsP.map WEntry.pgid).Nodup)
    (hLE : L bl E = some (true, []))
    (h'P : L' bl P = some (false, wsP.eraseIdx k))
    (hfr : ∀ q, q ≠ P → q ≠ E → L' bl q = L bl q)
    (hroot : t.pid ≠ E) (hedge : ∀ x c, edge t x c → c = E → x = P) :
    ∃ t', ltIs L' bl t' ∧ rtKept t t' E 0 := by
  by_cases hex : ¬ ∃ s0 ∈ t.subs, s0.pid = P
  · have hno : ∀ s ∈ t.subs, s.pid ≠ P := fun s hs hp => hex ⟨s, hs, hp⟩
    have hab := absent L bl t ht P _ hedge hroot hno
    exact ⟨t, frame_kept L L' bl t ht E (fun q hq => hfr q (hab q hq).1 (hab q hq).2)
      (fun h => (hab E h).2 rfl)⟩
  obtain ⟨s0, hs0, hs0p⟩ := Classical.not_not.mp hex
  have hs0l := ltIs_subs L bl t s0 ht hs0
  obtain ⟨wpre, wpost, rfl, hlen⟩ := split1 wsP k we hwe
  have hnd' := nodup_split1 wpre wpost we hnd
  rw [hE] at hnd'
  obtain ⟨cs0, rfl, -, hcs0⟩ := ltIs_node L bl s0 P false _ hs0l hs0p hP
  have hcs0 := hcs0 rfl
  obtain ⟨cpre, c2, rfl, hpre, hc2⟩ := ltIsL_append_inv L bl wpre _ cs0 hcs0
  obtain ⟨e, cpost, rfl⟩ : ∃ e cpost, c2 = e :: cpost := by
    match c2, hc2 with
    | e :: cpost, _ => exact ⟨e, cpost, rfl⟩
    | [], h => simp only [ltIsL] at h
  simp only [ltIsL] at hc2
  obtain ⟨hep, hel, hpost⟩ := hc2
  obtain ⟨cse, rfl, he1, -⟩ := ltIs_node L bl e E true [] hel (by rw [hep, hE]) hLE
  rw [he1 rfl] at hs0 hs0l
  let T : w64 → Prop := fun q => q = E
  have hmem : ∀ c ∈ cpre ++ cpost, c ∈ cpre ++ mk E true [] [] :: cpost := by
    intro c hc; simp only [List.mem_append, List.mem_cons] at hc ⊢; grind
  have hpid : ∀ c ∈ cpre ++ cpost, ∃ w ∈ wpre ++ wpost, c.pid = w.pgid := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨-, w, hw, h⟩ := ltIsL_mem L bl _ _ hpre c hc
      exact ⟨w, List.mem_append_left _ hw, h⟩
    · obtain ⟨-, w, hw, h⟩ := ltIsL_mem L bl _ _ hpost c hc
      exact ⟨w, List.mem_append_right _ hw, h⟩
  have hkids := kids_avoid L bl t ht P T hedge false _ _ hs0 hs0l (cpre ++ cpost) hmem
    (fun c hc hT => by
      obtain ⟨w, hw, he⟩ := hpid c hc
      exact hnd' w hw (he ▸ hT))
  have hkpre : ∀ q ∈ posL cpre, q ≠ P ∧ ¬ T q :=
    fun q hq => hkids q (by rw [posL_append]; exact List.mem_append_left _ hq)
  have hkpost : ∀ q ∈ posL cpost, q ≠ P ∧ ¬ T q :=
    fun q hq => hkids q (by rw [posL_append]; exact List.mem_append_right _ hq)
  have hfrq : ∀ q, q ≠ P ∧ ¬ T q → L' bl q = L bl q := fun q h => hfr q h.1 h.2
  let u := mk P false (wpre ++ wpost) (cpre ++ cpost)
  have herase : (wpre ++ we :: wpost).eraseIdx k = wpre ++ wpost := by
    rw [List.eraseIdx_append_of_length_le (by omega), hlen, Nat.sub_self]
    rfl
  have hu : ltIs L' bl u := by
    simp only [u, ltIs]
    exact ⟨by rw [h'P, herase], ltIsL_append L' bl _ _ _ _
      (ltIsL_frame L L' bl _ _ hpre (fun q hq => hfrq q (hkpre q hq)))
      (ltIsL_frame L L' bl _ _ hpost (fun q hq => hfrq q (hkpost q hq)))⟩
  have hok : repOK P (fun q => q = P ∨ T q) t :=
    repOK_of L bl t P T hedge t (self_mem_subs t) ht (Or.inr hroot)
  refine (fun H => ⟨_, H.1, H.2⟩) (rep_kept L L' bl t ht P (fun q => q = P ∨ T q) u _ E
    (fun q hq => hfr q (fun h => hq (Or.inl h)) (fun h => hq (Or.inr h))) hu rfl hs0 hs0l rfl hok
    (Or.inr rfl) ?_ ?_ ?_ ?_ ?_)
  · simp [u, lvs, lvsL, lvsL_append, List.flatten_append]
  · simp only [u, RTree.ht, htL_append, htL]
    omega
  · intro d x hx
    simp [u, dps, dpsL, dpsL_append] at hx ⊢
    grind
  · intro x hx
    simp only [u] at hx
    rw [pos_mk_br, posL_append] at hx
    rw [pos_mk_br, posL_append, posL_cons]
    have h1 := hkpre x; have h2 := hkpost x
    simp only [T, List.mem_cons, List.mem_append] at hx h1 h2 ⊢
    grind
  · intro x hx hxE
    simp only [u]
    rw [pos_mk_br, posL_append]
    rw [pos_mk_br, posL_append, posL_cons] at hx
    simp only [pos, List.mem_cons, List.mem_append, List.not_mem_nil] at hx ⊢
    grind

/-- **The root collapse**: the root `P`, a branch of one entry (position `C`), takes `C`'s kind
and entries. -/
theorem rt_collapse (L L' : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t)
    (P C : w64) (w0 : WEntry) (lf : Bool) (wsC : List WEntry) (hPC : P ≠ C) (hroot : t.pid = P)
    (hP : L bl P = some (false, [w0])) (hC : w0.pgid = C) (hLC : L bl C = some (lf, wsC))
    (h'P : L' bl P = some (lf, wsC))
    (hfr : ∀ q, q ≠ P → q ≠ C → L' bl q = L bl q)
    (hedge : ∀ x c, edge t x c → c = C → x = P) :
    ∃ t', ltIs L' bl t' ∧ rtKept t t' C 1 := by
  obtain ⟨cs0, rfl, -, hcs0⟩ := ltIs_node L bl t P false _ ht hroot hP
  have hcs0 := hcs0 rfl
  obtain ⟨c, hcp, hcl, hnil⟩ : ∃ c, c.pid = w0.pgid ∧ ltIs L bl c ∧ cs0 = [c] := by
    match cs0, hcs0 with
    | [c], h => simp only [ltIsL] at h; exact ⟨c, h.1, h.2.1, rfl⟩
    | [], h => simp only [ltIsL] at h
    | _ :: _ :: _, h => simp [ltIsL] at h
  subst hnil
  obtain ⟨csC, rfl, hC1, hC2⟩ := ltIs_node L bl c C lf wsC hcl (by rw [hcp, hC]) hLC
  let T : w64 → Prop := fun q => q = C
  have hg : ∀ q ∈ posL csC, q ≠ P ∧ ¬ T q := by
    cases lf
    · exact gkids_avoid L bl _ ht P T hedge false _ _ (self_mem_subs _) ht C wsC csC (by simp)
        hPC.symm
    · rw [hC1 rfl]; simp [posL]
  have hfrq : ∀ q, q ≠ P ∧ ¬ T q → L' bl q = L bl q := fun q h => hfr q h.1 h.2
  have ht' : ltIs L' bl (mk P lf wsC csC) := by
    cases lf
    · simp only [ltIs]
      exact ⟨h'P, ltIsL_frame L L' bl _ _ (hC2 rfl) (fun q hq => hfrq q (hg q hq))⟩
    · simp only [ltIs]
      exact ⟨h'P, hC1 rfl⟩
  have hpos' := pos_eq L' bl _ ht'
  have hposc := pos_eq L bl _ hcl
  simp only [RTree.pid, RTree.cs] at hpos' hposc
  refine ⟨_, ht', rfl, ?_, ?_, ?_, ?_, ?_⟩
  · cases lf
    · simp [lvs, lvsL]
    · simp [lvs, lvsL]
  · simp only [RTree.ht, htL]; omega
  · intro D hD x hx
    cases lf
    · simp only [dps, dpsL, List.append_nil] at hD hx
      have := hD (x + 1) (dpsL_succ csC 1 x hx)
      omega
    · simp only [dps, dpsL, List.append_nil, List.mem_singleton, forall_eq] at hD hx
      omega
  · have hpt : (mk P false [w0] [mk C lf wsC csC]).pos = P :: C :: posL csC := by
      show P :: posL [mk C lf wsC csC] = _
      rw [show posL [mk C lf wsC csC] = (mk C lf wsC csC).pos by simp [posL], hposc]
    intro x hx
    rw [hpos'] at hx
    rw [hpt]
    simp only [List.mem_cons] at hx ⊢
    rcases hx with rfl | hx
    · exact ⟨Or.inl rfl, hPC⟩
    · exact ⟨Or.inr (Or.inr hx), (hg x hx).2⟩
  · have hpt : (mk P false [w0] [mk C lf wsC csC]).pos = P :: C :: posL csC := by
      show P :: posL [mk C lf wsC csC] = _
      rw [show posL [mk C lf wsC csC] = (mk C lf wsC csC).pos by simp [posL], hposc]
    intro x hx hxC
    rw [hpos']
    rw [hpt] at hx
    simp only [List.mem_cons] at hx ⊢
    rcases hx with rfl | rfl | hx
    · exact Or.inl rfl
    · exact absurd rfl hxC
    · exact Or.inr hx

/-- **A step that changes no position of the tree** (the unbalanced flags, the parents, another
bucket's records). -/
theorem rt_frame (L L' : LTree) (bl : Loc) (t : RTree) (ht : ltIs L bl t)
    (hfr : ∀ q ∈ t.pos, L' bl q = L bl q) : ltIs L' bl t :=
  ltIs_frame L L' bl t ht hfr

end steps

end bbolt
end EtcdGrove
end Perennial
