/-
Tree surgery on the logical tree (U8b, `notes/bbolt-proof-plan.md`): every step of `rebalance`
(the root collapse, removing an empty child, merging two siblings) changes the logical tree only
at a few positions `S`, all inside the subtree at one position `p` (the parent's, or the root's),
and replaces that subtree by `u` (`RTree.rep p u`). The walk of the new tree is the old one with the
subtree replaced (`ltIs_rep`), as long as `S` occurs nowhere else (`RTree.repOK`); the leaves'
entries (flattened), the uniformity of the leaves' depth and the height are kept when `u` keeps
them (`lvs_rep`, `dps_rep`, `ht_rep`), and its positions are the old ones or `u`'s (`pos_rep`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rep
variable [GooseExts]

namespace RTree

mutual
/-- `t` with every subtree at position `p` replaced by `u`. -/
def rep (p : w64) (u : RTree) : RTree → RTree
  | mk q lf ws cs => if q = p then u else mk q lf ws (repL p u cs)
def repL (p : w64) (u : RTree) : List RTree → List RTree
  | [] => []
  | t :: ts => rep p u t :: repL p u ts
end

mutual
/-- The positions `S` occur in `t` only inside its subtrees at `p`. -/
def repOK (p : w64) (S : w64 → Prop) : RTree → Prop
  | mk q _ _ cs => q = p ∨ (¬ S q ∧ repOKL p S cs)
def repOKL (p : w64) (S : w64 → Prop) : List RTree → Prop
  | [] => True
  | t :: ts => repOK p S t ∧ repOKL p S ts
end

end RTree

open RTree

theorem RTree.pid_rep (p : w64) (u : RTree) (hu : u.pid = p) (t : RTree) : (rep p u t).pid = t.pid := by
  cases t with
  | mk q lf ws cs =>
    simp only [rep]
    split
    · next h => rw [hu, h]; rfl
    · rfl

theorem ltIsL_length (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree),
    ltIsL L bl ws cs → cs.length = ws.length
  | [], [], _ => rfl
  | _ :: ws, _ :: cs, h => by
    simp only [ltIsL] at h
    simp only [List.length_cons, ltIsL_length L bl ws cs h.2.2]
  | [], _ :: _, h => by simp only [ltIsL] at h
  | _ :: _, [], h => by simp only [ltIsL] at h

mutual
/-- **The walk of the changed tree** (`L'` equals `L` off `S`). -/
theorem ltIs_rep (L L' : LTree) (bl : Loc) (p : w64) (S : w64 → Prop) (u : RTree)
    (hL : ∀ q, ¬ S q → L' bl q = L bl q) (hu : ltIs L' bl u) (hup : u.pid = p) :
    ∀ t : RTree, ltIs L bl t → repOK p S t → ltIs L' bl (rep p u t)
  | .mk q lf ws cs, h, hok => by
    simp only [rep]
    split
    · exact hu
    · next hqp =>
      simp only [repOK] at hok
      rcases hok with hok | ⟨hS, hok⟩
      · exact absurd hok hqp
      cases lf with
      | true =>
        simp only [ltIs] at h ⊢
        rw [hL q hS, h.2]
        exact ⟨h.1, rfl⟩
      | false =>
        simp only [ltIs] at h ⊢
        rw [hL q hS]
        exact ⟨h.1, ltIsL_rep L L' bl p S u hL hu hup ws cs h.2 hok⟩
theorem ltIsL_rep (L L' : LTree) (bl : Loc) (p : w64) (S : w64 → Prop) (u : RTree)
    (hL : ∀ q, ¬ S q → L' bl q = L bl q) (hu : ltIs L' bl u) (hup : u.pid = p) :
    ∀ (ws : List WEntry) (cs : List RTree), ltIsL L bl ws cs → repOKL p S cs →
      ltIsL L' bl ws (repL p u cs)
  | [], [], _, _ => by simp only [repL, ltIsL]
  | w :: ws, t :: ts, h, hok => by
    simp only [ltIsL] at h
    simp only [repOKL] at hok
    simp only [repL, ltIsL]
    exact ⟨by rw [RTree.pid_rep p u hup, h.1], ltIs_rep L L' bl p S u hL hu hup t h.2.1 hok.1,
      ltIsL_rep L L' bl p S u hL hu hup ws ts h.2.2 hok.2⟩
  | [], _ :: _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], h, _ => by simp only [ltIsL] at h
end

mutual
/-- The tree of `L` from a position is unique. -/
theorem ltIs_det (L : LTree) (bl : Loc) : ∀ (s t : RTree), ltIs L bl s → ltIs L bl t →
    s.pid = t.pid → s = t
  | .mk p lf ws cs, .mk q lf' ws' cs', hs, ht, hp => by
    simp only [RTree.pid] at hp
    subst hp
    cases lf <;> cases lf' <;> simp only [ltIs] at hs ht
    · rw [hs.1] at ht; cases ht.1
      rw [ltIsL_det L bl ws cs cs' hs.2 ht.2]
    · rw [hs.1] at ht; cases ht.1
    · rw [hs.1] at ht; cases ht.1
    · rw [hs.1] at ht; cases ht.1
      rw [hs.2, ht.2]
theorem ltIsL_det (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs cs' : List RTree),
    ltIsL L bl ws cs → ltIsL L bl ws cs' → cs = cs'
  | [], [], [], _, _ => rfl
  | w :: ws, t :: ts, t' :: ts', h, h' => by
    simp only [ltIsL] at h h'
    rw [ltIs_det L bl t t' h.2.1 h'.2.1 (by rw [h.1, h'.1]), ltIsL_det L bl ws ts ts' h.2.2 h'.2.2]
  | [], _ :: _, _, h, _ => by simp only [ltIsL] at h
  | [], [], _ :: _, _, h => by simp only [ltIsL] at h
  | _ :: _, [], _, h, _ => by simp only [ltIsL] at h
  | _ :: _, _ :: _, [], _, h => by simp only [ltIsL] at h
end

mutual
/-- **The leaves' entries are kept** when `u` keeps the subtree's at `p`. -/
theorem lvs_rep (L : LTree) (bl : Loc) (p : w64) (u : RTree)
    (hu : ∀ s, ltIs L bl s → s.pid = p → u.lvs.flatten = s.lvs.flatten) :
    ∀ t : RTree, ltIs L bl t → (rep p u t).lvs.flatten = t.lvs.flatten
  | .mk q lf ws cs, h => by
    simp only [rep]
    split
    · next hq => exact hu _ h hq
    · cases lf with
      | true => rfl
      | false =>
        simp only [ltIs] at h
        simp only [lvs]
        exact lvsL_rep L bl p u hu ws cs h.2
theorem lvsL_rep (L : LTree) (bl : Loc) (p : w64) (u : RTree)
    (hu : ∀ s, ltIs L bl s → s.pid = p → u.lvs.flatten = s.lvs.flatten) :
    ∀ (ws : List WEntry) (cs : List RTree), ltIsL L bl ws cs →
      (lvsL (repL p u cs)).flatten = (lvsL cs).flatten
  | [], [], _ => rfl
  | w :: ws, t :: ts, h => by
    simp only [ltIsL] at h
    simp only [repL, lvsL, List.flatten_append]
    rw [lvs_rep L bl p u hu t h.2.1, lvsL_rep L bl p u hu ws ts h.2.2]
  | [], _ :: _, h => by simp only [ltIsL] at h
  | _ :: _, [], h => by simp only [ltIsL] at h
end

mutual
/-- **Uniform leaf depth is kept** when `u` keeps it at every depth the subtree at `p` has it. -/
theorem dps_rep (L : LTree) (bl : Loc) (p : w64) (u : RTree) (D : Nat)
    (hu : ∀ s k, ltIs L bl s → s.pid = p → (∀ x ∈ s.dps k, x = D) → ∀ x ∈ u.dps k, x = D) :
    ∀ (t : RTree) (d : Nat), ltIs L bl t → (∀ x ∈ t.dps d, x = D) → ∀ x ∈ (rep p u t).dps d, x = D
  | .mk q lf ws cs, d, h, hd => by
    simp only [rep]
    split
    · next hq => exact hu _ d h hq hd
    · cases lf with
      | true => exact hd
      | false =>
        simp only [ltIs] at h
        simp only [dps] at hd ⊢
        exact dpsL_rep L bl p u D hu ws cs (d + 1) h.2 hd
theorem dpsL_rep (L : LTree) (bl : Loc) (p : w64) (u : RTree) (D : Nat)
    (hu : ∀ s k, ltIs L bl s → s.pid = p → (∀ x ∈ s.dps k, x = D) → ∀ x ∈ u.dps k, x = D) :
    ∀ (ws : List WEntry) (cs : List RTree) (d : Nat), ltIsL L bl ws cs →
      (∀ x ∈ dpsL d cs, x = D) → ∀ x ∈ dpsL d (repL p u cs), x = D
  | [], [], _, _, _ => by simp [repL, dpsL]
  | w :: ws, t :: ts, d, h, hd => by
    simp only [ltIsL] at h
    simp only [dpsL, List.mem_append] at hd
    simp only [repL, dpsL, List.mem_append]
    rintro x (hx | hx)
    · exact dps_rep L bl p u D hu t d h.2.1 (fun y hy => hd y (Or.inl hy)) x hx
    · exact dpsL_rep L bl p u D hu ws ts d h.2.2 (fun y hy => hd y (Or.inr hy)) x hx
  | [], _ :: _, _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, h, _ => by simp only [ltIsL] at h
end

mutual
/-- **The height does not grow** when `u` is no higher than the subtree at `p`. -/
theorem ht_rep (L : LTree) (bl : Loc) (p : w64) (u : RTree)
    (hu : ∀ s, ltIs L bl s → s.pid = p → u.ht ≤ s.ht) :
    ∀ t : RTree, ltIs L bl t → (rep p u t).ht ≤ t.ht
  | .mk q lf ws cs, h => by
    simp only [rep]
    split
    · next hq => exact hu _ h hq
    · cases lf with
      | true =>
        simp only [ltIs] at h
        rw [h.2]; simp [repL]
      | false =>
        simp only [ltIs] at h
        simp only [ht]
        exact htL_rep L bl p u hu ws cs h.2
theorem htL_rep (L : LTree) (bl : Loc) (p : w64) (u : RTree)
    (hu : ∀ s, ltIs L bl s → s.pid = p → u.ht ≤ s.ht) :
    ∀ (ws : List WEntry) (cs : List RTree), ltIsL L bl ws cs → htL (repL p u cs) ≤ htL cs
  | [], [], _ => Nat.le_refl _
  | w :: ws, t :: ts, h => by
    simp only [ltIsL] at h
    simp only [repL, htL]
    have h1 := ht_rep L bl p u hu t h.2.1
    have h2 := htL_rep L bl p u hu ws ts h.2.2
    omega
  | [], _ :: _, h => by simp only [ltIsL] at h
  | _ :: _, [], h => by simp only [ltIsL] at h
end

mutual
/-- **The positions after**: the old ones, or `u`'s. -/
theorem pos_rep (p : w64) (u : RTree) : ∀ (t : RTree) (x : w64), x ∈ (rep p u t).pos →
    x ∈ t.pos ∨ x ∈ u.pos
  | .mk q lf ws cs, x, hx => by
    simp only [rep] at hx
    split at hx
    · exact Or.inr hx
    · cases lf with
      | true => exact Or.inl hx
      | false =>
        simp only [pos, List.mem_cons] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · rcases posL_rep p u cs x hx with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
theorem posL_rep (p : w64) (u : RTree) : ∀ (cs : List RTree) (x : w64), x ∈ posL (repL p u cs) →
    x ∈ posL cs ∨ x ∈ u.pos
  | [], x, hx => by simp [repL, posL] at hx
  | t :: ts, x, hx => by
    simp only [repL, posL, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · rcases pos_rep p u t x hx with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases posL_rep p u ts x hx with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
end

mutual
/-- **The positions kept**: an old position is a new one, or one of a subtree at `p`. -/
theorem pos_rep_back (L : LTree) (bl : Loc) (p : w64) (u : RTree) : ∀ (t : RTree) (x : w64),
    ltIs L bl t → x ∈ t.pos →
    x ∈ (rep p u t).pos ∨ ∃ s, ltIs L bl s ∧ s.pid = p ∧ x ∈ s.pos
  | .mk q lf ws cs, x, h, hx => by
    simp only [rep]
    split
    · next hq => exact Or.inr ⟨_, h, hq, hx⟩
    · cases lf with
      | true => exact Or.inl hx
      | false =>
        simp only [ltIs] at h
        simp only [pos, List.mem_cons] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · rcases posL_rep_back L bl p u ws cs x h.2 hx with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
theorem posL_rep_back (L : LTree) (bl : Loc) (p : w64) (u : RTree) : ∀ (ws : List WEntry)
    (cs : List RTree) (x : w64), ltIsL L bl ws cs → x ∈ posL cs →
    x ∈ posL (repL p u cs) ∨ ∃ s, ltIs L bl s ∧ s.pid = p ∧ x ∈ s.pos
  | [], [], x, _, hx => by simp [posL] at hx
  | w :: ws, t :: ts, x, h, hx => by
    simp only [ltIsL] at h
    simp only [repL, posL, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · rcases pos_rep_back L bl p u t x h.2.1 hx with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases posL_rep_back L bl p u ws ts x h.2.2 hx with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | [], _ :: _, _, h, _ => by simp only [ltIsL] at h
  | _ :: _, [], _, h, _ => by simp only [ltIsL] at h
end

end rep

end bbolt
end EtcdGrove
end Perennial
