/-
`dereference`'s effect on the writer's records (U9b, `notes/bbolt-proof-plan.md`; pure):
`nodeDerefd r r'` (`n.dereference()` on one node: every key and value copied to persistent heap
bytes, the node's key too, by data unchanged), `derefStep X X'` (some nodes of `X` dereferenced,
nothing else changed; reflexive and transitive), the nodes a call covers (`noView`), and what
the calls need of `X` (`derefPre`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.WOps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section deref
variable [GooseExts]

/-- Two options related by `R` (both none, or both some and related). -/
def optRel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem optRel_refl {α : Type} {R : α → α → Prop} (h : ∀ a, R a a) (o : Option α) :
    optRel R o o := by
  cases o <;> simp [optRel, h]

theorem optRel_trans {α : Type} {R : α → α → Prop} (h : ∀ a b c, R a b → R b c → R a c)
    (o1 o2 o3 : Option α) (h1 : optRel R o1 o2) (h2 : optRel R o2 o3) : optRel R o1 o3 := by
  cases o1 <;> cases o2 <;> cases o3 <;> simp_all [optRel]
  exact h _ _ _ h1 h2

theorem optRel_some_l {α β : Type} {R : α → β → Prop} {a : α} {o : Option β}
    (h : optRel R (some a) o) : ∃ b, o = some b ∧ R a b := by
  cases o <;> simp_all [optRel]

theorem optRel_none_l {α β : Type} {R : α → β → Prop} {o : Option β}
    (h : optRel R (none : Option α) o) : o = none := by
  cases o <;> simp_all [optRel]

theorem optRel_some_r {α β : Type} {R : α → β → Prop} {b : β} {o : Option α}
    (h : optRel R o (some b)) : ∃ a, o = some a ∧ R a b := by
  cases o <;> simp_all [optRel]

/-- The persistent heap source a copy gives. -/
abbrev Src.heap : Src := Src.own DFrac.discard

/-- **`r'` is the node `r` after `n.dereference()`'s copies**: every entry's key and value
copied (persistent heap bytes), the node's key too if it has one; the data, the children, the
struct but its `key` field, unchanged. -/
def nodeDerefd (r r' : NRec) : Prop :=
  r'.nv = { r.nv with key' := r'.nv.key' } ∧ (r'.nv.key' = slice.nil ↔ r.nv.key' = slice.nil) ∧
  r'.ws.map wDat = r.ws.map wDat ∧ (∀ w ∈ r'.ws, w.ks = Src.heap ∧ w.vs = Src.heap) ∧
  r'.ins.length = r.ins.length ∧ r'.cs = r.cs ∧ r'.key = r.key ∧ r'.capOwn = r.capOwn ∧
  r'.ksrc = (if r.nv.key' = slice.nil then r.ksrc else Src.heap)

theorem nodeDerefd_trans {r1 r2 r3 : NRec} (h1 : nodeDerefd r1 r2) (h2 : nodeDerefd r2 r3) :
    nodeDerefd r1 r3 := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, i1, j1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, i2, j2⟩ := h2
  refine ⟨?_, b2.trans b1, c2.trans c1, d2, e2.trans e1, f2.trans f1, g2.trans g1, i2.trans i1, ?_⟩
  · rw [a2, a1]
  · rw [j2, j1]
    by_cases h : r1.nv.key' = slice.nil
    · rw [if_pos (b1.2 h), if_pos h]
    · rw [if_neg (fun h' => h (b1.1 h')), if_neg h]

/-- A node's record kept or dereferenced. -/
def nodeStep (r r' : NRec) : Prop := r' = r ∨ nodeDerefd r r'

theorem nodeStep_refl (r : NRec) : nodeStep r r := Or.inl rfl

theorem nodeStep_trans (r1 r2 r3 : NRec) (h1 : nodeStep r1 r2) (h2 : nodeStep r2 r3) :
    nodeStep r1 r3 := by
  rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
  · exact Or.inl rfl
  · exact Or.inr h2
  · exact Or.inr h1
  · exact Or.inr (nodeDerefd_trans h1 h2)

/-- A bucket's record with some of its nodes dereferenced. -/
def bktStep (B B' : BRec) : Prop :=
  { B' with ns := B.ns } = B ∧ ∀ l, optRel nodeStep (B.ns !! l) (B'.ns !! l)

theorem bktStep_refl (B : BRec) : bktStep B B :=
  ⟨rfl, fun l => optRel_refl nodeStep_refl _⟩

theorem bktStep_trans (B1 B2 B3 : BRec) (h1 : bktStep B1 B2) (h2 : bktStep B2 B3) :
    bktStep B1 B3 := by
  refine ⟨?_, fun l => optRel_trans nodeStep_trans _ _ _ (h1.2 l) (h2.2 l)⟩
  have e1 := h1.1; have e2 := h2.1
  rw [← e1]
  rw [← e2]

/-- **`X'` is `X` with some nodes dereferenced** (by `n.dereference()` calls); nothing else
changed. -/
def derefStep (X X' : WX) : Prop :=
  X'.v = X.v ∧ X'.live = X.live ∧ X'.handles = X.handles ∧ X'.nloc = X.nloc ∧ X'.rl = X.rl ∧
  X'.t.t = X.t.t ∧ X'.t.mv = X.t.mv ∧ X'.t.pm = X.t.pm ∧ X'.t.bufs = X.t.bufs ∧
  X'.t.dead = X.t.dead ∧ ∀ bl, optRel bktStep (X.t.bs !! bl) (X'.t.bs !! bl)

theorem derefStep_refl (X : WX) : derefStep X X :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => optRel_refl bktStep_refl _⟩

theorem derefStep_trans (X1 X2 X3 : WX) (h1 : derefStep X1 X2) (h2 : derefStep X2 X3) :
    derefStep X1 X3 := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, i1, j1, k1, l1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, i2, j2, k2, l2⟩ := h2
  exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1, f2.trans f1,
    g2.trans g1, i2.trans i1, j2.trans j1, k2.trans k1,
    fun bl => optRel_trans bktStep_trans _ _ _ (l1 bl) (l2 bl)⟩

/-- A node record holds no view slice (what `derefOK` asks of a live node). -/
def noView (r : NRec) : Prop := (∀ w ∈ r.ws, w.ks ≠ .view ∧ w.vs ≠ .view) ∧ r.ksrc ≠ .view

theorem noView_derefd {r r' : NRec} (h : nodeDerefd r r') (hk : r.ksrc ≠ .view) : noView r' := by
  obtain ⟨-, -, -, hw, -, -, -, -, hks⟩ := h
  refine ⟨fun w hw' => ⟨by rw [(hw w hw').1]; simp, by rw [(hw w hw').2]; simp⟩, ?_⟩
  rw [hks]; split
  · exact hk
  · simp

theorem noView_step {r r' : NRec} (h : nodeStep r r') (hv : noView r) : noView r' := by
  rcases h with rfl | h
  · exact hv
  · exact noView_derefd h hv.2

/-- The nodes of bucket `B` below the node `n` (through `children`). -/
def subNodes (B : BRec) (n : Loc) : Loc → Prop := fun d => descIn B n d

/-- **What `dereference` needs of `X`** (beyond `liveFresh`): every live node's keys are not
empty (`node.dereference` asserts it), its key nil or not empty, and its children live nodes of
its bucket; every live bucket's cached buckets live buckets, and its root node, if any, a live
node of it below a root (`b.rootNode.root()`). -/
def derefPre (X : WX) : Prop :=
  (∀ bl B l r, X.t.bs !! bl = some B → B.ns !! l = some r → l ∈ X.live →
    (∀ w ∈ r.ws, 0 < w.key.length) ∧ (r.nv.key' = slice.nil ∨ 0 < r.key.length) ∧
    ∀ c ∈ r.cs, c ∈ X.live ∧ (B.ns !! c).isSome) ∧
  (∀ bl B, X.t.bs !! bl = some B → bl ∈ X.live →
    (∀ k c, B.bm !! k = some c → c ∈ X.live ∧ (X.t.bs !! c).isSome) ∧
    (B.bv.rootNode' ≠ null → ∃ rt, nodeRootIn B B.bv.rootNode' rt ∧ rt ∈ X.live))

end deref

end bbolt
end EtcdGrove
end Perennial
