/-
Structural lemmas about the node predicates of `Defs.lean`: unfolding `ownNode`, the
lists of children (`ownNodes`), lending a child out and putting it back, and persistence
of frozen subtrees.
-/
import EtcdGrove.Btree.Defs

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {K : Type}
variable (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc)

/-! ### Unfolding -/

theorem ownNode_node (dq : DFrac) (n : Loc) (is : List (V × K)) (cs : List (Tree (V × K))) :
    ownNode o c f less dq n (.node is cs) =
      iprop(ownedNode o c f less dq n (.node is cs) ∨ frozen o c f less n (.node is cs)) := by
  rw [ownNode]; rfl

theorem ownNode_unfold (dq : DFrac) (n : Loc) (t : Tree (V × K)) :
    ownNode o c f less dq n t ⊣⊢ ownedNode o c f less dq n t ∨ frozen o c f less n t := by
  cases t with
  | node is cs => rw [ownNode_node]; exact .rfl

theorem ownNode_of_owned (dq : DFrac) (n : Loc) (t : Tree (V × K)) :
    ownedNode o c f less dq n t ⊢ ownNode o c f less dq n t := by
  iintro H
  iapply (ownNode_unfold o c f less dq n t).2
  ileft; iexact H

theorem ownNode_of_frozen (dq : DFrac) (n : Loc) (t : Tree (V × K)) :
    frozen o c f less n t ⊢ ownNode o c f less dq n t := by
  iintro H
  iapply (ownNode_unfold o c f less dq n t).2
  iright; iexact H

theorem frozen_node (n : Loc) (is : List (V × K)) (cs : List (Tree (V × K))) :
    frozen o c f less n (.node is cs) =
      iprop(∃ (isl csl : GoSlice) (cow : Loc) (ps : List Loc),
        nodeFields (V := V) n DFrac.discard isl csl cow ∗ ⌜cow ≠ c⌝ ∗
        isCow o cow f less ∗
        isl ↦*□ is.map Prod.fst ∗ csl ↦*□ ps ∗
        frozenList o c f less ps cs) := by
  rw [frozen]

@[simp] theorem ownNodes_nil (dq : DFrac) :
    ownNodes o c f less dq [] [] = iprop(True) := by
  rw [ownNodes]

@[simp] theorem ownNodes_cons (dq : DFrac) (p : Loc) (ps : List Loc) (t : Tree (V × K))
    (ts : List (Tree (V × K))) :
    ownNodes o c f less dq (p :: ps) (t :: ts) =
      iprop(ownNode o c f less dq p t ∗ ownNodes o c f less dq ps ts) := by
  rw [ownNodes]

@[simp] theorem frozenList_nil : frozenList o c f less [] [] = iprop(True) := by
  rw [frozenList]

@[simp] theorem frozenList_cons (p : Loc) (ps : List Loc) (t : Tree (V × K))
    (ts : List (Tree (V × K))) :
    frozenList o c f less (p :: ps) (t :: ts) =
      iprop(frozen o c f less p t ∗ frozenList o c f less ps ts) := by
  rw [frozenList]

/-! ### Persistence of frozen subtrees -/

mutual
theorem frozen_persistent' : ∀ (n : Loc) (t : Tree (V × K)),
    Persistent (frozen o c f less n t)
  | n, .node is cs => by
    rw [frozen]
    have : ∀ ps, Persistent (frozenList o c f less ps cs) := fun ps => frozenList_persistent' ps cs
    infer_instance

theorem frozenList_persistent' : ∀ (ps : List Loc) (ts : List (Tree (V × K))),
    Persistent (frozenList o c f less ps ts)
  | [], [] => by rw [frozenList]; infer_instance
  | p :: ps, t :: ts => by
    rw [frozenList]
    have := frozen_persistent' p t
    have := frozenList_persistent' ps ts
    infer_instance
  | [], _ :: _ => by rw [frozenList]; infer_instance
  | _ :: _, [] => by rw [frozenList]; infer_instance
end

instance frozen_persistent (n : Loc) (t : Tree (V × K)) :
    Persistent (frozen o c f less n t) :=
  frozen_persistent' o c f less n t

instance frozenList_persistent (ps : List Loc) (ts : List (Tree (V × K))) :
    Persistent (frozenList o c f less ps ts) :=
  frozenList_persistent' o c f less ps ts

/-! ### Lists of children -/

theorem ownNodes_length (dq : DFrac) :
    ∀ (ps : List Loc) (ts : List (Tree (V × K))),
      ownNodes o c f less dq ps ts ⊢ ⌜ps.length = ts.length⌝
  | [], [] => by iintro _; ipureintro; rfl
  | p :: ps, t :: ts => by
    rw [ownNodes_cons]
    iintro ⟨_, H⟩
    ihave %h := ownNodes_length dq ps ts $$ H
    ipureintro; simp [h]
  | [], _ :: _ => by rw [ownNodes]; iintro %h; exact h.elim
  | _ :: _, [] => by rw [ownNodes]; iintro %h; exact h.elim

theorem ownNodes_app (dq : DFrac) :
    ∀ (ps1 ps2 : List Loc) (ts1 ts2 : List (Tree (V × K))), ps1.length = ts1.length →
      ownNodes o c f less dq (ps1 ++ ps2) (ts1 ++ ts2) ⊣⊢
        ownNodes o c f less dq ps1 ts1 ∗ ownNodes o c f less dq ps2 ts2
  | [], ps2, [], ts2, _ => by
    simp only [List.nil_append, ownNodes_nil]
    exact true_sep.symm
  | p :: ps1, ps2, t :: ts1, ts2, h => by
    simp only [List.cons_append, ownNodes_cons]
    refine (sep_congr .rfl (ownNodes_app dq ps1 ps2 ts1 ts2 (by simpa using h))).trans ?_
    exact sep_assoc.symm
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

theorem ownNodes_cons_1 (dq : DFrac) (p : Loc) (ps : List Loc) (t : Tree (V × K))
    (ts : List (Tree (V × K))) :
    ownNodes o c f less dq (p :: ps) (t :: ts) ⊢
      ownNode o c f less dq p t ∗ ownNodes o c f less dq ps ts := by
  rw [ownNodes_cons]

theorem ownNodes_cons_2 (dq : DFrac) (p : Loc) (ps : List Loc) (t : Tree (V × K))
    (ts : List (Tree (V × K))) :
    ownNode o c f less dq p t ∗ ownNodes o c f less dq ps ts ⊢
      ownNodes o c f less dq (p :: ps) (t :: ts) := by
  rw [ownNodes_cons]

theorem ownNodes_extract (dq : DFrac) (ps : List Loc) (ts : List (Tree (V × K))) (i : Nat)
    (p : Loc) (t : Tree (V × K)) (hp : ps[i]? = some p) (ht : ts[i]? = some t) :
    ownNodes o c f less dq ps ts ⊣⊢
      ownNode o c f less dq p t ∗ ownNodes o c f less dq (ps.eraseIdx i) (ts.eraseIdx i) := by
  have hpi : i < ps.length := by
    rcases List.getElem?_eq_some_iff.1 hp with ⟨h, _⟩; exact h
  have hti : i < ts.length := by
    rcases List.getElem?_eq_some_iff.1 ht with ⟨h, _⟩; exact h
  have eps : ps = ps.take i ++ p :: ps.drop (i + 1) := by
    rw [List.getElem?_eq_getElem hpi] at hp; cases hp
    rw [List.getElem_cons_drop, List.take_append_drop]
  have ets : ts = ts.take i ++ t :: ts.drop (i + 1) := by
    rw [List.getElem?_eq_getElem hti] at ht; cases ht
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hl : (ps.take i).length = (ts.take i).length := by simp; omega
  rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ]
  conv => lhs; rw [eps, ets]
  constructor
  · iintro H
    icases (ownNodes_app o c f less dq _ _ _ _ hl).1 $$ H with ⟨H1, H2⟩
    icases ownNodes_cons_1 o c f less dq _ _ _ _ $$ H2 with ⟨Hp, H2⟩
    iframe Hp
    iapply (ownNodes_app o c f less dq _ _ _ _ hl).2
    iframe
  · iintro ⟨Hp, H⟩
    icases (ownNodes_app o c f less dq _ _ _ _ hl).1 $$ H with ⟨H1, H2⟩
    iapply (ownNodes_app o c f less dq _ _ _ _ hl).2
    iframe H1
    iapply ownNodes_cons_2
    iframe

theorem ownNodes_fill (dq : DFrac) (ps : List Loc) (ts : List (Tree (V × K))) (i : Nat)
    (p : Loc) (t : Tree (V × K)) (hi : i < ps.length) (hl : ps.length = ts.length) :
    ownNode o c f less dq p t ∗ ownNodes o c f less dq (ps.eraseIdx i) (ts.eraseIdx i) ⊢
      ownNodes o c f less dq (ps.set i p) (ts.set i t) := by
  have hp : (ps.set i p)[i]? = some p := by simp [hi]
  have ht : (ts.set i t)[i]? = some t := by simp [hl ▸ hi]
  refine Entails.trans ?_ (ownNodes_extract o c f less dq _ _ i p t hp ht).2
  rw [List.eraseIdx_set_eq, List.eraseIdx_set_eq]

/-- Put a lent-out child back. -/
theorem ownedNodeHole_fill (n : Loc) (is : List (V × K)) (cs : List (Tree (V × K))) (i : Nat)
    (p : Loc) (t : Tree (V × K)) :
    ownedNodeHole o c f less n is cs i p ∗ ownNode o c f less (DFrac.own 1) p t ⊢
      ownedNode o c f less (DFrac.own 1) n (.node is (cs.set i t)) := by
  unfold ownedNodeHole ownedNode
  iintro ⟨⟨%ps, ⟨%hp, %hl'⟩, Hsh, Hns⟩, Hc⟩
  have hi : i < ps.length := by
    rcases List.getElem?_eq_some_iff.1 hp with ⟨h, _⟩; exact h
  iexists ps
  simp only [Tree.items_node, Tree.children_node]
  iframe Hsh
  have hset : ps.set i p = ps := by
    apply List.ext_getElem?; intro j
    by_cases hj : j = i
    · subst hj
      rw [List.getElem?_eq_getElem hi] at hp; cases hp
      simp [hi]
    · simp [Ne.symm hj]
  rw [show ownNodes o c f less (DFrac.own 1) ps (cs.set i t) =
      ownNodes o c f less (DFrac.own 1) (ps.set i p) (cs.set i t) by rw [hset]]
  iapply ownNodes_fill o c f less _ ps cs i p t hi hl' $$ [Hc Hns]
  iframe

end lemmas

end Btree
end EtcdGrove
end Perennial
