/-
Lemmas for the proofs of the allocation group: the free list (`FreeListG`), the
copy-on-write contexts' `newNode`/`freeNode`, `node.reset`, and the constructors.
-/
import EtcdGrove.Btree.NodeLemmas

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode Iris.BI.BigSepL github_com.google.btree

section lemmas
variable {PROP : Type _} [BI PROP] {A : Type _}

/-- Pop the last element of a `[∗list]`. -/
theorem bigSepL_pop (Φ : A → PROP) (l : List A) (i : Nat) (x : A) (h : l[i]? = some x)
    (hi : i + 1 = l.length) :
    ([∗list] y ∈ l, Φ y) ⊢ ([∗list] y ∈ l.take i, Φ y) ∗ Φ x := by
  have hl : l = l.take i ++ [x] := by
    have hlt : i < l.length := by omega
    rw [List.getElem?_eq_getElem hlt] at h; cases h
    conv => lhs; rw [← List.take_append_drop i l]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, List.drop_of_length_le (by omega)]
  conv => lhs; rw [hl]
  exact bigSepL_snoc.1

theorem drop_eq_cons_of_getElem? (l : List A) (i : Nat) (x : A) (h : l[i]? = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.1 h).1
  rw [List.drop_eq_getElem_cons hlt, List.getElem?_eq_getElem hlt] at *
  cases h; rfl

/-- Push an element at the end of a `[∗list]`. -/
theorem bigSepL_push (Φ : A → PROP) (l : List A) (x : A) :
    ([∗list] y ∈ l, Φ y) ∗ Φ x ⊢ ([∗list] y ∈ l ++ [x], Φ y) :=
  bigSepL_snoc.2

end lemmas

section nodes
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {K : Type}
variable (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc)

/-- Frozen children are (frozen) subtrees. -/
theorem frozenList_ownNodes (dq : DFrac) :
    ∀ (ps : List Loc) (ts : List (Tree (V × K))),
      frozenList o c f less ps ts ⊢ ownNodes o c f less dq ps ts
  | [], [] => by rw [frozenList_nil, ownNodes_nil]
  | p :: ps, t :: ts => by
    rw [frozenList_cons, ownNodes_cons]
    exact sep_mono (ownNode_of_frozen o c f less dq p t) (frozenList_ownNodes dq ps ts)
  | [], _ :: _ => by rw [frozenList]; exact false_elim
  | _ :: _, [] => by rw [frozenList]; exact false_elim

/-- The children of a frozen node: its (persistent) child slice and frozen children. -/
theorem frozen_children (n : Loc) (is : List (V × K)) (cs : List (Tree (V × K))) :
    frozen o c f less n (.node is cs) ⊢
      ∃ (csl : GoSlice) (ps : List Loc),
        structFieldRef (node V) go!"children" n ↦□ csl ∗ csl ↦*□ ps ∗
        frozenList o c f less ps cs := by
  rw [frozen_node]
  iintro ⟨%isl, %csl, %cow, %ps, Hnf, -, -, -, Hcsl, Hfl⟩
  unfold nodeFields
  icases Hnf with ⟨-, -, Hch, -⟩
  iexists csl, ps
  iframe

end nodes

end Btree
end EtcdGrove
end Perennial
