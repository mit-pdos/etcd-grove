/-
The interval tree's nodes with some `iv` fields lent out (`Visit`/`Stab`: the visitor gets each
overlapping node's `iv`, and keeps it): `ownNodeH s q qv p n T ns`, the subtree `T` at `n` whose
nodes overlapping the query `qv` have their `iv` lent out, `ns` those nodes in order. A subtree
with no overlapping entry lends nothing (`ownNode_holes_nil`); the lent fields given back make
the subtree whole again (`ownNodeH_fill`). And the visitors' protocols (`nodeVisitorOk`,
`ivVisitorOk`): a visitor that keeps the `iv` it is given and goes on. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section entries
variable [ext : FfiSyntax]

/-- The entries a node's subtree stabs: its left subtree's, its own, its right subtree's. -/
theorem stab_node (qv : IvlS) (c : RbColor) (l : RbT Entry) (e : Entry) (r : RbT Entry) :
    stab qv (RbT.node c l e r).inorder =
      stab qv l.inorder ++ (if ivlCmp qv e.1 = 0 then [e] else []) ++ stab qv r.inorder := by
  rw [RbT.inorder_node, stab_append, stab_cons]
  split <;> simp

end entries

section holes
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- The subtree at `n` (child of `p`) holding `T`, at the fraction `q`, whose nodes with an
entry overlapping `qv` have lent out their `iv` field; `ns` those nodes, in order. -/
def ownNodeH (s : Loc) (q : Qp) (qv : IvlS) : Loc → Loc → RbT Entry → List Loc → IProp GF
  | _, n, .leaf, ns => iprop(⌜n = s ∧ ns = []⌝)
  | p, n, .node c l e r, ns => iprop(∃ (lp rp : Loc) (nsl nsr : List Loc),
      ⌜n ≠ s ∧ n ≠ null ∧ ns = nsl ++ (if ivlCmp qv e.1 = 0 then [n] else []) ++ nsr⌝ ∗
      (if ivlCmp qv e.1 = 0 then iprop(True) else
        n.[intervalNode, go!"iv"] ↦{DFrac.own q}
          ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue)) ∗
      n.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
      n.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
      n.[intervalNode, go!"parent"] ↦{DFrac.own q} p ∗
      n.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNodeH s q qv n lp l nsl ∗ ownNodeH s q qv n rp r nsr)

theorem ownNodeH_leaf (s : Loc) (q : Qp) (qv : IvlS) (p n : Loc) (ns : List Loc) :
    ownNodeH (GF := GF) s q qv p n .leaf ns = iprop(⌜n = s ∧ ns = []⌝) := by rw [ownNodeH]

theorem ownNodeH_node (s : Loc) (q : Qp) (qv : IvlS) (p n : Loc) (c : RbColor) (l : RbT Entry)
    (e : Entry) (r : RbT Entry) (ns : List Loc) :
    ownNodeH (GF := GF) s q qv p n (.node c l e r) ns = iprop(∃ (lp rp : Loc) (nsl nsr : List Loc),
      ⌜n ≠ s ∧ n ≠ null ∧ ns = nsl ++ (if ivlCmp qv e.1 = 0 then [n] else []) ++ nsr⌝ ∗
      (if ivlCmp qv e.1 = 0 then iprop(True) else
        n.[intervalNode, go!"iv"] ↦{DFrac.own q}
          ({ Ivl' := affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue)) ∗
      n.[intervalNode, go!"max"] ↦{DFrac.own q} maxW (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{DFrac.own q} lp ∗
      n.[intervalNode, go!"right"] ↦{DFrac.own q} rp ∗
      n.[intervalNode, go!"parent"] ↦{DFrac.own q} p ∗
      n.[intervalNode, go!"c"] ↦{DFrac.own q} colorW c ∗
      ownNodeH s q qv n lp l nsl ∗ ownNodeH s q qv n rp r nsr) := by rw [ownNodeH]

/-- One lent node per stabbed entry. -/
theorem ownNodeH_length (s : Loc) (q : Qp) (qv : IvlS) : ∀ (p n : Loc) (T : RbT Entry)
    (ns : List Loc), ownNodeH (GF := GF) s q qv p n T ns ⊢ ⌜ns.length = (stab qv T.inorder).length⌝
  | p, n, .leaf, ns => by
    rw [ownNodeH_leaf]
    iintro %h
    ipureintro; rw [h.2]; rfl
  | p, n, .node c l e r, ns => by
    rw [ownNodeH_node]
    iintro ⟨%lp, %rp, %nsl, %nsr, %Hn, -, -, -, -, -, -, Hl, Hr⟩
    ihave %h1 := ownNodeH_length s q qv n lp l nsl $$ Hl
    ihave %h2 := ownNodeH_length s q qv n rp r nsr $$ Hr
    ipureintro
    rw [Hn.2.2, stab_node]
    simp only [List.length_append, h1, h2]
    split <;> rfl

/-- A subtree no entry of which overlaps the query lends nothing. -/
theorem ownNode_holes_nil (s : Loc) (q : Qp) (qv : IvlS) : ∀ (p n : Loc) (T : RbT Entry),
    stab qv T.inorder = [] → ownNode (GF := GF) s q p n T ⊢ ownNodeH s q qv p n T []
  | p, n, .leaf, _ => by
    rw [ownNode_leaf, ownNodeH_leaf]
    iintro %h
    ipureintro; exact ⟨h, rfl⟩
  | p, n, .node c l e r, h => by
    rw [stab_node] at h
    simp only [List.append_eq_nil_iff, ite_eq_right_iff, reduceCtorEq, imp_false] at h
    obtain ⟨⟨hl, he⟩, hr⟩ := h
    rw [ownNode_node, ownNodeH_node]
    iintro ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
    icases ownNode_holes_nil s q qv n lp l hl $$ Hnl with Hnl
    icases ownNode_holes_nil s q qv n rp r hr $$ Hnr with Hnr
    iexists lp, rp, [], []
    simp only [he, ↓reduceIte]
    iframe
    ipureintro; exact ⟨Hn.1, Hn.2, rfl⟩

/-- **The lent `iv` fields given back make the subtree whole.** -/
theorem ownNodeH_fill (s : Loc) (q : Qp) (qv : IvlS) : ∀ (p n : Loc) (T : RbT Entry)
    (ns : List Loc),
    ownNodeH (GF := GF) s q qv p n T ns ∗
      ([∗list] x ∈ (ns.map fun m => m.[intervalNode, go!"iv"]).zip (stab qv T.inorder),
        x.1 ↦{DFrac.own q} ({ Ivl' := affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue)) ⊢
      ownNode s q p n T
  | p, n, .leaf, ns => by
    rw [ownNodeH_leaf, ownNode_leaf]
    iintro ⟨%h, -⟩
    ipureintro; exact h.1
  | p, n, .node c l e r, ns => by
    rw [ownNodeH_node, ownNode_node]
    iintro ⟨⟨%lp, %rp, %nsl, %nsr, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩, Hlent⟩
    ihave %h1 := ownNodeH_length s q qv n lp l nsl $$ Hnl
    ihave %h2 := ownNodeH_length s q qv n rp r nsr $$ Hnr
    obtain ⟨hs, hnn, hns⟩ := Hn
    subst hns
    rw [stab_node, List.map_append, List.map_append,
      List.zip_append (by (try split) <;> simp [h1]),
      List.zip_append (by (try split) <;> simp [h1])]
    icases BigSepL.bigSepL_append.1 $$ Hlent with ⟨Hlent, Hlr⟩
    icases BigSepL.bigSepL_append.1 $$ Hlent with ⟨Hll, Hle⟩
    icases ownNodeH_fill s q qv n lp l nsl $$ [Hnl Hll] with Hnl
    · iframe
    icases ownNodeH_fill s q qv n rp r nsr $$ [Hnr Hlr] with Hnr
    · iframe
    iexists lp, rp
    iframe
    isplitl []
    · ipureintro; exact ⟨hs, hnn⟩
    split
    · simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left]
      icases BigSepL.bigSepL_singleton.1 $$ Hle with Hle
      iexact Hle
    · iexact Hiv

/-! ## The visitors -/

/-- A node visitor (`visit`'s `nv`) that keeps the `iv` field of each node it is given, records
it in `I`, and goes on (returns `true`). -/
def nodeVisitorOk (q : Qp) (nv : GoFunc) (I : List (Loc × Entry) → IProp GF) : IProp GF :=
  iprop(□ ∀ (n : Loc) (z : Entry) (acc : List (Loc × Entry)),
    {{ I acc ∗ n.[intervalNode, go!"iv"] ↦{DFrac.own q}
        ({ Ivl' := affIvl z.1.1 z.1.2, Val' := z.2 } : IntervalValue) }}
      (App (Val #nv) (Val #n))
    {{ RET #true; I (acc ++ [(n, z)]) }})

instance nodeVisitorOk_persistent (q : Qp) (nv : GoFunc) (I : List (Loc × Entry) → IProp GF) :
    Persistent (nodeVisitorOk q nv I) := by
  unfold nodeVisitorOk; infer_instance

/-- An interval-value visitor (`Visit`'s `ivv`) that keeps each `IntervalValue` pointer it is
given, records it in `I`, and goes on. -/
def ivVisitorOk (q : Qp) (ivv : GoFunc) (I : List (Loc × Entry) → IProp GF) : IProp GF :=
  iprop(□ ∀ (pv : Loc) (z : Entry) (acc : List (Loc × Entry)),
    {{ I acc ∗ pv ↦{DFrac.own q} ({ Ivl' := affIvl z.1.1 z.1.2, Val' := z.2 } : IntervalValue) }}
      (App (Val #ivv) (Val #pv))
    {{ RET #true; I (acc ++ [(pv, z)]) }})

instance ivVisitorOk_persistent (q : Qp) (ivv : GoFunc) (I : List (Loc × Entry) → IProp GF) :
    Persistent (ivVisitorOk q ivv I) := by
  unfold ivVisitorOk; infer_instance

end holes

end adt
end EtcdGrove
end Perennial
