/-
The interval tree's nodes with some `iv` fields lent out (`Visit`/`Stab`/`Contains`: the
visitor gets each overlapping node's `iv`, and keeps it): `ownNodeH K s dq qv p n T ns k`, the
subtree `T` at `n` whose **first `k`** nodes overlapping the query `qv` (in order) have their
`iv` lent out, `ns` those nodes in order (`Visit` of a visitor that goes on lends all of them,
`k` the number of overlapping entries; a visitor that stops, `Contains`' at a gap, lends the ones
visited before the stop and the one it stopped at). A subtree with no overlapping entry lends
nothing (`ownNode_holes_nil`), nor does one asked for none (`ownNode_holes_zero`); the lent
fields given back make the subtree whole again (`ownNodeH_fill`). And the visitors' protocols
(`nodeVisitorOk`, `ivVisitorOk`): a visitor that keeps the `iv` it is given, and goes on
(returning `true`, with `I` of the entries so far) or stops (`false`, with `J`). Generic in the
key representation `K` (the auth plan's S2b). Lean-first.
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

/-- The number of entries of a subtree the query overlaps. -/
abbrev nstab (qv : IvlS) (T : RbT Entry) : Nat := (stab qv T.inorder).length

/-- `visit` visits overlapping entries only, in order: a sublist of the stabbed ones, for any
query (the pruning on the subtrees' `max` may skip some for a degenerate one). -/
theorem visitL_sublist (q : IvlS) : ∀ T : RbT Entry, List.Sublist (T.visitL q) (stab q T.inorder)
  | .leaf => List.nil_sublist _
  | .node c l e r => by
    rw [stab_node]
    unfold RbT.visitL
    have hl := visitL_sublist q l
    have hr := visitL_sublist q r
    split
    · rename_i h
      have hne : ¬ ivlCmp q e.1 = 0 := by omega
      simp only [hne, ↓reduceIte, List.append_nil]
      exact hl.trans (List.sublist_append_left _ _)
    · split
      · rename_i h1 h2
        have hne : ¬ ivlCmp q e.1 = 0 := by omega
        simp only [hne, ↓reduceIte, List.append_nil]
        split
        · exact hl.append hr
        · exact List.nil_sublist _
      · rename_i h1 h2
        have h0 : ivlCmp q e.1 = 0 := by omega
        simp only [h0, ↓reduceIte]
        rw [List.append_assoc, List.singleton_append]
        exact hl.append (hr.cons₂ e)

theorem nstab_node (qv : IvlS) (c : RbColor) (l : RbT Entry) (e : Entry) (r : RbT Entry) :
    nstab qv (.node c l e r) = nstab qv l + (if ivlCmp qv e.1 = 0 then 1 else 0) + nstab qv r := by
  unfold nstab
  rw [stab_node]
  simp only [List.length_append]
  split <;> rfl

/-- The first `k` stabbed entries of a node's subtree: the left subtree's first `k`, the node's
entry if it overlaps and the left subtree has fewer than `k`, the right subtree's first
`k - nstab l - (1 or 0)`. -/
theorem take_stab_node (qv : IvlS) (c : RbColor) (l : RbT Entry) (e : Entry) (r : RbT Entry)
    (k : Nat) :
    (stab qv (RbT.node c l e r).inorder).take k =
      (stab qv l.inorder).take k ++
        (if ivlCmp qv e.1 = 0 ∧ nstab qv l < k then [e] else []) ++
        (stab qv r.inorder).take (k - nstab qv l - if ivlCmp qv e.1 = 0 then 1 else 0) := by
  rw [stab_node, List.take_append, List.take_append, List.length_append]
  have hB : (if ivlCmp qv e.1 = 0 then [e] else []).take (k - (stab qv l.inorder).length) =
      if ivlCmp qv e.1 = 0 ∧ nstab qv l < k then [e] else [] := by
    unfold nstab
    by_cases h : ivlCmp qv e.1 = 0
    · simp only [h, _root_.true_and, ↓reduceIte]
      by_cases hk : (stab qv l.inorder).length < k
      · have : k - (stab qv l.inorder).length = (k - (stab qv l.inorder).length - 1) + 1 := by
          omega
        rw [this]; simp [hk]
      · have : k - (stab qv l.inorder).length = 0 := by omega
        rw [this]; simp [hk]
    · simp [h]
  have hl : (if ivlCmp qv e.1 = 0 then [e] else []).length =
      if ivlCmp qv e.1 = 0 then 1 else 0 := by
    split <;> rfl
  rw [hB, hl]
  unfold nstab
  rw [Nat.sub_sub]

end entries

section holes
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]
variable (K : KeyRep (GF := GF))

/-- The subtree at `n` (child of `p`) holding `T`, at `dq`, with the nodes `ns` (in order)
having lent out their `iv` fields, `es` their entries (`Visit` lends the visited nodes': the
overlapping ones in order, for a query that is not empty-and-finite and a visitor that goes
on; a prefix of them for one that stops; some of them, in order, for a degenerate query, whose
descent prunes on the subtrees' `max`). A node is lent or not (`bl`). -/
def ownNodeH (K : KeyRep (GF := GF)) (s : Loc) (dq : DFrac) :
    Loc → Loc → RbT Entry → List Loc → List Entry → IProp GF
  | _, n, .leaf, ns, es => iprop(⌜n = s ∧ ns = [] ∧ es = []⌝)
  | p, n, .node c l e r, ns, es => iprop(∃ (lp rp : Loc) (nsl nsr : List Loc)
      (esl esr : List Entry) (bl : Bool),
      ⌜n ≠ s ∧ n ≠ null ∧ ns = nsl ++ (if bl then [n] else []) ++ nsr ∧
        es = esl ++ (if bl then [e] else []) ++ esr⌝ ∗
      (if bl then iprop(True) else K.ivAt n.[intervalNode, go!"iv"] dq e) ∗
      K.maxAt n.[intervalNode, go!"max"] dq (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{dq} lp ∗
      n.[intervalNode, go!"right"] ↦{dq} rp ∗
      n.[intervalNode, go!"parent"] ↦{dq} p ∗
      n.[intervalNode, go!"c"] ↦{dq} colorW c ∗
      ownNodeH K s dq n lp l nsl esl ∗ ownNodeH K s dq n rp r nsr esr)

theorem ownNodeH_leaf (s : Loc) (dq : DFrac) (p n : Loc) (ns : List Loc) (es : List Entry) :
    ownNodeH K s dq p n .leaf ns es = iprop(⌜n = s ∧ ns = [] ∧ es = []⌝) := by rw [ownNodeH]

theorem ownNodeH_node (s : Loc) (dq : DFrac) (p n : Loc) (c : RbColor)
    (l : RbT Entry) (e : Entry) (r : RbT Entry) (ns : List Loc) (es : List Entry) :
    ownNodeH K s dq p n (.node c l e r) ns es = iprop(∃ (lp rp : Loc) (nsl nsr : List Loc)
      (esl esr : List Entry) (bl : Bool),
      ⌜n ≠ s ∧ n ≠ null ∧ ns = nsl ++ (if bl then [n] else []) ++ nsr ∧
        es = esl ++ (if bl then [e] else []) ++ esr⌝ ∗
      (if bl then iprop(True) else K.ivAt n.[intervalNode, go!"iv"] dq e) ∗
      K.maxAt n.[intervalNode, go!"max"] dq (nodeMax l e r) ∗
      n.[intervalNode, go!"left"] ↦{dq} lp ∗
      n.[intervalNode, go!"right"] ↦{dq} rp ∗
      n.[intervalNode, go!"parent"] ↦{dq} p ∗
      n.[intervalNode, go!"c"] ↦{dq} colorW c ∗
      ownNodeH K s dq n lp l nsl esl ∗ ownNodeH K s dq n rp r nsr esr) := by
  rw [ownNodeH]

/-- One lent node per lent entry. -/
theorem ownNodeH_length (s : Loc) (dq : DFrac) : ∀ (p n : Loc) (T : RbT Entry)
    (ns : List Loc) (es : List Entry),
    ownNodeH K s dq p n T ns es ⊢ ⌜ns.length = es.length⌝
  | p, n, .leaf, ns, es => by
    rw [ownNodeH_leaf]
    iintro %h
    ipureintro; simp [h.2.1, h.2.2]
  | p, n, .node c l e r, ns, es => by
    rw [ownNodeH_node]
    iintro ⟨%lp, %rp, %nsl, %nsr, %esl, %esr, %bl, %Hn, -, -, -, -, -, -, Hl, Hr⟩
    ihave %h1 := ownNodeH_length s dq n lp l nsl esl $$ Hl
    ihave %h2 := ownNodeH_length s dq n rp r nsr esr $$ Hr
    ipureintro
    rw [Hn.2.2.1, Hn.2.2.2]
    simp only [List.length_append, h1, h2]
    cases bl <;> rfl

/-- A subtree lending nothing. -/
theorem ownNode_holes_nil (s : Loc) (dq : DFrac) : ∀ (p n : Loc) (T : RbT Entry),
    ownNode K s dq p n T ⊢ ownNodeH K s dq p n T [] []
  | p, n, .leaf => by
    rw [ownNode_leaf, ownNodeH_leaf]
    iintro %h
    ipureintro; exact ⟨h, rfl, rfl⟩
  | p, n, .node c l e r => by
    rw [ownNode_node, ownNodeH_node]
    iintro ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
    icases ownNode_holes_nil s dq n lp l $$ Hnl with Hnl
    icases ownNode_holes_nil s dq n rp r $$ Hnr with Hnr
    iexists lp, rp, [], [], [], [], false
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    iframe
    ipureintro; exact ⟨Hn.1, Hn.2, trivial, trivial⟩

/-- **The lent `iv` fields given back make the subtree whole.** -/
theorem ownNodeH_fill (s : Loc) (dq : DFrac) : ∀ (p n : Loc) (T : RbT Entry)
    (ns : List Loc) (es : List Entry),
    ownNodeH K s dq p n T ns es ∗
      ([∗list] x ∈ (ns.map fun m => m.[intervalNode, go!"iv"]).zip es, K.ivAt x.1 dq x.2) ⊢
      ownNode K s dq p n T
  | p, n, .leaf, ns, es => by
    rw [ownNodeH_leaf, ownNode_leaf]
    iintro ⟨%h, -⟩
    ipureintro; exact h.1
  | p, n, .node c l e r, ns, es => by
    rw [ownNodeH_node, ownNode_node]
    iintro ⟨⟨%lp, %rp, %nsl, %nsr, %esl, %esr, %bl, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩,
      Hlent⟩
    ihave %h1 := ownNodeH_length K s dq n lp l nsl esl $$ Hnl
    ihave %h2 := ownNodeH_length K s dq n rp r nsr esr $$ Hnr
    obtain ⟨hs, hnn, hns, hes⟩ := Hn
    subst hns hes
    have hl1 : (nsl.map fun m => m.[intervalNode, go!"iv"]).length = esl.length := by
      simp [h1]
    rw [List.map_append, List.map_append,
      List.zip_append (by cases bl <;> simp [hl1]), List.zip_append hl1]
    icases BigSepL.bigSepL_append.1 $$ Hlent with ⟨Hlent, Hlr⟩
    icases BigSepL.bigSepL_append.1 $$ Hlent with ⟨Hll, Hle⟩
    icases ownNodeH_fill s dq n lp l nsl esl $$ [Hnl Hll] with Hnl
    · iframe
    icases ownNodeH_fill s dq n rp r nsr esr $$ [Hnr Hlr] with Hnr
    · iframe
    iexists lp, rp
    iframe
    isplitl []
    · ipureintro; exact ⟨hs, hnn⟩
    cases bl with
    | true =>
      simp only [↓reduceIte, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left]
      icases BigSepL.bigSepL_singleton.1 $$ Hle with Hle
      iexact Hle
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexact Hiv

/-! ## The visitors -/

/-- A node visitor (`visit`'s `nv`) that keeps the `iv` field of each node it is given, records
it in `I` and goes on (returns `true`), or records it in `J` and stops (`false`). It is called
on entries of `S` in order (the entries visited so far and the new one are a sublist of `S`:
what bounds the number of calls, `Union`'s inserts), on a prefix of `S` when the query is not
degenerate (`hq`, `Visit`'s `b = "" ∨ b < e`: `Contains` reads the entries in order). -/
def nodeVisitorOk (K : KeyRep (GF := GF)) (dq : DFrac) (S : List Entry) (hq : Prop) (nv : GoFunc)
    (I J : List (Loc × Entry) → IProp GF) : IProp GF :=
  iprop(□ ∀ (n : Loc) (z : Entry) (acc : List (Loc × Entry)),
    {{ ⌜List.Sublist (acc.map Prod.snd ++ [z]) S ∧ (hq → acc.map Prod.snd ++ [z] <+: S)⌝ ∗ I acc ∗
        K.ivAt n.[intervalNode, go!"iv"] dq z }}
      (App (Val #nv) (Val #n))
    {{ (r : Bool), RET #r; if r then I (acc ++ [(n, z)]) else J (acc ++ [(n, z)]) }})

instance nodeVisitorOk_persistent (dq : DFrac) (S : List Entry) (hq : Prop) (nv : GoFunc)
    (I J : List (Loc × Entry) → IProp GF) : Persistent (nodeVisitorOk K dq S hq nv I J) := by
  unfold nodeVisitorOk; infer_instance

/-- An interval-value visitor (`Visit`'s `ivv`) that keeps each `IntervalValue` pointer it is
given, records it in `I` and goes on, or in `J` and stops; called on the entries of `S` in
order, as `nodeVisitorOk`. -/
def ivVisitorOkK (K : KeyRep (GF := GF)) (dq : DFrac) (S : List Entry) (hq : Prop) (ivv : GoFunc)
    (I J : List (Loc × Entry) → IProp GF) : IProp GF :=
  iprop(□ ∀ (pv : Loc) (z : Entry) (acc : List (Loc × Entry)),
    {{ ⌜List.Sublist (acc.map Prod.snd ++ [z]) S ∧ (hq → acc.map Prod.snd ++ [z] <+: S)⌝ ∗ I acc ∗
        K.ivAt pv dq z }}
      (App (Val #ivv) (Val #pv))
    {{ (r : Bool), RET #r; if r then I (acc ++ [(pv, z)]) else J (acc ++ [(pv, z)]) }})

instance ivVisitorOkK_persistent (dq : DFrac) (S : List Entry) (hq : Prop) (ivv : GoFunc)
    (I J : List (Loc × Entry) → IProp GF) : Persistent (ivVisitorOkK K dq S hq ivv I J) := by
  unfold ivVisitorOkK; infer_instance

/-- An interval-value visitor over string-affine keys that keeps each `IntervalValue` pointer it
is given, records it in `I`, and goes on (the watchable store's: `intervalTree.Visit.spec`, the
string-affine `Visit`); `ivVisitorOkK` for `strKey` with a visitor that never stops
(`ivVisitorOk_K`). -/
def ivVisitorOk (q : Qp) (S : List Entry) (ivv : GoFunc) (I : List (Loc × Entry) → IProp GF) :
    IProp GF :=
  iprop(□ ∀ (pv : Loc) (z : Entry) (acc : List (Loc × Entry)),
    {{ ⌜acc.map Prod.snd ++ [z] <+: S⌝ ∗ I acc ∗ pv ↦{DFrac.own q} ({ Ivl' := affIvl z.1.1 z.1.2, Val' := z.2 } : IntervalValue) }}
      (App (Val #ivv) (Val #pv))
    {{ RET #true; I (acc ++ [(pv, z)]) }})

instance ivVisitorOk_persistent (q : Qp) (S : List Entry) (ivv : GoFunc)
    (I : List (Loc × Entry) → IProp GF) : Persistent (ivVisitorOk q S ivv I) := by
  unfold ivVisitorOk; infer_instance

end holes

end adt
end EtcdGrove
end Perennial
