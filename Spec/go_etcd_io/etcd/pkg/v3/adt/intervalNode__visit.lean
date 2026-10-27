/-
`intervalTree.Len` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
Pending: the interval tree's contract, proved in unit 4 (the tree's proof); until then a
hypothesis of every result that reaches it (`?` in `etc/link-lean-first-adt.txt`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Holes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `x.visit(iv, sentinel, nv)` (internal, `Visit`'s), over the keys `K`, on the subtree at `x`
(child of `p`) holding `Tx` (sorted), at `dq`, for a query at `ivp` (its values holding its keys
at any fractions): calls the visitor on nodes whose entries overlap the query, in order, until
it stops if it does; the visitor keeps their `iv` fields (recorded in `I`, or in `J` when it
stops: `nodeVisitorOk`). Returns whether no visitor stopped; the subtree with the visited nodes'
fields lent out (`ownNodeH`, `ns` the nodes, `es` their entries: a sublist of the overlapping
ones, and, for a query that is not empty-and-finite (`b = ""` or `b < e`), all of them when none
stopped, a non-empty prefix of them else). The visitor is told it is called on the entries of
`S` in order: the entries visited before (`acc`) and this subtree's overlapping ones are a
sublist of `S` (a prefix for such a query). -/
abbrev adt.intervalNode.visit.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (s : Loc) (dq : DFrac) (p x : Loc) (Tx : adt.RbT adt.Entry) (ivp : Loc) (dq' : DFrac)
    (vb ve : val) (db de : DFrac) (b e : GoString) (nv : GoFunc) (S : List adt.Entry)
    (I J : List (Loc × adt.Entry) → IProp GF) (acc : List (Loc × adt.Entry)),
  adt.IvSorted Tx.inorder →
  List.Sublist (acc.map Prod.snd ++ adt.stab (b, e) Tx.inorder) S →
  ((b = go!"" ∨ adt.affLt b e) → acc.map Prod.snd ++ adt.stab (b, e) Tx.inorder <+: S) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      adt.ownNode K s dq p x Tx ∗ ivp ↦{dq'} K.ivl vb ve ∗ K.keyAt db vb b ∗ K.keyAt de ve e ∗
      adt.nodeVisitorOk K dq S (b = go!"" ∨ adt.affLt b e) nv I J ∗ I acc }}
    (App (App (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"visit"))
      (Val #ivp)) (Val #s)) (Val #nv))
  {{ (r : Bool), RET #r; ivp ↦{dq'} K.ivl vb ve ∗ K.keyAt db vb b ∗ K.keyAt de ve e ∗
      ∃ (ns : List Loc) (es : List adt.Entry),
        ⌜List.Sublist es (adt.stab (b, e) Tx.inorder) ∧
          ((b = go!"" ∨ adt.affLt b e) →
            if r then es = adt.stab (b, e) Tx.inorder
            else es <+: adt.stab (b, e) Tx.inorder ∧ es ≠ [])⌝ ∗
        adt.ownNodeH K s dq p x Tx ns es ∗ (if r then I else J) (acc ++ ns.zip es) }}

end spec

end EtcdGrove
end Perennial
