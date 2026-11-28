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
(child of `p`) holding `Tx`, at `dq`, for any query at `ivp` (its values holding its keys at any
fractions): calls the visitor on the nodes `Tx.visitL (b, e)` names (the descent `visit` makes,
pruning on the subtrees' `max`; for a sorted tree and a query that is not empty-and-finite, the
overlapping ones: `visit_stab`), in order, until it stops if it does; the visitor keeps their `iv`
fields (recorded in `I`, or in `J` when it stops: `nodeVisitorOk`). Returns whether no visitor
stopped; the subtree with the visited nodes' fields lent out (`ownNodeH`, `ns` the nodes, `es`
their entries: all of `Tx.visitL (b, e)` when none stopped, a non-empty prefix of it else). The
visitor is told it is called on a prefix of `S`, the entries visited before (`acc`) and this
subtree's being one. -/
abbrev adt.intervalNode.visit.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (s : Loc) (dq : DFrac) (p x : Loc) (Tx : adt.RbT adt.Entry) (ivp : Loc) (dq' : DFrac)
    (vb ve : val) (db de : DFrac) (b e : GoString) (nv : GoFunc) (S : List adt.Entry)
    (I J : List (Loc × adt.Entry) → IProp GF) (acc : List (Loc × adt.Entry)),
  acc.map Prod.snd ++ Tx.visitL (b, e) <+: S →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      adt.ownNode K s dq p x Tx ∗ ivp ↦{dq'} K.ivl vb ve ∗ K.keyAt db vb b ∗ K.keyAt de ve e ∗
      adt.nodeVisitorOk K dq S True nv I J ∗ I acc }}
    (App (App (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"visit"))
      (Val #ivp)) (Val #s)) (Val #nv))
  {{ (r : Bool), RET #r; ivp ↦{dq'} K.ivl vb ve ∗ K.keyAt db vb b ∗ K.keyAt de ve e ∗
      ∃ (ns : List Loc) (es : List adt.Entry),
        ⌜if r then es = Tx.visitL (b, e) else es <+: Tx.visitL (b, e) ∧ es ≠ []⌝ ∗
        adt.ownNodeH K s dq p x Tx ns es ∗ (if r then I else J) (acc ++ ns.zip es) }}

end spec

end EtcdGrove
end Perennial
