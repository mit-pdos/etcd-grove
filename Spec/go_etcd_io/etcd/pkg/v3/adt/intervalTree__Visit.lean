/-
`(*intervalTree).Visit(ivl, ivv)`: calls `ivv` on each entry overlapping the query, in the tree's
order, until it returns `false`.

**Users.** `Stab`, `Contains`, `Union` (internal to the package). No caller outside. Kept: verified
before.

**Proof sketch.** `intervalNode.visit` from the root (in-order, pruning a right subtree whose
`max` is at or below the query's begin); the callback's contract (`ivVisitorOk`) once per visited
entry, the tree's node lent.

**Changes** from `specs-ref`'s `Visit_gen`: at a key kind `c`. **Margin.** On a non-`queryOk` query,
the visited entries are only a sublist of the stabbed ones.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

def intervalTree.Visit.spec : Prop :=
  ∀ (c : Cmp) (t : Loc) (L : List Entry) (vb ve : val) (db de : DFrac) (b e : GoString)
    (dq : DFrac) (ivv : GoFunc) (I J : List (Loc × Entry) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ivt c t L dq ∗ keyAt c db vb b ∗ keyAt c de ve e ∗
      ivVisitorOk c dq (stab (b, e) L) (IvlS.queryOk (b, e)) ivv I J ∗ I [] }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Visit")) (Val #(c.ivl vb ve))) (Val #ivv))
  {{ RET #(); keyAt c db vb b ∗ keyAt c de ve e ∗ ivt c t L dq ∗
      ∃ (ps : List Loc) (es : List Entry) (r : Bool),
      ⌜List.Sublist es (stab (b, e) L) ∧ ps.length = es.length ∧
        (IvlS.queryOk (b, e) →
          if r then es = stab (b, e) L else es <+: stab (b, e) L ∧ es ≠ [])⌝ ∗
      (if r then I (ps.zip es) else J (ps.zip es)) }}

end spec

end Adt
end EtcdGrove
end Perennial
