/-
`(*intervalTree).Stab(iv)`: the entries overlapping the query, as pointers to the nodes'
`IntervalValue`s, in the tree's order (`nil` for an empty tree).

**Users.** `watcherGroup.watcherSetByKey` (3f: the range watchers of an event's key, a point query;
their sets are read, merged or returned). Snippet: `adt/watchers.go` `ReqRangeWatchers`.

**Proof sketch.** `count == 0` returns `nil` (the count is exact: `ivt`'s realization); else
`Visit` with an appending closure. The pointers are lent at the tree's fraction, given back by the
wand.

**Changes** from `specs-ref`'s `Stab_gen`: at a key kind `c`. **Margin.** On a query that is not
`queryOk`, a sublist (not stated: no caller).
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

def intervalTree.Stab.spec : Prop :=
  ∀ (c : Cmp) (t : Loc) (L : List Entry) (vb ve : val) (db de : DFrac) (b e : GoString)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ivt c t L dq ∗ keyAt c db vb b ∗ keyAt c de ve e ∗ ⌜IvlS.queryOk (b, e)⌝ }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Stab")) (Val #(c.ivl vb ve)))
  {{ (ivs : GoSlice) (ps : List Loc), RET #ivs; keyAt c db vb b ∗ keyAt c de ve e ∗
      ivs ↦* ps ∗ ownSliceCap Loc ivs (DFrac.own 1) ∗ ⌜ps.length = (stab (b, e) L).length⌝ ∗
      ([∗list] x ∈ ps.zip (stab (b, e) L), ⌜x.1 ≠ null⌝ ∗ ivAt c x.1 dq x.2) ∗
      (([∗list] x ∈ ps.zip (stab (b, e) L), ivAt c x.1 dq x.2) -∗ ivt c t L dq) }}

end spec

end Adt
end EtcdGrove
end Perennial
