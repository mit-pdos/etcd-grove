/-
`(*intervalTree).Union(inIvt, ivl)`: inserts into the receiver every entry of `inIvt` overlapping
`ivl`, in `inIvt`'s order.

**Users.** `checkIntervals` (2a: a nested transaction's branches' deletes merged into the level's,
over the whole key space `["\x00", "")`). Snippet: `adt/dups.go` `ReqNestedDeletes`.

**Proof sketch.** `inIvt.Visit` (its `Visit` spec at the other tree's fraction) with a closure whose
loop state is the receiver after the inserts so far (`Insert`, each below `ivtCountMax` by the
premise); the visit is exact (`queryOk`). The two trees are distinct (the receiver's whole and the
argument's fraction cannot coexist on one tree).

**Changes** from `specs-ref`'s `Union_gen`: at a key kind `c`; the inserted list is the stabbed one
itself (the old spec's permutation was slack: `Visit` is in order).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.adt.Api

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

def intervalTree.Union.spec : Prop :=
  ∀ (c : Cmp) (t t' : Loc) (L L' : List Entry) (dq' : DFrac) (vb ve : val) (db de : DFrac)
    (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ivt c t L (DFrac.own 1) ∗ ivt c t' L' dq' ∗ keyAt c db vb b ∗ keyAt c de ve e ∗
      ⌜L.length + L'.length ≤ ivtCountMax ∧ IvlS.queryOk (b, e)⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Union"))
      (Val #(interface.mkOk (go.GoType.PointerType intervalTree.ty) #t'))) (Val #(c.ivl vb ve)))
  {{ RET #(); keyAt c db vb b ∗ keyAt c de ve e ∗ ivt c t' L' dq' ∗
      ivt c t ((stab (b, e) L').foldl (fun acc z => ivtInsert z acc) L) (DFrac.own 1) }}

end spec

end Adt
end EtcdGrove
end Perennial
