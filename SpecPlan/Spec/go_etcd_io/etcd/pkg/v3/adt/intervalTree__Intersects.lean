/-
`(*intervalTree).Intersects(iv)`: whether some entry overlaps the interval.

**Users.** `watcherGroup.contains` (3f: a point: does a key have a range watcher), `checkIntervals`
(2a: a put's key against the level's deletes), `checkKeyPoint` (3d: a key against the permission
tree). Snippets: `adt/watchers.go`, `adt/perms.go` `ReqPermPoint`, `adt/dups.go`.

**Proof sketch.** The descent by the left child's `max` (CLRS 14.3's search): an overlap in the left
subtree exists iff its `max` is above the query's begin.

**Changes** from `specs-ref`'s `Intersects_gen`: at a key kind `c`. **Margin.** None (exact for any
query, `stab`'s emptiness).
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

def intervalTree.Intersects.spec : Prop :=
  ∀ (c : Cmp) (t : Loc) (L : List Entry) (vb ve : val) (db de : DFrac) (b e : GoString)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ivt c t L dq ∗ keyAt c db vb b ∗ keyAt c de ve e }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Intersects")) (Val #(c.ivl vb ve)))
  {{ RET #(decide (stab (b, e) L ≠ [])); ivt c t L dq ∗ keyAt c db vb b ∗ keyAt c de ve e }}

end spec

end Adt
end EtcdGrove
end Perennial
