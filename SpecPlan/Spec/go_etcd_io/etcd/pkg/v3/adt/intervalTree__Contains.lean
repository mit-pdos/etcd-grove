/-
`(*intervalTree).Contains(ivl)`: whether the entries' intervals cover every key of the query.

**Users.** `checkKeyInterval` (3d: a range request against the permission tree). Snippet:
`adt/perms.go` `ReqPermCover`.

**Proof sketch.** `Visit` over the query with a closure scanning the stabbed entries in order (the
running maximum end; a gap stops it); the result compares the scan's maximum with the query's end
and the first begin with its begin. Its correctness (`containsRes_iff` of `specs-ref`'s proof):
for a query whose begin is below its end, the greedy scan over the begin-sorted stabbed entries
answers coverage. A query from the top (`b = ""`: `IvlS.queryOk`, so `Visit` is exact) stabs
nothing (`ivlCmp` puts it right of every interval), so `minBegin` stays `nil`: `false`.

**Changes** from `specs-ref`'s `Contains_gen`: the result stated as its meaning (coverage of every
key, `ivlMem`) rather than the scan's definition (`containsRes`), which a client would unfold; at a
key kind `c`.

**Margin.** For an empty or inverted query with a key begin (`affLt b e` false, `b ≠ ""`) some
boolean. (Integration: the top-begin query's `false` added for 3d's `checkKeyInterval`, I5's
request, `req/go_etcd_io_etcd_pkg_v3_adt.md`, "from 3d", item 3.)
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

/-- **`t.Contains(ivl)`**: for a query `[b, e)` with `b` below `e`, whether every key in it is in
some entry's interval. -/
def intervalTree.Contains.spec : Prop :=
  ∀ (c : Cmp) (t : Loc) (L : List Entry) (vb ve : val) (db de : DFrac) (b e : GoString)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ivt c t L dq ∗ keyAt c db vb b ∗ keyAt c de ve e }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Contains")) (Val #(c.ivl vb ve)))
  {{ (r : Bool), RET #r; ivt c t L dq ∗ keyAt c db vb b ∗ keyAt c de ve e ∗
      ⌜(affLt b e → (r = true ↔ ∀ k, ivlMem (b, e) k → ∃ z ∈ L, ivlMem z.1 k)) ∧
        (b = go!"" → r = false)⌝ }}

end spec

end Adt
end EtcdGrove
end Perennial
