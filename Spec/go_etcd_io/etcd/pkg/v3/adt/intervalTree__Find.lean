/-
`(*intervalTree).Find(ivl)`: a pointer to the `IntervalValue` of an entry with exactly that
interval, or `nil`.

**Users.** `watcherGroup.add` (3f: the existing watcher set of a range, to which the watcher is
added: `iv.Val.(watcherSet).add(wa)` writes the map, not the node), `watcherGroup.delete`. Snippet:
`adt/watchers.go` `ReqRangeWatchers`.

**Proof sketch.** `find`'s descent (both endpoints compared at each node). The node's `iv` is lent
at the tree's fraction, the tree given back by the wand.

**Changes** from `specs-ref`'s `Find_gen`: at a key kind `c`. **Margin.** Which equal entry is found
is not specified.
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

def intervalTree.Find.spec : Prop :=
  ∀ (c : Cmp) (t : Loc) (L : List Entry) (vb ve : val) (db de : DFrac) (b e : GoString)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ivt c t L dq ∗ keyAt c db vb b ∗ keyAt c de ve e }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Find")) (Val #(c.ivl vb ve)))
  {{ (p : Loc), RET #p; keyAt c db vb b ∗ keyAt c de ve e ∗
      ((∃ z : Entry, ⌜z ∈ L ∧ z.1 = (b, e) ∧ p ≠ null⌝ ∗ ivAt c p dq z ∗
          (ivAt c p dq z -∗ ivt c t L dq)) ∨
       (⌜p = null ∧ (b, e) ∉ L.map Prod.fst⌝ ∗ ivt c t L dq)) }}

end spec

end Adt
end EtcdGrove
end Perennial
