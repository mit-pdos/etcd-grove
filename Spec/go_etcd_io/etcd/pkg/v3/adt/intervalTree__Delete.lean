/-
`(*intervalTree).Delete(ivl)`: removes one entry with exactly that interval, if any (CLRS 13.4
with the successor's `iv` copied into the deleted node; `deleteFixup`).

**Users.** `watcherGroup.delete` (3f: a range whose watcher set became empty; its caller panics on
`false`). Snippet: `adt/watchers.go` `ReqRangeWatchers`.

**Proof sketch.** `find`; when found, `successor` if two children, the splice, `updateMax` up from
the spliced node's parent, `deleteFixup` when a black node was removed, `count--`.

**Changes** from `specs-ref`'s `Delete_gen`: at a key kind `c`. **Margin.** Which of several equal
entries is removed is not specified (`find`'s descent picks one).
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

/-- **`t.Delete(ivl)`**: `true` iff an entry has the interval, one of them removed. -/
def intervalTree.Delete.spec : Prop :=
  ∀ (c : Cmp) (t : Loc) (L : List Entry) (vb ve : val) (db de : DFrac) (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ivt c t L (DFrac.own 1) ∗ keyAt c db vb b ∗ keyAt c de ve e }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Delete")) (Val #(c.ivl vb ve)))
  {{ RET #(decide ((b, e) ∈ L.map Prod.fst)); keyAt c db vb b ∗ keyAt c de ve e ∗
      ∃ L' : List Entry,
        ⌜if (b, e) ∈ L.map Prod.fst then
            ∃ (i : Nat) (z : Entry), L[i]? = some z ∧ z.1 = (b, e) ∧ L' = L.eraseIdx i
          else L' = L⌝ ∗
        ivt c t L' (DFrac.own 1) }}

end spec

end Adt
end EtcdGrove
end Perennial
