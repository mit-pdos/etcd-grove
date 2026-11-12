/-
`intervalTree.Find` (`interval_tree.go`) over a comparator (the auth plan's S2b, 2026-10-23).
Lean-first; see `Model.lean`, `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs

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

/-- `t.Find(ivl)` over the keys `K` (the query's values holding its keys at any fractions,
kept): a pointer to the `IntervalValue` of a node whose entry has the interval, or `nil` when
there is none. With equal intervals (the tree allows them), the entry is one of them, not
necessarily the first in order: `find` stops at the topmost on its path. At any `dq` of the
tree; the pointer is lent at `dq`, the tree given back by the wand. -/
abbrev adt.intervalTree.Find_gen.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t : Loc) (L : List adt.Entry) (vb ve : val) (db de : DFrac) (b e : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvtK K t L dq ∗
      K.keyAt db vb b ∗ K.keyAt de ve e }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Find"))
      (Val #(K.ivl vb ve)))
  {{ (p : Loc), RET #p; K.keyAt db vb b ∗ K.keyAt de ve e ∗
      ((∃ z : adt.Entry, ⌜z ∈ L ∧ z.1 = (b, e)⌝ ∗ ⌜p ≠ null⌝ ∗
        K.ivAt p dq z ∗ (K.ivAt p dq z -∗ adt.ownIvtK K t L dq)) ∨
      (⌜p = null ∧ (b, e) ∉ L.map Prod.fst⌝ ∗ adt.ownIvtK K t L dq)) }}

end spec

end EtcdGrove
end Perennial
