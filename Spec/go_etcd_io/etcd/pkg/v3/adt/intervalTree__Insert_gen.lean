/-
`intervalTree.Insert` (`interval_tree.go`) over a comparator: the generic result the string-affine
`Insert.spec` and the bytes-affine `Insert_bytes.spec` instantiate (the auth plan's S2b, 2026-10-23;
`notes/decisions.md`, "S2b of the auth plan"). Lean-first; see `Model.lean`, `Defs.lean`.
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

/-- `t.Insert(ivl, v)` over the keys `K` (the interval's values holding its keys read-only: the
new node keeps them), the tree below `2^63 - 1` entries (the count's bound: `ownIvtK` keeps
`count` below `2^63`, which `count++` cannot check): the entry inserted in the tree's order,
after the entries with an equal interval if any (the tree allows them). The whole tree. -/
abbrev adt.intervalTree.Insert_gen.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t : Loc) (L : List adt.Entry) (vb ve : val) (b e : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      adt.ownIvtK K t L (DFrac.own 1) ∗ K.keyAt .discard vb b ∗ K.keyAt .discard ve e ∗
      ⌜L.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Insert"))
      (Val #(K.ivl vb ve))) (Val #v))
  {{ RET #(); adt.ownIvtK K t (adt.ivtInsert ((b, e), v) L) (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
