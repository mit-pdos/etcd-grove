/-
`intervalTree.Insert` (`interval_tree.go`) over a comparator: the generic result the string-affine
`Insert.spec` and the bytes-affine `Insert_bytes.spec` instantiate (the auth plan's S2b, 2026-10-23;
`notes/decisions.md`, "S2b of the auth plan"). Lean-first; see `Model.lean`, `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs
public import Proof.go_etcd_io.etcd.pkg.v3.adt.TreeInsert

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
new node keeps them), on the exact tree `T` (`ownIvtT`), below `2^63 - 1` entries (the count's
bound: `count++` cannot check it): the tree `Insert` computes (`RbT.insertRB`: the descent, the
red leaf, `insertFixup`), whose entries are `T`'s with the new one inserted in the tree's order,
after the entries with an equal interval if any (the tree allows them). The whole tree. -/
abbrev adt.intervalTree.Insert_gen.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t : Loc) (T : adt.RbT adt.Entry) (vb ve : val) (b e : GoString) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      adt.ownIvtT K t T (DFrac.own 1) ∗ K.keyAt .discard vb b ∗ K.keyAt .discard ve e ∗
      ⌜T.inorder.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Insert"))
      (Val #(K.ivl vb ve))) (Val #v))
  {{ RET #(); adt.ownIvtT K t (T.insertRB ((b, e), v)) (DFrac.own 1) ∗
      ⌜(T.insertRB ((b, e), v)).inorder = adt.ivtInsert ((b, e), v) T.inorder⌝ }}

end spec

end EtcdGrove
end Perennial
