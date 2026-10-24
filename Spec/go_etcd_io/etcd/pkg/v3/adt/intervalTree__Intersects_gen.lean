/-
`intervalTree.Intersects` (`interval_tree.go`) over a comparator (the auth plan's S2b, 2026-10-23).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `t.Intersects(ivl)` over the keys `K` (the query's values holding its keys at any fractions,
kept): whether an entry overlaps the interval. At any `dq` of the tree. -/
abbrev adt.intervalTree.Intersects_gen.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t : Loc) (L : List adt.Entry) (vb ve : val) (db de : DFrac) (b e : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvtK K t L dq ∗
      K.keyAt db vb b ∗ K.keyAt de ve e }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Intersects"))
      (Val #(K.ivl vb ve)))
  {{ RET #(decide (adt.stab (b, e) L ≠ [])); adt.ownIvtK K t L dq ∗
      K.keyAt db vb b ∗ K.keyAt de ve e }}

end spec

end EtcdGrove
end Perennial
