/-
`intervalTree.Stab` (`interval_tree.go`) over a comparator (the auth plan's S2b, 2026-10-23).
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

/-- `t.Stab(ivl)` over the keys `K`, of a query (its values holding its keys at any fractions,
kept) that is not empty-and-finite (`b = ""`, never overlapping, or `b < e`): a fresh slice of
pointers to the nodes' `IntervalValue`s of the entries overlapping the interval, in the tree's
order (`nil` for an empty tree). At any `dq` of the tree; the pointers are lent at `dq`, the
tree given back by the wand. -/
abbrev adt.intervalTree.Stab_gen.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t : Loc) (L : List adt.Entry) (vb ve : val) (db de : DFrac) (b e : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ adt.ownIvtK K t L dq ∗
      K.keyAt db vb b ∗ K.keyAt de ve e ∗ ⌜b = go!"" ∨ adt.affLt b e⌝ }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Stab"))
      (Val #(K.ivl vb ve)))
  {{ (ivs : GoSlice) (ps : List Loc), RET #ivs; K.keyAt db vb b ∗ K.keyAt de ve e ∗ ivs ↦* ps ∗
      ownSliceCap Loc ivs (DFrac.own 1) ∗ ⌜ps.length = (adt.stab (b, e) L).length⌝ ∗
      ([∗list] x ∈ ps.zip (adt.stab (b, e) L), ⌜x.1 ≠ null⌝ ∗ K.ivAt x.1 dq x.2) ∗
      (([∗list] x ∈ ps.zip (adt.stab (b, e) L), K.ivAt x.1 dq x.2) -∗ adt.ownIvtK K t L dq) }}

end spec

end EtcdGrove
end Perennial
