/-
`intervalTree.Delete` (`interval_tree.go`) over a comparator (the auth plan's S2b, 2026-10-23).
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

/-- `t.Delete(ivl)` over the keys `K` (the query's values holding its keys at any fractions,
kept): an entry with the interval removed, if any (and whether there was one). With equal
intervals (the tree allows them), the entry removed is one of them, not necessarily the first in
order (`find`'s). The whole tree. -/
abbrev adt.intervalTree.Delete_gen.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t : Loc) (L : List adt.Entry) (vb ve : val) (db de : DFrac) (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      adt.ownIvtK K t L (DFrac.own 1) ∗ K.keyAt db vb b ∗ K.keyAt de ve e }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Delete"))
      (Val #(K.ivl vb ve)))
  {{ RET #(decide ((b, e) ∈ L.map Prod.fst)); K.keyAt db vb b ∗ K.keyAt de ve e ∗
      ∃ L' : List adt.Entry,
        ⌜if (b, e) ∈ L.map Prod.fst then
            ∃ (i : Nat) (z : adt.Entry), L[i]? = some z ∧ z.1 = (b, e) ∧ L' = L.eraseIdx i
          else L' = L⌝ ∗
        adt.ownIvtK K t L' (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
