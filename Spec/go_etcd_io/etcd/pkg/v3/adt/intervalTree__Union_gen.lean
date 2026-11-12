/-
`intervalTree.Union` (`interval_tree.go`) over a comparator (the auth plan's S2b, 2026-10-23).
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

/-- `t.Union(t', ivl)` over the keys `K`, of another tree `t'` (an `IntervalTree` holding an
`*intervalTree`): inserts into `t`, one by one (`Insert`, in `Visit`'s order: some order of them),
the entries of `t'` the interval overlaps (`stab`); `t'` unchanged. As `Insert`, no premise that
the inserted intervals are new, and the count bound: `t` holds the whole tree, `t'` any `dq'`
(so the two are distinct trees), together below `2^63` entries. The query (its values holding
its keys at any fractions, kept) is not degenerate (`Stab`'s and `Visit`'s premise). -/
abbrev adt.intervalTree.Union_gen.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (t t' : Loc) (L L' : List adt.Entry) (dq' : DFrac) (vb ve : val) (db de : DFrac)
    (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      adt.ownIvtK K t L (DFrac.own 1) ∗ adt.ownIvtK K t' L' dq' ∗
      K.keyAt db vb b ∗ K.keyAt de ve e ∗
      ⌜L.length + L'.length < 2 ^ 63⌝ ∗ ⌜b = go!"" ∨ adt.affLt b e⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Union"))
      (Val #(interface.mkOk (go.GoType.PointerType intervalTree.ty) #t')))
      (Val #(K.ivl vb ve)))
  {{ RET #(); K.keyAt db vb b ∗ K.keyAt de ve e ∗
      ∃ zs : List adt.Entry, ⌜zs.Perm (adt.stab (b, e) L')⌝ ∗
      adt.ownIvtK K t (zs.foldl (fun acc z => adt.ivtInsert z acc) L) (DFrac.own 1) ∗
      adt.ownIvtK K t' L' dq' }}

end spec

end EtcdGrove
end Perennial
