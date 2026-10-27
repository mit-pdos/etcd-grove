/-
`Interval.Compare` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Model.lean`, `Defs.lean`.
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

/-- `p.Compare(q)` for two intervals over the keys `K` (`q` as a `Comparable`, the `*Interval`
the body asserts it is), the values holding the keys at any fractions: `ivlCmp`, `-1` if `p` is
left of `q`, `1` if right, `0` if they overlap. -/
abbrev adt.Interval.Compare.spec : Prop :=
  ∀ (K : adt.KeyRep (GF := GF)), K.CompareOk →
  ∀ (p : Loc) (dq : DFrac) (vb ve : val) (db de : DFrac) (b e : GoString)
    (q : Loc) (dq' : DFrac) (vb' ve' : val) (db' de' : DFrac) (b' e' : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      p ↦{dq} K.ivl vb ve ∗ K.keyAt db vb b ∗ K.keyAt de ve e ∗
      q ↦{dq'} K.ivl vb' ve' ∗ K.keyAt db' vb' b' ∗ K.keyAt de' ve' e' }}
    (App (Val (p @!! go.GoType.PointerType Interval.ty @!! go!"Compare"))
      (Val #(interface.mkOk (go.GoType.PointerType Interval.ty) #q)))
  {{ RET #(W64 (adt.ivlCmp (b, e) (b', e')));
      p ↦{dq} K.ivl vb ve ∗ K.keyAt db vb b ∗ K.keyAt de ve e ∗
      q ↦{dq'} K.ivl vb' ve' ∗ K.keyAt db' vb' b' ∗ K.keyAt de' ve' e' }}

end spec

end EtcdGrove
end Perennial
