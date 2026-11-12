/-
`BytesAffineComparable.Compare` (`interval_tree.go`). Lean-first (no Rocq counterpart); see
`Model.lean` (`affCmp`) and `BytesIvl.lean` (the auth plan's S2, 2026-10-23).
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

/-- `b.Compare(c)`, `c` a `BytesAffineComparable` (the code's type assertion: a panic on any
other `Comparable`): the affine order of the slices' contents, `affCmp` (the empty slice the top,
else `bytes.Compare`, the string order); the slices kept. -/
abbrev adt.BytesAffineComparable.Compare.spec : Prop :=
  ∀ (s s' : GoSlice) (bs bs' : GoString) (d d' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ s ↦*{d} bs ∗ s' ↦*{d'} bs' }}
    (App (Val (s @!! BytesAffineComparable.ty @!! go!"Compare"))
      (Val #(interface.mkOk BytesAffineComparable.ty #s')))
  {{ RET #(W64 (adt.affCmp bs bs')); s ↦*{d} bs ∗ s' ↦*{d'} bs' }}

end spec

end EtcdGrove
end Perennial
