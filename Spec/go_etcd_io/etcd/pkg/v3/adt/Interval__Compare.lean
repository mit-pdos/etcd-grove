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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `p.Compare(q)` for two affine intervals (`q` as a `Comparable`, the `*Interval` the body
asserts it is): `ivlCmp`, `-1` if `p` is left of `q`, `1` if right, `0` if they overlap. -/
abbrev adt.Interval.Compare.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (b e : GoString) (q : Loc) (dq' : DFrac) (b' e' : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ p ↦{dq} adt.affIvl b e ∗ q ↦{dq'} adt.affIvl b' e' }}
    (App (Val (p @!! go.GoType.PointerType Interval.ty @!! go!"Compare"))
      (Val #(interface.mkOk (go.GoType.PointerType Interval.ty) #q)))
  {{ RET #(W64 (adt.ivlCmp (b, e) (b', e'))); p ↦{dq} adt.affIvl b e ∗ q ↦{dq'} adt.affIvl b' e' }}

end spec

end EtcdGrove
end Perennial
