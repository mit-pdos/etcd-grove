/-
`intervalTree.replaceParent` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Ctx.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Ctx

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

/-- `t.replaceParent(x, y)` (internal, the rotations'): `y` takes `x`'s place under `x`'s
parent `p` (or as the root), `p`'s `max` recomputed from `y`'s (`updateMax` up the path), and
`x`'s parent is `y`. `x` is the hole of the context `C` (its parent's `max` from any `mh`); `y`
brings its `parent` and `max` fields. -/
abbrev adt.intervalTree.replaceParent.spec : Prop :=
  ∀ (t s : Loc) (dq : DFrac) (C : adt.RbCtx adt.Entry) (x p y yp : Loc)
    (mh : Option GoString) (my : GoString),
  x ≠ s → y ≠ s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗ adt.ownCtx t s C x p mh ∗
      x.[intervalNode, go!"parent"] ↦ p ∗
      y.[intervalNode, go!"parent"] ↦ yp ∗ y.[intervalNode, go!"max"] ↦ adt.maxW my }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"replaceParent"))
      (Val #x)) (Val #y))
  {{ RET #(); t.[intervalTree, go!"sentinel"] ↦{dq} s ∗ adt.ownCtx t s C y p (some my) ∗
      x.[intervalNode, go!"parent"] ↦ y ∗
      y.[intervalNode, go!"parent"] ↦ p ∗ y.[intervalNode, go!"max"] ↦ adt.maxW my }}

end spec

end EtcdGrove
end Perennial
