/-
`intervalTree.rotateRight` (`interval_tree.go`). Lean-first (no Rocq counterpart); see `Ctx.lean`.
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

/-- `t.rotateRight(x)` (internal, the fixups'), at the hole `x` of the context `C` with its
left child `y` (CLRS's `RIGHT-ROTATE`, mirrored `rotateLeft`): `y` takes `x`'s place, `x`
becomes its right child with `y`'s right subtree on its left; the `max`es recomputed. -/
abbrev adt.intervalTree.rotateRight.spec : Prop :=
  ∀ (t s : Loc) (dq : DFrac) (C : adt.RbCtx adt.Entry) (x p y ap bp dp : Loc)
    (cx cy : adt.RbColor) (a b d : adt.RbT adt.Entry) (xe ye : adt.Entry),
  x ≠ s ∧ x ≠ null → y ≠ s ∧ y ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      adt.ownCtx t s C x p (some (adt.nodeMax (.node cy a ye b) xe d)) ∗
      x.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl xe.1.1 xe.1.2, Val' := xe.2 } : IntervalValue) ∗
      x.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMax (.node cy a ye b) xe d) ∗
      x.[intervalNode, go!"left"] ↦ y ∗ x.[intervalNode, go!"right"] ↦ dp ∗
      x.[intervalNode, go!"parent"] ↦ p ∗ x.[intervalNode, go!"c"] ↦ adt.colorW cx ∗
      y.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl ye.1.1 ye.1.2, Val' := ye.2 } : IntervalValue) ∗
      y.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMax a ye b) ∗
      y.[intervalNode, go!"left"] ↦ ap ∗ y.[intervalNode, go!"right"] ↦ bp ∗
      y.[intervalNode, go!"parent"] ↦ x ∗ y.[intervalNode, go!"c"] ↦ adt.colorW cy ∗
      adt.ownNode s 1 y ap a ∗ adt.ownNode s 1 y bp b ∗ adt.ownNode s 1 x dp d }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"rotateRight")) (Val #x))
  {{ RET #(); t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      adt.ownCtx t s C y p (some (adt.nodeMax a ye (.node cx b xe d))) ∗
      y.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl ye.1.1 ye.1.2, Val' := ye.2 } : IntervalValue) ∗
      y.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMax a ye (.node cx b xe d)) ∗
      y.[intervalNode, go!"left"] ↦ ap ∗ y.[intervalNode, go!"right"] ↦ x ∗
      y.[intervalNode, go!"parent"] ↦ p ∗ y.[intervalNode, go!"c"] ↦ adt.colorW cy ∗
      adt.ownNode s 1 y ap a ∗ adt.ownNode s 1 y x (.node cx b xe d) }}

end spec

end EtcdGrove
end Perennial
