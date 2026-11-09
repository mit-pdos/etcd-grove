/-
`(*intervalTree).rotateRight(x)` (internal): `x`'s left child takes its place; the two nodes'
`max` recomputed.

**Proof sketch.** As `rotateLeft`'s.

**Changes** from `specs-ref`'s file: at a key kind `c` (was a key representation `K` with
its comparison contract); pure premises in the precondition.

**Margin.** Mirrors the code.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

def intervalTree.rotateRight.spec : Prop :=
  ∀ (c : Cmp) (t s : Loc) (dq : DFrac) (C : RbCtx Entry) (ls : List (Loc × Loc))
    (x p y ap bp dp : Loc)
    (cx cy : RbColor) (a b d : RbT Entry) (xe ye : Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ⌜(x ≠ s ∧ x ≠ null → y ≠ s ∧ y ≠ null)⌝ ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      ownCtxAt c t s C ls x p (some (nodeMax (.node cy a ye b) xe d)) ∗
      ivAt c (x.[intervalNode, go!"iv"]) (DFrac.own 1) xe ∗
      maxAt c (x.[intervalNode, go!"max"]) (DFrac.own 1) (nodeMax (.node cy a ye b) xe d) ∗
      x.[intervalNode, go!"left"] ↦ y ∗ x.[intervalNode, go!"right"] ↦ dp ∗
      x.[intervalNode, go!"parent"] ↦ p ∗ x.[intervalNode, go!"c"] ↦ colorW cx ∗
      ivAt c (y.[intervalNode, go!"iv"]) (DFrac.own 1) ye ∗
      maxAt c (y.[intervalNode, go!"max"]) (DFrac.own 1) (nodeMax a ye b) ∗
      y.[intervalNode, go!"left"] ↦ ap ∗ y.[intervalNode, go!"right"] ↦ bp ∗
      y.[intervalNode, go!"parent"] ↦ x ∗ y.[intervalNode, go!"c"] ↦ colorW cy ∗
      ownNode c s (DFrac.own 1) y ap a ∗ ownNode c s (DFrac.own 1) y bp b ∗ ownNode c s (DFrac.own 1) x dp d }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"rotateRight")) (Val #x))
  {{ RET #(); t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      ownCtxAt c t s C ls y p (some (nodeMax a ye (.node cx b xe d))) ∗
      ivAt c (y.[intervalNode, go!"iv"]) (DFrac.own 1) ye ∗
      maxAt c (y.[intervalNode, go!"max"]) (DFrac.own 1) (nodeMax a ye (.node cx b xe d)) ∗
      y.[intervalNode, go!"left"] ↦ ap ∗ y.[intervalNode, go!"right"] ↦ x ∗
      y.[intervalNode, go!"parent"] ↦ p ∗ y.[intervalNode, go!"c"] ↦ colorW cy ∗
      ivAt c (x.[intervalNode, go!"iv"]) (DFrac.own 1) xe ∗
      maxAt c (x.[intervalNode, go!"max"]) (DFrac.own 1) (nodeMax b xe d) ∗
      x.[intervalNode, go!"left"] ↦ bp ∗ x.[intervalNode, go!"right"] ↦ dp ∗
      x.[intervalNode, go!"parent"] ↦ y ∗ x.[intervalNode, go!"c"] ↦ colorW cx ∗
      ownNode c s (DFrac.own 1) y ap a ∗ ownNode c s (DFrac.own 1) x bp b ∗ ownNode c s (DFrac.own 1) x dp d }}

end spec

end Adt
end EtcdGrove
end Perennial
