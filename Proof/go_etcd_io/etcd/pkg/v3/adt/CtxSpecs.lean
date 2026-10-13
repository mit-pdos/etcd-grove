/-
The helpers' specs over `ownCtx` (the context's frames' locations hidden), derived from their
specs over `ownCtxAt` (`CtxAt.lean`): what `Insert` and `insertFixup` use (they never come back
to a frame). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__updateMax
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__rotateLeft
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__rotateRight

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `updateMax`'s spec over `ownCtx`. -/
theorem adt.updateMax_ctx (h : adt.intervalNode.updateMax.spec (GF := GF) (hG := hG)) :
  ∀ (t s : Loc) (C : adt.RbCtx adt.Entry) (x p lp rp : Loc) (e : adt.Entry) (m0 : GoString)
    (ml mr : Option GoString),
  x ≠ s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      adt.ownCtx t s C x p (some m0) ∗
      x.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      x.[intervalNode, go!"max"] ↦ adt.maxW m0 ∗
      x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
      x.[intervalNode, go!"parent"] ↦ p ∗
      adt.childMax s lp ml ∗ adt.childMax s rp mr }}
    (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"updateMax")) (Val #s))
  {{ RET #(); adt.ownCtx t s C x p (some (adt.nodeMaxO ml e mr)) ∗
      x.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl e.1.1 e.1.2, Val' := e.2 } : IntervalValue) ∗
      x.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMaxO ml e mr) ∗
      x.[intervalNode, go!"left"] ↦ lp ∗ x.[intervalNode, go!"right"] ↦ rp ∗
      x.[intervalNode, go!"parent"] ↦ p ∗
      adt.childMax s lp ml ∗ adt.childMax s rp mr }}
  := by
  intro t s C x p lp rp e m0 ml mr hxs
  wp_start_folded as ⟨HC, Hiv, Hmx, Hl, Hr, Hp, Hml, Hmr⟩
  icases (adt.ownCtx_at _ _ _ _ _ _).1 $$ HC with ⟨%ls, HC⟩
  wp_apply h t s C ls x p lp rp e m0 ml mr hxs $$ [HC Hiv Hmx Hl Hr Hp Hml Hmr]
    as ⟨HC, Hiv, Hmx, Hl, Hr, Hp, Hml, Hmr⟩
  · iframe
  iapply HΦ
  iframe
  iapply adt.ownCtxAt_ctx; iexact HC

/-- `rotateLeft`'s spec over `ownCtx`, `x`'s subtree whole. -/
theorem adt.rotateLeft_ctx (h : adt.intervalTree.rotateLeft.spec (GF := GF) (hG := hG)) :
  ∀ (t s : Loc) (dq : DFrac) (C : adt.RbCtx adt.Entry) (x p y ap bp dp : Loc)
    (cx cy : adt.RbColor) (a b d : adt.RbT adt.Entry) (xe ye : adt.Entry),
  x ≠ s ∧ x ≠ null → y ≠ s ∧ y ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗
      t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      adt.ownCtx t s C x p (some (adt.nodeMax a xe (.node cy b ye d))) ∗
      x.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl xe.1.1 xe.1.2, Val' := xe.2 } : IntervalValue) ∗
      x.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMax a xe (.node cy b ye d)) ∗
      x.[intervalNode, go!"left"] ↦ ap ∗ x.[intervalNode, go!"right"] ↦ y ∗
      x.[intervalNode, go!"parent"] ↦ p ∗ x.[intervalNode, go!"c"] ↦ adt.colorW cx ∗
      y.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl ye.1.1 ye.1.2, Val' := ye.2 } : IntervalValue) ∗
      y.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMax b ye d) ∗
      y.[intervalNode, go!"left"] ↦ bp ∗ y.[intervalNode, go!"right"] ↦ dp ∗
      y.[intervalNode, go!"parent"] ↦ x ∗ y.[intervalNode, go!"c"] ↦ adt.colorW cy ∗
      adt.ownNode s 1 x ap a ∗ adt.ownNode s 1 y bp b ∗ adt.ownNode s 1 y dp d }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"rotateLeft")) (Val #x))
  {{ RET #(); t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
      adt.ownCtx t s C y p (some (adt.nodeMax (.node cx a xe b) ye d)) ∗
      y.[intervalNode, go!"iv"] ↦
        ({ Ivl' := adt.affIvl ye.1.1 ye.1.2, Val' := ye.2 } : IntervalValue) ∗
      y.[intervalNode, go!"max"] ↦ adt.maxW (adt.nodeMax (.node cx a xe b) ye d) ∗
      y.[intervalNode, go!"left"] ↦ x ∗ y.[intervalNode, go!"right"] ↦ dp ∗
      y.[intervalNode, go!"parent"] ↦ p ∗ y.[intervalNode, go!"c"] ↦ adt.colorW cy ∗
      adt.ownNode s 1 y x (.node cx a xe b) ∗ adt.ownNode s 1 y dp d }}
  := by
  intro t s dq C x p y ap bp dp cx cy a b d xe ye hx hy
  wp_start_folded as ⟨Hs, HC, Hxiv, Hxmx, Hxl, Hxr, Hxp, Hxc, Hyiv, Hymx, Hyl, Hyr, Hyp, Hyc, Ha, Hb, Hd⟩
  icases (adt.ownCtx_at _ _ _ _ _ _).1 $$ HC with ⟨%ls, HC⟩
  wp_apply h t s dq C ls x p y ap bp dp cx cy a b d xe ye hx hy
    $$ [Hs HC Hxiv Hxmx Hxl Hxr Hxp Hxc Hyiv Hymx Hyl Hyr Hyp Hyc Ha Hb Hd]
    as ⟨Hs, HC, Hyiv, Hymx, Hyl, Hyr, Hyp, Hyc, Hxiv, Hxmx, Hxl, Hxr, Hxp, Hxc, Ha, Hb, Hd⟩
  · iframe
  iapply HΦ
  ihave HC := adt.ownCtxAt_ctx _ _ _ _ _ _ _ $$ HC
  iframe
  iapply adt.ownNode_node_close
  iexists ap, bp
  iframe
  ipureintro; exact hx

/-- `rotateRight`'s spec over `ownCtx`, `x`'s subtree whole. -/
theorem adt.rotateRight_ctx (h : adt.intervalTree.rotateRight.spec (GF := GF) (hG := hG)) :
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
  := by
  intro t s dq C x p y ap bp dp cx cy a b d xe ye hx hy
  wp_start_folded as ⟨Hs, HC, Hxiv, Hxmx, Hxl, Hxr, Hxp, Hxc, Hyiv, Hymx, Hyl, Hyr, Hyp, Hyc, Ha, Hb, Hd⟩
  icases (adt.ownCtx_at _ _ _ _ _ _).1 $$ HC with ⟨%ls, HC⟩
  wp_apply h t s dq C ls x p y ap bp dp cx cy a b d xe ye hx hy
    $$ [Hs HC Hxiv Hxmx Hxl Hxr Hxp Hxc Hyiv Hymx Hyl Hyr Hyp Hyc Ha Hb Hd]
    as ⟨Hs, HC, Hyiv, Hymx, Hyl, Hyr, Hyp, Hyc, Hxiv, Hxmx, Hxl, Hxr, Hxp, Hxc, Ha, Hb, Hd⟩
  · iframe
  iapply HΦ
  ihave HC := adt.ownCtxAt_ctx _ _ _ _ _ _ _ $$ HC
  iframe
  iapply adt.ownNode_node_close
  iexists bp, dp
  iframe
  ipureintro; exact hx

end proof

end EtcdGrove
end Perennial
