module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__rotateRight
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__replaceParent
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__updateMax

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

theorem adt.intervalTree.rotateRight.wp_proof
    (h_updateMax : adt.intervalNode.updateMax.spec (GF := GF) (hG := hG))
    (h_replaceParent : adt.intervalTree.replaceParent.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.rotateRight.spec (GF := GF) (hG := hG) := by
  intro t s dq C ls x p y ap bp dp cx cy a b d xe ye hx hy
  wp_start as ⟨Hs, HC, Hxiv, Hxmx, Hxl, Hxr, Hxp, Hxc, Hyiv, Hymx, Hyl, Hyr, Hyp, Hyc, Ha, Hb, Hd⟩
  wp_auto
  rw [_root_.decide_eq_false hy.1]
  wp_auto
  wp_join iprop(adt.ownNode s 1 x bp b ∗ y.[intervalNode, go!"right"] ↦ bp ∗ y_ptr ↦ y ∗
      x_ptr ↦ x)
    with [Hb Hyr y x] as ⟨Hb, Hyr, y, x⟩
  · cases b with
    | leaf => rw [adt.ownNode_leaf, adt.ownNode_leaf]; iframe
    | node cb lb eb rb =>
      icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hb with ⟨%lp, %rp, %Hn, -⟩
      exact absurd Hif Hn.1
  · cases b with
    | leaf =>
      rw [adt.ownNode_leaf]; icases Hb with %Hn; exact absurd Hn Hif
    | node cb lb eb rb =>
      icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hb with
        ⟨%lp, %rp, %Hn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
      wp_auto
      iframe
      isplitl []
      · ipureintro; rfl
      iapply adt.ownNode_node_close
      iexists lp, rp
      iframe
      ipureintro; exact Hn
  -- `x`'s max over its new children
  icases adt.ownNode_childMax _ _ _ b $$ Hb with ⟨Hbm, Hbback⟩
  icases adt.ownNode_childMax _ _ _ d $$ Hd with ⟨Hdm, Hdback⟩
  wp_apply h_updateMax t s C ls x p bp dp xe (adt.nodeMax (.node cy a ye b) xe d) b.maxEnd d.maxEnd
    hx.1 $$ [HC Hxiv Hxmx Hxl Hxr Hxp Hbm Hdm] as ⟨HC, Hxiv, Hxmx, Hxl, Hxr, Hxp, Hbm, Hdm⟩
  · iframe
  ihave Hb := Hbback $$ Hbm
  ihave Hd := Hdback $$ Hdm
  -- `y` in `x`'s place
  wp_apply h_replaceParent t s dq C ls x p y x _ (adt.nodeMax a ye b) hx.1 hy.1
    $$ [Hs HC Hxp Hyp Hymx] as ⟨Hs, HC, Hxp, Hyp, Hymx⟩
  · iframe
  -- `x` under `y`, `y`'s max
  icases adt.ownNode_childMax _ _ _ a $$ Ha with ⟨Ham, Haback⟩
  wp_apply h_updateMax t s C ls y p ap x ye (adt.nodeMax a ye b) a.maxEnd
    (some (adt.nodeMaxO b.maxEnd xe d.maxEnd)) hy.1
    $$ [HC Hyiv Hymx Hyl Hyr Hyp Hxmx Ham] as ⟨HC, Hyiv, Hymx, Hyl, Hyr, Hyp, Ham, Hxm⟩
  · rw [adt.childMax_some]; iframe; ipureintro; exact hx.1
  rw [adt.childMax_some]
  icases Hxm with ⟨-, Hxmx⟩
  ihave Ha := Haback $$ Ham
  iapply HΦ
  simp only [adt.nodeMax_eq, adt.maxEnd_node]
  iframe

end proof

end EtcdGrove
end Perennial
