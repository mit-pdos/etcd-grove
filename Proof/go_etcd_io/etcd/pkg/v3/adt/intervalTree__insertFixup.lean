module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__insertFixup
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__color
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__rotateLeft
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__rotateRight
public import Proof.go_etcd_io.etcd.pkg.v3.adt.CtxSpecs

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

theorem adt.intervalTree.insertFixup.wp_proof
    (h_color : adt.intervalNode.color.spec (GF := GF) (hG := hG))
    (h_rotateLeft : adt.intervalTree.rotateLeft.spec (GF := GF) (hG := hG))
    (h_rotateRight : adt.intervalTree.rotateRight.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.insertFixup.spec (GF := GF) (hG := hG) := by
  intro t s dq C0 z0 p0 tz0 hinv0
  wp_start as ⟨Hs, HC, Hz⟩
  wp_auto
  ihave HI : (∃ (z p : Loc) (C : adt.RbCtx adt.Entry) (tz : adt.RbT adt.Entry),
      "z" ∷ z_ptr ↦ z ∗ "HC" ∷ adt.ownCtx t s C z p tz.maxEnd ∗
      "Hz" ∷ adt.ownNode s 1 p z tz ∗
      "%Hinv" ∷ ⌜C.FixInv tz ∧ (C.plug tz).inorder = (C0.plug tz0).inorder⌝ : IProp GF)
      $$ [z HC Hz]
  · iexists z0, p0, C0, tz0
    iframe
    ipureintro; exact ⟨hinv0, rfl⟩
  wp_for HI
  obtain ⟨l, ze, r, rfl⟩ := adt.RbCtx.fixInv_red C tz Hinv.1
  icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hz with
    ⟨%lp, %rp, %Hzn, Hziv, Hzmx, Hzl, Hzr, Hzp, Hzc, Hzln, Hzrn⟩
  icases adt.ownCtx_colorAt _ _ _ _ _ _ $$ HC with ⟨Hpc, HCback⟩
  wp_auto
  wp_apply h_color p s C.color (DFrac.own 1) $$ [Hpc] as Hpc
  · iframe
  ihave HC := HCback $$ Hpc
  have hvb : decide ((#false : val) = #true) = false :=
    decide_eq_false (fun h => Bool.false_ne_true (go.intoVal_inj h))
  cases hcol : C.color with
  | black =>
    -- the parent is black (or the sentinel): the loop ends; the root blackened
    rw [show decide (adt.colorW .black = W64 1) = false by decide]
    simp only [hvb, Bool.false_eq_true, _root_.decide_true, ↓reduceIte]
    ihave Hz := adt.ownNode_node_close s 1 p z .red l ze r $$ [Hziv Hzmx Hzl Hzr Hzp Hzc Hzln Hzrn]
    · iexists lp, rp; iframe; ipureintro; exact Hzn
    icases adt.ownCtx_plug _ _ _ _ _ _ $$ [HC Hz] with ⟨%R, Hroot, HT⟩
    · iframe
    obtain ⟨c', l', e', r', hT⟩ := adt.RbCtx.plug_node C .red l ze r
    rw [hT]
    icases adt.ownNode_blacken _ _ _ _ _ _ _ $$ HT with ⟨Hrc, HT⟩
    wp_auto
    rw [show black = #(adt.colorW .black) from rfl]
    wp_auto
    ihave HT := HT $$ Hrc
    iapply HΦ
    iframe Hs
    iexists R, .node .black l' e' r'
    iframe
    ipureintro
    have hx := adt.RbCtx.fixInv_exit C _ Hinv.1 hcol
    rw [hT] at hx
    refine ⟨hx, ?_⟩
    rw [← Hinv.2, hT]; rfl
  | red =>
    rw [show decide (adt.colorW .red = W64 1) = true by decide]
    simp only [_root_.decide_true, ↓reduceIte]
    have hinv := Hinv.1
    have hord := Hinv.2
    cases C with
    | top => cases hcol
    | inL c CP pe s1 =>
      simp only [adt.RbCtx.color] at hcol
      subst hcol
      rw [adt.ownCtx_inL t s .red CP pe s1 z]
      icases HC with ⟨%g, %s1p, %Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hs1, HC⟩
      cases CP with
      | top => exact (adt.RbCtx.fixInv_inL_top hinv rfl).elim
      | inL cg CG ge u =>
        rw [adt.ownCtx_inL t s cg CG ge u p]
        icases HC with ⟨%gp, %up, %Hgn, Hgiv, Hgmx, Hgl, Hgr, Hgp, Hgc, Hu, HC⟩
        wp_auto
        icases adt.ownNode_colorAt _ _ _ _ $$ Hu with ⟨Huc, Huback⟩
        wp_apply h_color up s u.color (DFrac.own 1) $$ [Huc] as Huc
        · iframe
        ihave Hu := Huback $$ Huc
        cases hucol : u.color with
        | red =>
          obtain ⟨ul, ue, ur, rfl⟩ : ∃ ul ue ur, u = .node .red ul ue ur := by
            cases u with
            | leaf => cases hucol
            | node cu ul ue ur => cases hucol; exact ⟨ul, ue, ur, rfl⟩
          rw [show decide (adt.colorW .red = W64 1) = true by decide]
          icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hu with
            ⟨%ulp, %urp, %Hun, Huiv, Humx, Hul, Hur, Hup, Hucc, Huln, Hurn⟩
          rw [show black = #(adt.colorW .black) from rfl, show red = #(adt.colorW .red) from rfl]
          wp_auto
          wp_for_post
          obtain ⟨hinv', hord'⟩ := adt.RbCtx.fix_red_LL hinv
          ihave Hz := adt.ownNode_node_close s 1 p z .red l ze r $$
            [Hziv Hzmx Hzl Hzr Hzp Hzc Hzln Hzrn]
          · iexists lp, rp; iframe; ipureintro; exact Hzn
          ihave Hp := adt.ownNode_node_close s 1 g p .black (.node .red l ze r) pe s1 $$
            [Hpiv Hpmx Hpl Hpr Hpp Hpc Hz Hs1]
          · iexists z, s1p; simp only [adt.nodeMax_eq]; iframe; ipureintro; exact Hpn
          ihave Hu := adt.ownNode_node_close s 1 g up .black ul ue ur $$
            [Huiv Humx Hul Hur Hup Hucc Huln Hurn]
          · iexists ulp, urp; iframe; ipureintro; exact Hun
          ihave Hg := adt.ownNode_node_close s 1 gp g .red
            (.node .black (.node .red l ze r) pe s1) ge (.node .black ul ue ur) $$
            [Hgiv Hgmx Hgl Hgr Hgp Hgc Hp Hu]
          · iexists p, up; simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hgn
          iframe
          iexists g, gp, CG,
            .node .red (.node .black (.node .red l ze r) pe s1) ge (.node .black ul ue ur)
          simp only [adt.nodeMax_eq, adt.maxEnd_node]
          iframe
          ipureintro
          exact ⟨hinv', hord'.trans hord⟩
        | black =>
          rw [show decide (adt.colorW .black = W64 1) = false by decide]
          ihave %Hne := adt.ownNode_ne _ _ _ _ _ _ Hzn.1 $$ Hs1 Hzp
          rw [show black = #(adt.colorW .black) from rfl, show red = #(adt.colorW .red) from rfl]
          wp_auto
          rw [_root_.decide_eq_false (Ne.symm Hne)]
          wp_auto
          ihave Hz := adt.ownNode_node_close s 1 p z .red l ze r $$
            [Hziv Hzmx Hzl Hzr Hzp Hzc Hzln Hzrn]
          · iexists lp, rp; iframe; ipureintro; exact Hzn
          wp_apply adt.rotateRight_ctx h_rotateRight t s dq CG g gp p z s1p up .red .black (.node .red l ze r) s1 u
            ge pe Hgn Hpn
            $$ [Hs HC Hgiv Hgmx Hgl Hgr Hgp Hgc Hpiv Hpmx Hpl Hpr Hpp Hpc Hz Hs1 Hu]
            as ⟨Hs, HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hz, Hg⟩
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
          wp_for_post
          obtain ⟨hinv', hord'⟩ := adt.RbCtx.fix_black_LL hinv hucol
          ihave HC : adt.ownCtx t s (.inL .black CG pe (.node .red s1 ge u)) z p
              (RbT.node .red l ze r).maxEnd $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hg]
          · rw [adt.ownCtx_inL]
            iexists gp, g
            simp only [adt.nodeMax_eq, adt.maxEnd_node]
            iframe
            ipureintro; exact Hpn
          iframe
          iexists z, p, .inL .black CG pe (.node .red s1 ge u), .node .red l ze r
          iframe
          ipureintro
          exact ⟨hinv', hord'.trans hord⟩
      | inR cg u ge CG =>
        rw [adt.ownCtx_inR t s cg u ge CG p]
        icases HC with ⟨%gp, %up, %Hgn, Hgiv, Hgmx, Hgl, Hgr, Hgp, Hgc, Hu, HC⟩
        ihave %Hne := adt.ownNode_ne _ _ _ _ _ _ Hpn.1 $$ Hu Hpp
        wp_auto
        rw [_root_.decide_eq_false (Ne.symm Hne)]
        wp_auto
        icases adt.ownNode_colorAt _ _ _ _ $$ Hu with ⟨Huc, Huback⟩
        wp_apply h_color up s u.color (DFrac.own 1) $$ [Huc] as Huc
        · iframe
        ihave Hu := Huback $$ Huc
        cases hucol : u.color with
        | red =>
          obtain ⟨ul, ue, ur, rfl⟩ : ∃ ul ue ur, u = .node .red ul ue ur := by
            cases u with
            | leaf => cases hucol
            | node cu ul ue ur => cases hucol; exact ⟨ul, ue, ur, rfl⟩
          rw [show decide (adt.colorW .red = W64 1) = true by decide]
          icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hu with
            ⟨%ulp, %urp, %Hun, Huiv, Humx, Hul, Hur, Hup, Hucc, Huln, Hurn⟩
          rw [show black = #(adt.colorW .black) from rfl, show red = #(adt.colorW .red) from rfl]
          wp_auto
          wp_for_post
          obtain ⟨hinv', hord'⟩ := adt.RbCtx.fix_red_LR hinv
          ihave Hz := adt.ownNode_node_close s 1 p z .red l ze r $$
            [Hziv Hzmx Hzl Hzr Hzp Hzc Hzln Hzrn]
          · iexists lp, rp; iframe; ipureintro; exact Hzn
          ihave Hp := adt.ownNode_node_close s 1 g p .black (.node .red l ze r) pe s1 $$
            [Hpiv Hpmx Hpl Hpr Hpp Hpc Hz Hs1]
          · iexists z, s1p; simp only [adt.nodeMax_eq]; iframe; ipureintro; exact Hpn
          ihave Hu := adt.ownNode_node_close s 1 g up .black ul ue ur $$
            [Huiv Humx Hul Hur Hup Hucc Huln Hurn]
          · iexists ulp, urp; iframe; ipureintro; exact Hun
          ihave Hg := adt.ownNode_node_close s 1 gp g .red
            (.node .black ul ue ur) ge (.node .black (.node .red l ze r) pe s1) $$
            [Hgiv Hgmx Hgl Hgr Hgp Hgc Hp Hu]
          · iexists up, p; simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hgn
          iframe
          iexists g, gp, CG,
            .node .red (.node .black ul ue ur) ge (.node .black (.node .red l ze r) pe s1)
          simp only [adt.nodeMax_eq, adt.maxEnd_node]
          iframe
          ipureintro
          exact ⟨hinv', hord'.trans hord⟩
        | black =>
          rw [show decide (adt.colorW .black = W64 1) = false by decide]
          rw [show black = #(adt.colorW .black) from rfl, show red = #(adt.colorW .red) from rfl]
          wp_auto
          -- `z` is `P`'s left child: rotate `P` right, `z` moves up to `P`
          ihave HCP : adt.ownCtx t s (.inR cg u ge CG) p g
              (some (adt.nodeMax (.node .red l ze r) pe s1)) $$ [HC Hgiv Hgmx Hgl Hgr Hgp Hgc Hu]
          · rw [adt.ownCtx_inR]
            iexists gp, up
            simp only [adt.nodeMax_eq, adt.maxEnd_node]
            iframe; ipureintro; exact Hgn
          wp_apply adt.rotateRight_ctx h_rotateRight t s dq (.inR cg u ge CG) p g z lp rp s1p .red .red l r s1 pe ze
            Hpn Hzn
            $$ [Hs HCP Hpiv Hpmx Hpl Hpr Hpp Hpc Hziv Hzmx Hzl Hzr Hzp Hzc Hzln Hzrn Hs1]
            as ⟨Hs, HCP, Hziv, Hzmx, Hzl, Hzr, Hzp, Hzc, Hzln, Hp⟩
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
          icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hp with
            ⟨%rp', %s1p', %Hpn', Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hrn, Hs1⟩
          rw [adt.ownCtx_inR t s cg u ge CG z]
          icases HCP with ⟨%gp', %up', %Hgn', Hgiv, Hgmx, Hgl, Hgr, Hgp, Hgc, Hu, HC⟩
          wp_auto
          -- `z`'s old node black, `G` red: rotate `G` left
          ihave Hp := adt.ownNode_node_close s 1 z p .red r pe s1 $$
            [Hpiv Hpmx Hpl Hpr Hpp Hpc Hrn Hs1]
          · iexists rp', s1p'; iframe; ipureintro; exact Hpn'
          wp_apply adt.rotateLeft_ctx h_rotateLeft t s dq CG g gp' z up' lp p .red .black u l (.node .red r pe s1)
            ge ze Hgn' Hzn
            $$ [Hs HC Hgiv Hgmx Hgl Hgr Hgp Hgc Hziv Hzmx Hzl Hzr Hzp Hzc Hu Hzln Hp]
            as ⟨Hs, HC, Hziv, Hzmx, Hzl, Hzr, Hzp, Hzc, Hg, Hp⟩
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
          wp_for_post
          obtain ⟨hinv', hord'⟩ := adt.RbCtx.fix_black_LR hinv hucol
          ihave HC : adt.ownCtx t s (.inR .black (.node .red u ge l) ze CG) p z
              (RbT.node .red r pe s1).maxEnd $$ [HC Hziv Hzmx Hzl Hzr Hzp Hzc Hg]
          · rw [adt.ownCtx_inR]
            iexists gp', g
            simp only [adt.nodeMax_eq, adt.maxEnd_node]
            iframe
            ipureintro; exact Hzn
          iframe
          iexists p, z, .inR .black (.node .red u ge l) ze CG, .node .red r pe s1
          iframe
          ipureintro
          exact ⟨hinv', hord'.trans hord⟩
    | inR c s1 pe CP =>
      simp only [adt.RbCtx.color] at hcol
      subst hcol
      rw [adt.ownCtx_inR t s .red s1 pe CP z]
      icases HC with ⟨%g, %s1p, %Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hs1, HC⟩
      cases CP with
      | top => exact (adt.RbCtx.fixInv_inR_top hinv rfl).elim
      | inL cg CG ge u =>
        rw [adt.ownCtx_inL t s cg CG ge u p]
        icases HC with ⟨%gp, %up, %Hgn, Hgiv, Hgmx, Hgl, Hgr, Hgp, Hgc, Hu, HC⟩
        wp_auto
        icases adt.ownNode_colorAt _ _ _ _ $$ Hu with ⟨Huc, Huback⟩
        wp_apply h_color up s u.color (DFrac.own 1) $$ [Huc] as Huc
        · iframe
        ihave Hu := Huback $$ Huc
        cases hucol : u.color with
        | red =>
          obtain ⟨ul, ue, ur, rfl⟩ : ∃ ul ue ur, u = .node .red ul ue ur := by
            cases u with
            | leaf => cases hucol
            | node cu ul ue ur => cases hucol; exact ⟨ul, ue, ur, rfl⟩
          rw [show decide (adt.colorW .red = W64 1) = true by decide]
          icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hu with
            ⟨%ulp, %urp, %Hun, Huiv, Humx, Hul, Hur, Hup, Hucc, Huln, Hurn⟩
          rw [show black = #(adt.colorW .black) from rfl, show red = #(adt.colorW .red) from rfl]
          wp_auto
          wp_for_post
          obtain ⟨hinv', hord'⟩ := adt.RbCtx.fix_red_RL hinv
          ihave Hz := adt.ownNode_node_close s 1 p z .red l ze r $$
            [Hziv Hzmx Hzl Hzr Hzp Hzc Hzln Hzrn]
          · iexists lp, rp; iframe; ipureintro; exact Hzn
          ihave Hp := adt.ownNode_node_close s 1 g p .black s1 pe (.node .red l ze r) $$
            [Hpiv Hpmx Hpl Hpr Hpp Hpc Hz Hs1]
          · iexists s1p, z; simp only [adt.nodeMax_eq]; iframe; ipureintro; exact Hpn
          ihave Hu := adt.ownNode_node_close s 1 g up .black ul ue ur $$
            [Huiv Humx Hul Hur Hup Hucc Huln Hurn]
          · iexists ulp, urp; iframe; ipureintro; exact Hun
          ihave Hg := adt.ownNode_node_close s 1 gp g .red
            (.node .black s1 pe (.node .red l ze r)) ge (.node .black ul ue ur) $$
            [Hgiv Hgmx Hgl Hgr Hgp Hgc Hp Hu]
          · iexists p, up; simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hgn
          iframe
          iexists g, gp, CG,
            .node .red (.node .black s1 pe (.node .red l ze r)) ge (.node .black ul ue ur)
          simp only [adt.nodeMax_eq, adt.maxEnd_node]
          iframe
          ipureintro
          exact ⟨hinv', hord'.trans hord⟩
        | black =>
          rw [show decide (adt.colorW .black = W64 1) = false by decide]
          rw [show black = #(adt.colorW .black) from rfl, show red = #(adt.colorW .red) from rfl]
          wp_auto
          -- `z` is `P`'s right child: rotate `P` left, `z` moves up to `P`
          ihave HCP : adt.ownCtx t s (.inL cg CG ge u) p g
              (some (adt.nodeMax s1 pe (.node .red l ze r))) $$ [HC Hgiv Hgmx Hgl Hgr Hgp Hgc Hu]
          · rw [adt.ownCtx_inL]
            iexists gp, up
            simp only [adt.nodeMax_eq, adt.maxEnd_node]
            iframe; ipureintro; exact Hgn
          wp_apply adt.rotateLeft_ctx h_rotateLeft t s dq (.inL cg CG ge u) p g z s1p lp rp .red .red s1 l r pe ze
            Hpn Hzn
            $$ [Hs HCP Hpiv Hpmx Hpl Hpr Hpp Hpc Hziv Hzmx Hzl Hzr Hzp Hzc Hzln Hzrn Hs1]
            as ⟨Hs, HCP, Hziv, Hzmx, Hzl, Hzr, Hzp, Hzc, Hp, Hzrn⟩
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
          icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hp with
            ⟨%s1p', %lp', %Hpn', Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hs1, Hln⟩
          rw [adt.ownCtx_inL t s cg CG ge u z]
          icases HCP with ⟨%gp', %up', %Hgn', Hgiv, Hgmx, Hgl, Hgr, Hgp, Hgc, Hu, HC⟩
          wp_auto
          -- `z`'s old node black, `G` red: rotate `G` right
          ihave Hp := adt.ownNode_node_close s 1 z p .red s1 pe l $$
            [Hpiv Hpmx Hpl Hpr Hpp Hpc Hs1 Hln]
          · iexists s1p', lp'; iframe; ipureintro; exact Hpn'
          wp_apply adt.rotateRight_ctx h_rotateRight t s dq CG g gp' z p rp up' .red .black (.node .red s1 pe l) r u
            ge ze Hgn' Hzn
            $$ [Hs HC Hgiv Hgmx Hgl Hgr Hgp Hgc Hziv Hzmx Hzl Hzr Hzp Hzc Hp Hzrn Hu]
            as ⟨Hs, HC, Hziv, Hzmx, Hzl, Hzr, Hzp, Hzc, Hp, Hg⟩
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
          wp_for_post
          obtain ⟨hinv', hord'⟩ := adt.RbCtx.fix_black_RL hinv hucol
          ihave HC : adt.ownCtx t s (.inL .black CG ze (.node .red r ge u)) p z
              (RbT.node .red s1 pe l).maxEnd $$ [HC Hziv Hzmx Hzl Hzr Hzp Hzc Hg]
          · rw [adt.ownCtx_inL]
            iexists gp', g
            simp only [adt.nodeMax_eq, adt.maxEnd_node]
            iframe
            ipureintro; exact Hzn
          iframe
          iexists p, z, .inL .black CG ze (.node .red r ge u), .node .red s1 pe l
          iframe
          ipureintro
          exact ⟨hinv', hord'.trans hord⟩
      | inR cg u ge CG =>
        rw [adt.ownCtx_inR t s cg u ge CG p]
        icases HC with ⟨%gp, %up, %Hgn, Hgiv, Hgmx, Hgl, Hgr, Hgp, Hgc, Hu, HC⟩
        ihave %Hne := adt.ownNode_ne _ _ _ _ _ _ Hpn.1 $$ Hu Hpp
        wp_auto
        rw [_root_.decide_eq_false (Ne.symm Hne)]
        wp_auto
        icases adt.ownNode_colorAt _ _ _ _ $$ Hu with ⟨Huc, Huback⟩
        wp_apply h_color up s u.color (DFrac.own 1) $$ [Huc] as Huc
        · iframe
        ihave Hu := Huback $$ Huc
        cases hucol : u.color with
        | red =>
          obtain ⟨ul, ue, ur, rfl⟩ : ∃ ul ue ur, u = .node .red ul ue ur := by
            cases u with
            | leaf => cases hucol
            | node cu ul ue ur => cases hucol; exact ⟨ul, ue, ur, rfl⟩
          rw [show decide (adt.colorW .red = W64 1) = true by decide]
          icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hu with
            ⟨%ulp, %urp, %Hun, Huiv, Humx, Hul, Hur, Hup, Hucc, Huln, Hurn⟩
          rw [show black = #(adt.colorW .black) from rfl, show red = #(adt.colorW .red) from rfl]
          wp_auto
          wp_for_post
          obtain ⟨hinv', hord'⟩ := adt.RbCtx.fix_red_RR hinv
          ihave Hz := adt.ownNode_node_close s 1 p z .red l ze r $$
            [Hziv Hzmx Hzl Hzr Hzp Hzc Hzln Hzrn]
          · iexists lp, rp; iframe; ipureintro; exact Hzn
          ihave Hp := adt.ownNode_node_close s 1 g p .black s1 pe (.node .red l ze r) $$
            [Hpiv Hpmx Hpl Hpr Hpp Hpc Hz Hs1]
          · iexists s1p, z; simp only [adt.nodeMax_eq]; iframe; ipureintro; exact Hpn
          ihave Hu := adt.ownNode_node_close s 1 g up .black ul ue ur $$
            [Huiv Humx Hul Hur Hup Hucc Huln Hurn]
          · iexists ulp, urp; iframe; ipureintro; exact Hun
          ihave Hg := adt.ownNode_node_close s 1 gp g .red
            (.node .black ul ue ur) ge (.node .black s1 pe (.node .red l ze r)) $$
            [Hgiv Hgmx Hgl Hgr Hgp Hgc Hp Hu]
          · iexists up, p; simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hgn
          iframe
          iexists g, gp, CG,
            .node .red (.node .black ul ue ur) ge (.node .black s1 pe (.node .red l ze r))
          simp only [adt.nodeMax_eq, adt.maxEnd_node]
          iframe
          ipureintro
          exact ⟨hinv', hord'.trans hord⟩
        | black =>
          rw [show decide (adt.colorW .black = W64 1) = false by decide]
          ihave %Hne' := adt.ownNode_ne _ _ _ _ _ _ Hzn.1 $$ Hs1 Hzp
          rw [show black = #(adt.colorW .black) from rfl, show red = #(adt.colorW .red) from rfl]
          wp_auto
          rw [_root_.decide_eq_false (Ne.symm Hne')]
          wp_auto
          ihave Hz := adt.ownNode_node_close s 1 p z .red l ze r $$
            [Hziv Hzmx Hzl Hzr Hzp Hzc Hzln Hzrn]
          · iexists lp, rp; iframe; ipureintro; exact Hzn
          wp_apply adt.rotateLeft_ctx h_rotateLeft t s dq CG g gp p up s1p z .red .black u s1 (.node .red l ze r)
            ge pe Hgn Hpn
            $$ [Hs HC Hgiv Hgmx Hgl Hgr Hgp Hgc Hpiv Hpmx Hpl Hpr Hpp Hpc Hu Hs1 Hz]
            as ⟨Hs, HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hg, Hz⟩
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
          wp_for_post
          obtain ⟨hinv', hord'⟩ := adt.RbCtx.fix_black_RR hinv hucol
          ihave HC : adt.ownCtx t s (.inR .black (.node .red u ge s1) pe CG) z p
              (RbT.node .red l ze r).maxEnd $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hg]
          · rw [adt.ownCtx_inR]
            iexists gp, g
            simp only [adt.nodeMax_eq, adt.maxEnd_node]
            iframe
            ipureintro; exact Hpn
          iframe
          iexists z, p, .inR .black (.node .red u ge s1) pe CG, .node .red l ze r
          iframe
          ipureintro
          exact ⟨hinv', hord'.trans hord⟩

end proof

end EtcdGrove
end Perennial
