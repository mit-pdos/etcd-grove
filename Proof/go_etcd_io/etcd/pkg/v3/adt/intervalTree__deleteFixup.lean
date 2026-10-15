module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__deleteFixup
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__color
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

/-- The tree after the exit's blackening of `x`. -/
theorem adt.del_exit_post (t s : Loc) (C : adt.RbCtx adt.Entry) (ls : List (Loc × Loc))
    (x p : Loc) (tx : adt.RbT adt.Entry) (h : C.DelInv tx) (hx : C = .top ∨ tx.color = .red) :
    adt.ownCtxAt t s C ls x p tx.maxEnd ∗ adt.ownNode (GF := GF) s 1 p x tx.blacken ⊢
      ∃ (r : Loc) (T : adt.RbT adt.Entry), t.[intervalTree, go!"root"] ↦ r ∗
        adt.ownNode s 1 s r T ∗ ⌜adt.RbOk T ∧ T.inorder = (C.plug tx).inorder⌝ := by
  iintro ⟨HC, Hx⟩
  ihave HC := adt.ownCtxAt_ctx _ _ _ _ _ _ _ $$ HC
  rw [← adt.maxEnd_blacken]
  icases adt.ownCtx_plug _ _ _ _ _ _ $$ [HC Hx] with ⟨%r, Hr, HT⟩
  · iframe
  iexists r, C.plug tx.blacken
  iframe
  ipureintro
  exact ⟨adt.RbCtx.delInv_exit C tx h hx,
    adt.RbCtx.inorder_plug_congr C (adt.RbT.inorder_blacken tx)⟩

theorem adt.intervalTree.deleteFixup.wp_proof
    (h_color : adt.intervalNode.color.spec (GF := GF) (hG := hG))
    (h_rotateLeft : adt.intervalTree.rotateLeft.spec (GF := GF) (hG := hG))
    (h_rotateRight : adt.intervalTree.rotateRight.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.deleteFixup.spec (GF := GF) (hG := hG) := by
  intro t s dq C0 x0 p0 tx0 hinv0
  wp_start as ⟨Hs, HC, Hx, Hsent⟩
  wp_auto
  have hvb : decide ((#false : val) = #true) = false :=
    decide_eq_false (fun h => Bool.false_ne_true (go.intoVal_inj h))
  ihave HI : (∃ (x p : Loc) (C : adt.RbCtx adt.Entry) (tx : adt.RbT adt.Entry),
      "x" ∷ x_ptr ↦ x ∗ "HC" ∷ adt.ownCtx t s C x p tx.maxEnd ∗
      "Hx" ∷ adt.ownNode s 1 p x tx ∗ "Hsent" ∷ adt.sentAt s x p ∗
      "%Hinv" ∷ ⌜C.DelInv tx ∧ (C.plug tx).inorder = (C0.plug tx0).inorder⌝ : IProp GF)
      $$ [x HC Hx Hsent]
  · iexists x0, p0, C0, tx0
    iframe
    ipureintro; exact ⟨hinv0, rfl⟩
  wp_for HI
  obtain ⟨hinv, hord⟩ := Hinv
  icases (adt.ownCtx_at _ _ _ _ _ _).1 $$ HC with ⟨%ls, HC⟩
  icases adt.ownCtxAt_root _ _ _ _ _ _ _ $$ HC with ⟨Hroot, HCback⟩
  by_cases hCt : C = .top
  · -- `x` is the root: the loop ends
    subst hCt
    simp only [adt.topAt_top]
    wp_auto
    simp only [_root_.decide_true, hvb, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    ihave HC := HCback $$ Hroot
    -- the exit: `x` blackened
    cases tx with
    | leaf =>
      icases adt.ownNode_leaf_open _ _ _ _ $$ Hx with %Hxs
      rw [Hxs]
      unfold adt.sentAt
      icases Hsent with ⟨%v, Hsv, -⟩
      icases adt.node_c _ _ $$ Hsv with ⟨Hc, %Hsn, Hcback⟩
      rw [_root_.decide_eq_false Hsn]
      rw [show black = #(adt.colorW .black) from rfl]
      wp_auto
      ihave Hsv := Hcback $$ %(adt.colorW .black) Hc
      iapply HΦ
      iframe Hs
      isplitl [Hsv]
      · unfold adt.ownSentinel; iexists _; iexact Hsv
      rw [← hord]
      iapply adt.del_exit_post t s _ ls s p .leaf hinv (Or.inl rfl)
      iframe
    | node c l e r =>
      ihave %Hxn := adt.ownNode_node_ne _ _ _ _ _ _ _ _ $$ Hx
      rw [_root_.decide_eq_false Hxn.2]
      icases adt.ownNode_blacken _ _ _ _ _ _ _ $$ Hx with ⟨Hc, Hxback⟩
      rw [show black = #(adt.colorW .black) from rfl]
      wp_auto
      ihave Hx := Hxback $$ Hc
      iapply HΦ
      iframe Hs
      isplitl [Hsent]
      · iapply adt.sentAt_ownSentinel; iexact Hsent
      rw [← hord]
      iapply adt.del_exit_post t s _ ls x p (.node c l e r) hinv (Or.inl rfl)
      iframe
  · ihave HC := HCback $$ Hroot
    ihave %Hne := adt.ownCtxAt_root_ne_hole t s C ls x p _ tx hCt $$ HC Hx
    icases adt.ownCtxAt_root _ _ _ _ _ _ _ $$ HC with ⟨Hroot, HCback⟩
    wp_auto
    rw [_root_.decide_eq_false (Ne.symm Hne)]
    simp only [Bool.not_false]
    icases adt.ownNode_colorAt _ _ _ _ $$ Hx with ⟨Hxc, Hxback⟩
    wp_auto
    wp_apply h_color x s tx.color (DFrac.own 1) $$ [Hxc] as Hxc
    · iframe
    ihave Hx := Hxback $$ Hxc
    ihave HC := HCback $$ Hroot
    cases htxc : tx.color with
    | red =>
      rw [show decide (adt.colorW .red = W64 0) = false by decide]
      simp only [hvb, Bool.false_eq_true, ↓reduceIte, _root_.decide_true]
      wp_auto
      -- the exit: `x` blackened
      cases tx with
      | leaf =>
        icases adt.ownNode_leaf_open _ _ _ _ $$ Hx with %Hxs
        rw [Hxs]
        unfold adt.sentAt
        icases Hsent with ⟨%v, Hsv, -⟩
        icases adt.node_c _ _ $$ Hsv with ⟨Hc, %Hsn, Hcback⟩
        rw [_root_.decide_eq_false Hsn]
        rw [show black = #(adt.colorW .black) from rfl]
        wp_auto
        ihave Hsv := Hcback $$ %(adt.colorW .black) Hc
        iapply HΦ
        iframe Hs
        isplitl [Hsv]
        · unfold adt.ownSentinel; iexists _; iexact Hsv
        rw [← hord]
        iapply adt.del_exit_post t s _ ls s p .leaf hinv (Or.inr htxc)
        iframe
      | node c l e r =>
        ihave %Hxn := adt.ownNode_node_ne _ _ _ _ _ _ _ _ $$ Hx
        rw [_root_.decide_eq_false Hxn.2]
        icases adt.ownNode_blacken _ _ _ _ _ _ _ $$ Hx with ⟨Hc, Hxback⟩
        rw [show black = #(adt.colorW .black) from rfl]
        wp_auto
        ihave Hx := Hxback $$ Hc
        iapply HΦ
        iframe Hs
        isplitl [Hsent]
        · iapply adt.sentAt_ownSentinel; iexact Hsent
        rw [← hord]
        iapply adt.del_exit_post t s _ ls x p (.node c l e r) hinv (Or.inr htxc)
        iframe

    | black =>
      rw [show decide (adt.colorW .black = W64 0) = true by decide]
      simp only [_root_.decide_true, ↓reduceIte]
      cases C with
      | top => exact absurd rfl hCt
      | inL cp CP pe tw =>
        cases ls with
        | nil => iexfalso; iapply adt.ownCtxAt_inL_nil $$ HC
        | cons f ls' =>
        obtain ⟨pp, wp⟩ := f
        obtain ⟨cw, wl, we, wr, rfl⟩ := adt.RbCtx.delInv_sib_L hinv
        icases (adt.ownCtxAt_inL _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HC with
          ⟨%Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hw, HC⟩
        icases adt.parentAt_open _ _ _ _ $$ [Hx Hsent] with ⟨Hxp, Hxback⟩
        · iframe
        wp_auto
        icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hw with
          ⟨%wlp, %wrp, %Hwn, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hwln, Hwrn⟩
        ihave Hwc := adt.colorAt_intro s wp cw (DFrac.own 1) Hwn.1 $$ Hwc
        wp_apply h_color wp s cw (DFrac.own 1) $$ [Hwc] as Hwc
        · iframe
        ihave Hwc := adt.colorAt_elim s wp cw (DFrac.own 1) Hwn.1 $$ Hwc
        rw [show red = #(adt.colorW .red) from rfl, show black = #(adt.colorW .black) from rfl]
        wp_join iprop(∃ (cp' : adt.RbColor) (CP' : adt.RbCtx adt.Entry) (pp' w' : Loc)
            (ls'' : List (Loc × Loc)) (wl' : adt.RbT adt.Entry) (we' : adt.Entry)
            (wr' : adt.RbT adt.Entry),
            w_ptr ↦ w' ∗ x_ptr ↦ x ∗ ivt_ptr ↦ t ∗ t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
            adt.ownCtxAt t s (.inL cp' CP' pe (.node .black wl' we' wr')) ((pp', w') :: ls'') x p
              tx.maxEnd ∗
            adt.ownNode s 1 p x tx ∗ adt.sentAt s x p ∗
            ⌜(adt.RbCtx.inL cp' CP' pe (.node .black wl' we' wr')).DelInv tx ∧
              ((adt.RbCtx.inL cp' CP' pe (.node .black wl' we' wr')).plug tx).inorder =
                (C0.plug tx0).inorder⌝)
          with [w x ivt Hs Hpiv Hpmx Hpl Hpr Hpp Hpc HC Hxp Hxback Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln
            Hwrn] as ⟨%cp', %CP', %pp', %w', %ls'', %wl', %we', %wr', w, x, ivt, Hs, HC, Hx, Hsent,
              %Hinv'⟩
        · -- case 1: the sibling red: recoloured, `P` rotated left
          have hcw : cw = .red := by
            cases cw
            · rfl
            · exact absurd Hif (by decide)
          subst hcw
          ihave Hx := Hxback $$ Hxp
          icases Hx with ⟨Hx, Hsent⟩
          wp_apply h_rotateLeft t s dq CP ls' p pp wp x wlp wrp .red .black tx wl wr pe we Hpn Hwn
            $$ [Hs HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hwiv Hwmx Hwl Hwr Hwp Hwc Hx Hwln Hwrn]
            as ⟨Hs, HC, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hx, Hwln,
              Hwrn⟩
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
          icases adt.parentAt_open _ _ _ _ $$ [Hx Hsent] with ⟨Hxp, Hxback⟩
          · iframe
          wp_auto
          ihave Hx := Hxback $$ Hxp
          icases Hx with ⟨Hx, Hsent⟩
          obtain ⟨hinv1, hwlc, hord1⟩ := adt.RbCtx.del_case1_L hinv
          ihave HC1 := (adt.ownCtxAt_inL t s .black CP we wr pp wrp ls' p wp
              (some (adt.nodeMaxO tx.maxEnd pe wl.maxEnd))).2
            $$ [HC Hwiv Hwmx Hwl Hwr Hwp Hwc Hwrn]
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hwn
          ihave HC2 := (adt.ownCtxAt_inL t s .red (.inL .black CP we wr) pe wl wp wlp
              ((pp, wrp) :: ls') x p tx.maxEnd).2
            $$ [HC1 Hpiv Hpmx Hpl Hpr Hpp Hpc Hwln]
          · simp only [adt.nodeMax_eq]; iframe; ipureintro; exact Hpn
          obtain ⟨cw', wl', we', wr', rfl⟩ := adt.RbCtx.delInv_sib_L hinv1
          simp only [adt.RbT.color_node] at hwlc
          subst hwlc
          isplitl []
          · ipureintro; rfl
          iexists .red, .inL .black CP we wr, wp, wlp, (pp, wrp) :: ls', wl', we', wr'
          iframe
          ipureintro; exact ⟨hinv1, hord1.trans hord⟩
        · -- the sibling black
          have hcw : cw = .black := by
            cases cw
            · exact absurd rfl Hif
            · rfl
          subst hcw
          ihave Hx := Hxback $$ Hxp
          icases Hx with ⟨Hx, Hsent⟩
          ihave Hw := adt.ownNode_node_close s 1 p wp .black wl we wr $$
            [Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln Hwrn]
          · iexists wlp, wrp; iframe; ipureintro; exact Hwn
          ihave HC := (adt.ownCtxAt_inL t s cp CP pe (.node .black wl we wr) pp wp ls' x p
              tx.maxEnd).2 $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hw]
          · iframe; ipureintro; exact Hpn
          iexists cp, CP, pp, wp, ls', wl, we, wr
          iframe
          ipureintro; exact ⟨hinv, hord⟩
        -- the sibling black: `w`'s children's colours
        icases (adt.ownCtxAt_inL _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HC with
          ⟨%Hpn', Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hw, HC⟩
        icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hw with
          ⟨%wlp, %wrp, %Hwn, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hwln, Hwrn⟩
        rw [_root_.decide_eq_false Hwn.2]
        wp_auto
        icases adt.ownNode_colorAt _ _ _ _ $$ Hwln with ⟨Hlc, Hlback⟩
        icases adt.ownNode_colorAt _ _ _ _ $$ Hwrn with ⟨Hrc, Hrback⟩
        wp_join (Q := fun v => iprop(⌜v = #(decide (wl'.color = .black ∧ wr'.color = .black))⌝ ∗
            adt.colorAt s wlp wl'.color (DFrac.own 1) ∗ adt.colorAt s wrp wr'.color (DFrac.own 1) ∗
            w'.[intervalNode, go!"left"] ↦ wlp ∗ w'.[intervalNode, go!"right"] ↦ wrp ∗
            w_ptr ↦ w' ∗ ivt_ptr ↦ t ∗ t.[intervalTree, go!"sentinel"] ↦{dq} s))
          at (if: _ then _ else #false) with [Hlc Hrc Hwl Hwr w ivt Hs]
        · wp_apply h_color wlp s wl'.color (DFrac.own 1) $$ [Hlc] as Hlc
          · iframe
          cases hl : wl'.color with
          | red =>
            rw [show decide (adt.colorW .red = adt.colorW .black) = false by decide]
            wp_auto
            iframe
            ipureintro; simp
          | black =>
            rw [show decide (adt.colorW .black = adt.colorW .black) = true by decide]
            wp_auto
            wp_apply h_color wrp s wr'.color (DFrac.own 1) $$ [Hrc] as Hrc
            · iframe
            iframe
            cases hr : wr'.color with
            | red =>
              ipureintro; simp [show adt.colorW .red ≠ adt.colorW .black by decide]
            | black =>
              ipureintro; simp
        iintro ⟨%hv, Hlc, Hrc, Hwl, Hwr, w, ivt, Hs⟩
        subst hv
        obtain ⟨hinv', hord'⟩ := Hinv'
        by_cases hA : wl'.color = .black ∧ wr'.color = .black
        · -- case 2: both of `w`'s children black: `w` red, `x` moves up
          rw [_root_.decide_eq_true hA]
          wp_auto
          icases adt.parentAt_open _ _ _ _ $$ [Hx Hsent] with ⟨Hxp, Hxback⟩
          · iframe
          wp_auto
          ihave Hx := Hxback $$ Hxp
          icases Hx with ⟨Hx, Hsent⟩
          ihave Hwln := Hlback $$ Hlc
          ihave Hwrn := Hrback $$ Hrc
          wp_for_post
          obtain ⟨hinv2, hord2⟩ := adt.RbCtx.del_case2_L hinv' htxc hA.1 hA.2
          ihave Hw := adt.ownNode_node_close s 1 p w' .red wl' we' wr' $$
            [Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln Hwrn]
          · iexists wlp, wrp; iframe; ipureintro; exact Hwn
          ihave Hp := adt.ownNode_node_close s 1 pp' p cp' tx pe (.node .red wl' we' wr') $$
            [Hpiv Hpmx Hpl Hpr Hpp Hpc Hx Hw]
          · iexists x, w'; simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hpn'
          ihave HC := adt.ownCtxAt_ctx _ _ _ _ _ _ _ $$ HC
          ihave Hsent := adt.sentAt_other s x p p pp' Hpn'.1 $$ Hsent
          iframe
          iexists p, pp', CP', .node cp' tx pe (.node .red wl' we' wr')
          simp only [adt.maxEnd_node, adt.nodeMax_eq]
          iframe
          ipureintro; exact ⟨hinv2, hord2.trans hord'⟩
        · -- cases 3 and 4: `w`'s right child made red (case 3), then `P` rotated left
          rw [_root_.decide_eq_false hA]
          wp_auto
          wp_apply h_color wrp s wr'.color (DFrac.own 1) $$ [Hrc] as Hrc
          · iframe
          wp_join iprop(∃ (w2 : Loc) (wl2 : adt.RbT adt.Entry) (we2 : adt.Entry)
              (a2 : adt.RbT adt.Entry) (e2 : adt.Entry) (b2 : adt.RbT adt.Entry),
              w_ptr ↦ w2 ∗ x_ptr ↦ x ∗ ivt_ptr ↦ t ∗ t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
              adt.ownCtxAt t s (.inL cp' CP' pe (.node .black wl2 we2 (.node .red a2 e2 b2)))
                ((pp', w2) :: ls'') x p tx.maxEnd ∗
              adt.ownNode s 1 p x tx ∗ adt.sentAt s x p ∗
              ⌜(adt.RbCtx.inL cp' CP' pe (.node .black wl2 we2 (.node .red a2 e2 b2))).DelInv tx ∧
                ((adt.RbCtx.inL cp' CP' pe (.node .black wl2 we2 (.node .red a2 e2 b2))).plug
                  tx).inorder = (C0.plug tx0).inorder⌝)
            with [w x ivt Hs Hx Hsent Hpiv Hpmx Hpl Hpr Hpp Hpc HC Hwiv Hwmx Hwl Hwr Hwp Hwc Hlc Hrc
              Hlback Hrback] as ⟨%w2, %wl2, %we2, %a2, %e2, %b2, w, x, ivt, Hs, HC, Hx, Hsent,
                %Hinv3⟩
          · -- case 3: `w`'s left child black, `w` red, rotated right
            have hwr : wr'.color = .black := adt.colorW_inj Hif
            have hwl : wl'.color = .red := by
              cases h : wl'.color
              · rfl
              · exact absurd ⟨h, hwr⟩ hA
            obtain ⟨a, e1, b, rfl⟩ : ∃ a e1 b, wl' = .node .red a e1 b := by
              cases wl' with
              | leaf => simp at hwl
              | node c a e1 b => simp at hwl; subst hwl; exact ⟨a, e1, b, rfl⟩
            ihave Hwln := Hlback $$ Hlc
            icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hwln with
              ⟨%ap, %bp, %Hln, Hliv, Hlmx, Hll, Hlr, Hlp, Hlcc, Hlan, Hlbn⟩
            wp_auto
            ihave Hwrn := Hrback $$ Hrc
            ihave HCr := (adt.ownCtxAt_inR t s cp' tx pe CP' pp' x ls'' w' p
                (some (adt.nodeMax (.node .black a e1 b) we' wr'))).2
              $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hx]
            · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hpn'
            wp_apply h_rotateRight t s dq (.inR cp' tx pe CP') ((pp', x) :: ls'') w' p wlp ap bp wrp
                .red .black a b wr' we' e1 Hwn Hln
              $$ [Hs HCr Hwiv Hwmx Hwl Hwr Hwp Hwc Hliv Hlmx Hll Hlr Hlp Hlcc Hlan Hlbn Hwrn]
              as ⟨Hs, HCr, Hliv, Hlmx, Hll, Hlr, Hlp, Hlcc, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hlan,
                Hlbn, Hwrn⟩
            · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
            icases (adt.ownCtxAt_inR _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HCr with
              ⟨-, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hx, HC⟩
            icases adt.parentAt_open _ _ _ _ $$ [Hx Hsent] with ⟨Hxp, Hxback⟩
            · iframe
            wp_auto
            ihave Hx := Hxback $$ Hxp
            icases Hx with ⟨Hx, Hsent⟩
            obtain ⟨hinv3, hord3⟩ := adt.RbCtx.del_case3_L hinv' hwr
            ihave Hwn' := adt.ownNode_node_close s 1 wlp w' .red b we' wr' $$
              [Hwiv Hwmx Hwl Hwr Hwp Hwc Hlbn Hwrn]
            · iexists bp, wrp; iframe; ipureintro; exact Hwn
            ihave Hsib := adt.ownNode_node_close s 1 p wlp .black a e1 (.node .red b we' wr') $$
              [Hliv Hlmx Hll Hlr Hlp Hlcc Hlan Hwn']
            · iexists ap, w'; simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro
              exact Hln
            ihave HC := (adt.ownCtxAt_inL t s cp' CP' pe (.node .black a e1 (.node .red b we' wr'))
                pp' wlp ls'' x p tx.maxEnd).2 $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hsib]
            · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hpn'
            wp_join_done
            iexists wlp, a, e1, b, we', wr'
            iframe
            ipureintro; exact ⟨hinv3, hord3.trans hord'⟩
          · -- `w`'s right child red already
            have hwr : wr'.color = .red := by
              cases h : wr'.color
              · rfl
              · exact absurd (by rw [h]) Hif
            obtain ⟨a, e2, b, rfl⟩ : ∃ a e2 b, wr' = .node .red a e2 b := by
              cases wr' with
              | leaf => simp at hwr
              | node c a e2 b => simp at hwr; subst hwr; exact ⟨a, e2, b, rfl⟩
            ihave Hwln := Hlback $$ Hlc
            ihave Hwrn := Hrback $$ Hrc
            ihave Hw := adt.ownNode_node_close s 1 p w' .black wl' we' (.node .red a e2 b) $$
              [Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln Hwrn]
            · iexists wlp, wrp; iframe; ipureintro; exact Hwn
            ihave HC := (adt.ownCtxAt_inL t s cp' CP' pe (.node .black wl' we' (.node .red a e2 b))
                pp' w' ls'' x p tx.maxEnd).2 $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hw]
            · iframe; ipureintro; exact Hpn'
            iexists w', wl', we', a, e2, b
            iframe
            ipureintro; exact ⟨hinv', hord'⟩
          -- case 4: `w` takes `P`'s colour, `P` and `w`'s right child black, `P` rotated left
          obtain ⟨hinv3, hord3⟩ := Hinv3
          icases (adt.ownCtxAt_inL _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HC with
            ⟨%Hpn3, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hw, HC⟩
          icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hw with
            ⟨%wlp, %wrp, %Hwn, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hwln, Hwrn⟩
          icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hwrn with
            ⟨%ap, %bp, %Hrn, Hriv, Hrmx, Hrl, Hrr, Hrp, Hrc, Hran, Hrbn⟩
          icases adt.parentAt_open _ _ _ _ $$ [Hx Hsent] with ⟨Hxp, Hxback⟩
          · iframe
          ihave Hpc := adt.colorAt_intro s p cp' (DFrac.own 1) Hpn3.1 $$ Hpc
          wp_auto
          wp_apply h_color p s cp' (DFrac.own 1) $$ [Hpc] as Hpc
          · iframe
          ihave Hpc := adt.colorAt_elim s p cp' (DFrac.own 1) Hpn3.1 $$ Hpc
          wp_auto
          ihave Hx := Hxback $$ Hxp
          icases Hx with ⟨Hx, Hsent⟩
          ihave Hwrn := adt.ownNode_node_close s 1 w2 wrp .black a2 e2 b2 $$
            [Hriv Hrmx Hrl Hrr Hrp Hrc Hran Hrbn]
          · iexists ap, bp; iframe; ipureintro; exact Hrn
          wp_apply h_rotateLeft t s dq CP' ls'' p pp' w2 x wlp wrp .black cp' tx wl2
              (.node .black a2 e2 b2) pe we2 Hpn3 Hwn
            $$ [Hs HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hwiv Hwmx Hwl Hwr Hwp Hwc Hx Hwln Hwrn]
            as ⟨Hs, HC, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hx, Hwln,
              Hwrn⟩
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
          ihave Hp := adt.ownNode_node_close s 1 w2 p .black tx pe wl2 $$
            [Hpiv Hpmx Hpl Hpr Hpp Hpc Hx Hwln]
          · iexists x, wlp; iframe; ipureintro; exact Hpn3
          ihave Hw := adt.ownNode_node_close s 1 pp' w2 cp' (.node .black tx pe wl2) we2
              (.node .black a2 e2 b2) $$ [Hwiv Hwmx Hwl Hwr Hwp Hwc Hp Hwrn]
          · iexists p, wrp; simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro
            exact Hwn
          ihave HC := adt.ownCtxAt_ctx _ _ _ _ _ _ _ $$ HC
          icases adt.ownCtx_plug t s CP' w2 pp'
              (.node cp' (.node .black tx pe wl2) we2 (.node .black a2 e2 b2)) $$ [HC Hw]
            with ⟨%r, Hroot, HT⟩
          · simp only [adt.maxEnd_node, adt.nodeMax_eq]; iframe
          wp_auto
          wp_for_post
          obtain ⟨hinv4, hord4⟩ := adt.RbCtx.del_case4_L hinv3 htxc
          obtain ⟨c4, l4, e4, r4, hT⟩ := adt.RbCtx.plug_node CP' cp' (.node .black tx pe wl2) we2
            (.node .black a2 e2 b2)
          rw [hT] at hinv4 hord4
          rw [hT]
          ihave %Hrs := adt.ownNode_node_ne _ _ _ _ _ _ _ _ $$ HT
          icases adt.ownCtx_root t s r _ $$ [Hroot HT] with ⟨HC, HT⟩
          · iframe
          ihave Hsent := adt.sentAt_other s x p r s Hrs.1 $$ Hsent
          iframe
          iexists r, s, .top, .node c4 l4 e4 r4
          iframe
          ipureintro; exact ⟨hinv4, hord4.trans hord3⟩
      | inR cp tw pe CP =>
        cases ls with
        | nil => iexfalso; iapply adt.ownCtxAt_inR_nil $$ HC
        | cons f ls' =>
        obtain ⟨pp, wp⟩ := f
        obtain ⟨cw, wl, we, wr, rfl⟩ := adt.RbCtx.delInv_sib_R hinv
        icases (adt.ownCtxAt_inR _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HC with
          ⟨%Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hw, HC⟩
        ihave %Hwx := adt.ownNode_hole_ne_sib _ _ _ _ _ _ _ _ _ _ $$ Hx Hw
        icases adt.parentAt_open _ _ _ _ $$ [Hx Hsent] with ⟨Hxp, Hxback⟩
        · iframe
        wp_auto
        rw [_root_.decide_eq_false (Ne.symm Hwx)]
        wp_auto
        icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hw with
          ⟨%wlp, %wrp, %Hwn, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hwln, Hwrn⟩
        ihave Hwc := adt.colorAt_intro s wp cw (DFrac.own 1) Hwn.1 $$ Hwc
        wp_apply h_color wp s cw (DFrac.own 1) $$ [Hwc] as Hwc
        · iframe
        ihave Hwc := adt.colorAt_elim s wp cw (DFrac.own 1) Hwn.1 $$ Hwc
        rw [show red = #(adt.colorW .red) from rfl, show black = #(adt.colorW .black) from rfl]
        wp_join iprop(∃ (cp' : adt.RbColor) (CP' : adt.RbCtx adt.Entry) (pp' w' : Loc)
            (ls'' : List (Loc × Loc)) (wl' : adt.RbT adt.Entry) (we' : adt.Entry)
            (wr' : adt.RbT adt.Entry),
            w_ptr ↦ w' ∗ x_ptr ↦ x ∗ ivt_ptr ↦ t ∗ t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
            adt.ownCtxAt t s (.inR cp' (.node .black wl' we' wr') pe CP') ((pp', w') :: ls'') x p
              tx.maxEnd ∗
            adt.ownNode s 1 p x tx ∗ adt.sentAt s x p ∗
            ⌜(adt.RbCtx.inR cp' (.node .black wl' we' wr') pe CP').DelInv tx ∧
              ((adt.RbCtx.inR cp' (.node .black wl' we' wr') pe CP').plug tx).inorder =
                (C0.plug tx0).inorder⌝)
          with [w x ivt Hs Hpiv Hpmx Hpl Hpr Hpp Hpc HC Hxp Hxback Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln
            Hwrn] as ⟨%cp', %CP', %pp', %w', %ls'', %wl', %we', %wr', w, x, ivt, Hs, HC, Hx, Hsent,
              %Hinv'⟩
        · -- case 1: the sibling red: recoloured, `P` rotated right
          have hcw : cw = .red := by
            cases cw
            · rfl
            · exact absurd Hif (by decide)
          subst hcw
          ihave Hx := Hxback $$ Hxp
          icases Hx with ⟨Hx, Hsent⟩
          wp_apply h_rotateRight t s dq CP ls' p pp wp wlp wrp x .red .black wl wr tx pe we Hpn Hwn
            $$ [Hs HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hwiv Hwmx Hwl Hwr Hwp Hwc Hx Hwln Hwrn]
            as ⟨Hs, HC, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hwln, Hwrn,
              Hx⟩
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
          icases adt.parentAt_open _ _ _ _ $$ [Hx Hsent] with ⟨Hxp, Hxback⟩
          · iframe
          wp_auto
          ihave Hx := Hxback $$ Hxp
          icases Hx with ⟨Hx, Hsent⟩
          obtain ⟨hinv1, hwrc, hord1⟩ := adt.RbCtx.del_case1_R hinv
          ihave HC1 := (adt.ownCtxAt_inR t s .black wl we CP pp wlp ls' p wp
              (some (adt.nodeMaxO wr.maxEnd pe tx.maxEnd))).2
            $$ [HC Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln]
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hwn
          ihave HC2 := (adt.ownCtxAt_inR t s .red wr pe (.inR .black wl we CP) wp wrp
              ((pp, wlp) :: ls') x p tx.maxEnd).2
            $$ [HC1 Hpiv Hpmx Hpl Hpr Hpp Hpc Hwrn]
          · simp only [adt.nodeMax_eq]; iframe; ipureintro; exact Hpn
          obtain ⟨cw', wl', we', wr', rfl⟩ := adt.RbCtx.delInv_sib_R hinv1
          simp only [adt.RbT.color_node] at hwrc
          subst hwrc
          isplitl []
          · ipureintro; rfl
          iexists .red, .inR .black wl we CP, wp, wrp, (pp, wlp) :: ls', wl', we', wr'
          iframe
          ipureintro; exact ⟨hinv1, hord1.trans hord⟩
        · -- the sibling black
          have hcw : cw = .black := by
            cases cw
            · exact absurd rfl Hif
            · rfl
          subst hcw
          ihave Hx := Hxback $$ Hxp
          icases Hx with ⟨Hx, Hsent⟩
          ihave Hw := adt.ownNode_node_close s 1 p wp .black wl we wr $$
            [Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln Hwrn]
          · iexists wlp, wrp; iframe; ipureintro; exact Hwn
          ihave HC := (adt.ownCtxAt_inR t s cp (.node .black wl we wr) pe CP pp wp ls' x p
              tx.maxEnd).2 $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hw]
          · iframe; ipureintro; exact Hpn
          iexists cp, CP, pp, wp, ls', wl, we, wr
          iframe
          ipureintro; exact ⟨hinv, hord⟩
        -- the sibling black: `w`'s children's colours
        icases (adt.ownCtxAt_inR _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HC with
          ⟨%Hpn', Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hw, HC⟩
        icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hw with
          ⟨%wlp, %wrp, %Hwn, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hwln, Hwrn⟩
        rw [_root_.decide_eq_false Hwn.2]
        wp_auto
        icases adt.ownNode_colorAt _ _ _ _ $$ Hwln with ⟨Hlc, Hlback⟩
        icases adt.ownNode_colorAt _ _ _ _ $$ Hwrn with ⟨Hrc, Hrback⟩
        wp_join (Q := fun v => iprop(⌜v = #(decide (wl'.color = .black ∧ wr'.color = .black))⌝ ∗
            adt.colorAt s wlp wl'.color (DFrac.own 1) ∗ adt.colorAt s wrp wr'.color (DFrac.own 1) ∗
            w'.[intervalNode, go!"left"] ↦ wlp ∗ w'.[intervalNode, go!"right"] ↦ wrp ∗
            w_ptr ↦ w' ∗ ivt_ptr ↦ t ∗ t.[intervalTree, go!"sentinel"] ↦{dq} s))
          at (if: _ then _ else #false) with [Hlc Hrc Hwl Hwr w ivt Hs]
        · wp_apply h_color wlp s wl'.color (DFrac.own 1) $$ [Hlc] as Hlc
          · iframe
          cases hl : wl'.color with
          | red =>
            rw [show decide (adt.colorW .red = adt.colorW .black) = false by decide]
            wp_auto
            iframe
            ipureintro; simp
          | black =>
            rw [show decide (adt.colorW .black = adt.colorW .black) = true by decide]
            wp_auto
            wp_apply h_color wrp s wr'.color (DFrac.own 1) $$ [Hrc] as Hrc
            · iframe
            iframe
            cases hr : wr'.color with
            | red =>
              ipureintro; simp [show adt.colorW .red ≠ adt.colorW .black by decide]
            | black =>
              ipureintro; simp
        iintro ⟨%hv, Hlc, Hrc, Hwl, Hwr, w, ivt, Hs⟩
        subst hv
        obtain ⟨hinv', hord'⟩ := Hinv'
        by_cases hA : wl'.color = .black ∧ wr'.color = .black
        · -- case 2: both of `w`'s children black: `w` red, `x` moves up
          rw [_root_.decide_eq_true hA]
          wp_auto
          icases adt.parentAt_open _ _ _ _ $$ [Hx Hsent] with ⟨Hxp, Hxback⟩
          · iframe
          wp_auto
          ihave Hx := Hxback $$ Hxp
          icases Hx with ⟨Hx, Hsent⟩
          ihave Hwln := Hlback $$ Hlc
          ihave Hwrn := Hrback $$ Hrc
          wp_for_post
          obtain ⟨hinv2, hord2⟩ := adt.RbCtx.del_case2_R hinv' htxc hA.1 hA.2
          ihave Hw := adt.ownNode_node_close s 1 p w' .red wl' we' wr' $$
            [Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln Hwrn]
          · iexists wlp, wrp; iframe; ipureintro; exact Hwn
          ihave Hp := adt.ownNode_node_close s 1 pp' p cp' (.node .red wl' we' wr') pe tx $$
            [Hpiv Hpmx Hpl Hpr Hpp Hpc Hw Hx]
          · iexists w', x; simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hpn'
          ihave HC := adt.ownCtxAt_ctx _ _ _ _ _ _ _ $$ HC
          ihave Hsent := adt.sentAt_other s x p p pp' Hpn'.1 $$ Hsent
          iframe
          iexists p, pp', CP', .node cp' (.node .red wl' we' wr') pe tx
          simp only [adt.maxEnd_node, adt.nodeMax_eq]
          iframe
          ipureintro; exact ⟨hinv2, hord2.trans hord'⟩
        · -- cases 3 and 4: `w`'s left child made red (case 3), then `P` rotated right
          rw [_root_.decide_eq_false hA]
          wp_auto
          wp_apply h_color wlp s wl'.color (DFrac.own 1) $$ [Hlc] as Hlc
          · iframe
          wp_join iprop(∃ (w2 : Loc) (a2 : adt.RbT adt.Entry) (e2 : adt.Entry) (b2 : adt.RbT adt.Entry)
              (we2 : adt.Entry) (wr2 : adt.RbT adt.Entry),
              w_ptr ↦ w2 ∗ x_ptr ↦ x ∗ ivt_ptr ↦ t ∗ t.[intervalTree, go!"sentinel"] ↦{dq} s ∗
              adt.ownCtxAt t s (.inR cp' (.node .black (.node .red a2 e2 b2) we2 wr2) pe CP')
                ((pp', w2) :: ls'') x p tx.maxEnd ∗
              adt.ownNode s 1 p x tx ∗ adt.sentAt s x p ∗
              ⌜(adt.RbCtx.inR cp' (.node .black (.node .red a2 e2 b2) we2 wr2) pe CP').DelInv tx ∧
                ((adt.RbCtx.inR cp' (.node .black (.node .red a2 e2 b2) we2 wr2) pe CP').plug
                  tx).inorder = (C0.plug tx0).inorder⌝)
            with [w x ivt Hs Hx Hsent Hpiv Hpmx Hpl Hpr Hpp Hpc HC Hwiv Hwmx Hwl Hwr Hwp Hwc Hlc Hrc
              Hlback Hrback] as ⟨%w2, %a2, %e2, %b2, %we2, %wr2, w, x, ivt, Hs, HC, Hx, Hsent,
                %Hinv3⟩
          · -- case 3: `w`'s right child black, `w` red, rotated left
            have hwl : wl'.color = .black := adt.colorW_inj Hif
            have hwr : wr'.color = .red := by
              cases h : wr'.color
              · rfl
              · exact absurd ⟨hwl, h⟩ hA
            obtain ⟨a, e1, b, rfl⟩ : ∃ a e1 b, wr' = .node .red a e1 b := by
              cases wr' with
              | leaf => simp at hwr
              | node c a e1 b => simp at hwr; subst hwr; exact ⟨a, e1, b, rfl⟩
            ihave Hwrn := Hrback $$ Hrc
            icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hwrn with
              ⟨%ap, %bp, %Hrn, Hriv, Hrmx, Hrl, Hrr, Hrp, Hrcc, Hran, Hrbn⟩
            wp_auto
            ihave Hwln := Hlback $$ Hlc
            ihave HCl := (adt.ownCtxAt_inL t s cp' CP' pe tx pp' x ls'' w' p
                (some (adt.nodeMax wl' we' (.node .black a e1 b)))).2
              $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hx]
            · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hpn'
            wp_apply h_rotateLeft t s dq (.inL cp' CP' pe tx) ((pp', x) :: ls'') w' p wrp wlp ap bp
                .red .black wl' a b we' e1 Hwn Hrn
              $$ [Hs HCl Hwiv Hwmx Hwl Hwr Hwp Hwc Hriv Hrmx Hrl Hrr Hrp Hrcc Hwln Hran Hrbn]
              as ⟨Hs, HCl, Hriv, Hrmx, Hrl, Hrr, Hrp, Hrcc, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hwln,
                Hran, Hrbn⟩
            · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
            icases (adt.ownCtxAt_inL _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HCl with
              ⟨-, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hx, HC⟩
            icases adt.parentAt_open _ _ _ _ $$ [Hx Hsent] with ⟨Hxp, Hxback⟩
            · iframe
            wp_auto
            ihave Hx := Hxback $$ Hxp
            icases Hx with ⟨Hx, Hsent⟩
            obtain ⟨hinv3, hord3⟩ := adt.RbCtx.del_case3_R hinv' hwl
            ihave Hwn' := adt.ownNode_node_close s 1 wrp w' .red wl' we' a $$
              [Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln Hran]
            · iexists wlp, ap; iframe; ipureintro; exact Hwn
            ihave Hsib := adt.ownNode_node_close s 1 p wrp .black (.node .red wl' we' a) e1 b $$
              [Hriv Hrmx Hrl Hrr Hrp Hrcc Hwn' Hrbn]
            · iexists w', bp; simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro
              exact Hrn
            ihave HC := (adt.ownCtxAt_inR t s cp' (.node .black (.node .red wl' we' a) e1 b) pe CP'
                pp' wrp ls'' x p tx.maxEnd).2 $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hsib]
            · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro; exact Hpn'
            wp_join_done
            iexists wrp, wl', we', a, e1, b
            iframe
            ipureintro; exact ⟨hinv3, hord3.trans hord'⟩
          · -- `w`'s left child red already
            have hwl : wl'.color = .red := by
              cases h : wl'.color
              · rfl
              · exact absurd (by rw [h]) Hif
            obtain ⟨a, e2, b, rfl⟩ : ∃ a e2 b, wl' = .node .red a e2 b := by
              cases wl' with
              | leaf => simp at hwl
              | node c a e2 b => simp at hwl; subst hwl; exact ⟨a, e2, b, rfl⟩
            ihave Hwln := Hlback $$ Hlc
            ihave Hwrn := Hrback $$ Hrc
            ihave Hw := adt.ownNode_node_close s 1 p w' .black (.node .red a e2 b) we' wr' $$
              [Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln Hwrn]
            · iexists wlp, wrp; iframe; ipureintro; exact Hwn
            ihave HC := (adt.ownCtxAt_inR t s cp' (.node .black (.node .red a e2 b) we' wr') pe CP'
                pp' w' ls'' x p tx.maxEnd).2 $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hw]
            · iframe; ipureintro; exact Hpn'
            iexists w', a, e2, b, we', wr'
            iframe
            ipureintro; exact ⟨hinv', hord'⟩
          -- case 4: `w` takes `P`'s colour, `P` and `w`'s left child black, `P` rotated right
          obtain ⟨hinv3, hord3⟩ := Hinv3
          icases (adt.ownCtxAt_inR _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HC with
            ⟨%Hpn3, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hw, HC⟩
          icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hw with
            ⟨%wlp, %wrp, %Hwn, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hwln, Hwrn⟩
          icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hwln with
            ⟨%ap, %bp, %Hln, Hliv, Hlmx, Hll, Hlr, Hlp, Hlc, Hlan, Hlbn⟩
          icases adt.parentAt_open _ _ _ _ $$ [Hx Hsent] with ⟨Hxp, Hxback⟩
          · iframe
          ihave Hpc := adt.colorAt_intro s p cp' (DFrac.own 1) Hpn3.1 $$ Hpc
          wp_auto
          wp_apply h_color p s cp' (DFrac.own 1) $$ [Hpc] as Hpc
          · iframe
          ihave Hpc := adt.colorAt_elim s p cp' (DFrac.own 1) Hpn3.1 $$ Hpc
          wp_auto
          ihave Hx := Hxback $$ Hxp
          icases Hx with ⟨Hx, Hsent⟩
          ihave Hwln := adt.ownNode_node_close s 1 w2 wlp .black a2 e2 b2 $$
            [Hliv Hlmx Hll Hlr Hlp Hlc Hlan Hlbn]
          · iexists ap, bp; iframe; ipureintro; exact Hln
          wp_apply h_rotateRight t s dq CP' ls'' p pp' w2 wlp wrp x .black cp'
              (.node .black a2 e2 b2) wr2 tx pe we2 Hpn3 Hwn
            $$ [Hs HC Hpiv Hpmx Hpl Hpr Hpp Hpc Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln Hwrn Hx]
            as ⟨Hs, HC, Hwiv, Hwmx, Hwl, Hwr, Hwp, Hwc, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, Hwln, Hwrn,
              Hx⟩
          · simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe
          ihave Hp := adt.ownNode_node_close s 1 w2 p .black wr2 pe tx $$
            [Hpiv Hpmx Hpl Hpr Hpp Hpc Hwrn Hx]
          · iexists wrp, x; iframe; ipureintro; exact Hpn3
          ihave Hw := adt.ownNode_node_close s 1 pp' w2 cp' (.node .black a2 e2 b2) we2
              (.node .black wr2 pe tx) $$ [Hwiv Hwmx Hwl Hwr Hwp Hwc Hwln Hp]
          · iexists wlp, p; simp only [adt.nodeMax_eq, adt.maxEnd_node]; iframe; ipureintro
            exact Hwn
          ihave HC := adt.ownCtxAt_ctx _ _ _ _ _ _ _ $$ HC
          icases adt.ownCtx_plug t s CP' w2 pp'
              (.node cp' (.node .black a2 e2 b2) we2 (.node .black wr2 pe tx)) $$ [HC Hw]
            with ⟨%r, Hroot, HT⟩
          · simp only [adt.maxEnd_node, adt.nodeMax_eq]; iframe
          wp_auto
          wp_for_post
          obtain ⟨hinv4, hord4⟩ := adt.RbCtx.del_case4_R hinv3 htxc
          obtain ⟨c4, l4, e4, r4, hT⟩ := adt.RbCtx.plug_node CP' cp' (.node .black a2 e2 b2) we2
            (.node .black wr2 pe tx)
          rw [hT] at hinv4 hord4
          rw [hT]
          ihave %Hrs := adt.ownNode_node_ne _ _ _ _ _ _ _ _ $$ HT
          icases adt.ownCtx_root t s r _ $$ [Hroot HT] with ⟨HC, HT⟩
          · iframe
          ihave Hsent := adt.sentAt_other s x p r s Hrs.1 $$ Hsent
          iframe
          iexists r, s, .top, .node c4 l4 e4 r4
          iframe
          ipureintro; exact ⟨hinv4, hord4.trans hord3⟩

end proof

end EtcdGrove
end Perennial
