/-
`intervalTree.Delete` (`interval_tree.go`) over a comparator: the proof of
`Spec/.../adt/intervalTree__Delete_gen.lean` (unit 4c, generalized in the auth plan's S2b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Delete_gen
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__find
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__successor
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__updateMax
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__color
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__deleteFixup
public import Proof.go_etcd_io.etcd.pkg.v3.adt.TreeDelete

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `Delete`'s end: the tree struct with the new root and the count decremented, an entry with
the interval removed. -/
theorem adt.del_post (K : adt.KeyRep (GF := GF)) (t s R : Loc) (cnt : w64)
    (T' : adt.RbT adt.Entry) (L : List adt.Entry)
    (i : Nat) (ze : adt.Entry) (b e : GoString) (htn : t ≠ null) (hget : L[i]? = some ze)
    (hz : ze.1 = (b, e)) (hT' : T'.inorder = L.eraseIdx i) (hrb : adt.RbOk T')
    (hs : adt.IvSorted L) (hc : cnt = W64 L.length) (hlen : L.length < 2 ^ 63) :
    t.[intervalTree, go!"root"] ↦ R ∗ t.[intervalTree, go!"count"] ↦ (cnt - W64 1) ∗
      t.[intervalTree, go!"sentinel"] ↦ s ∗ adt.ownSentinel s (DFrac.own 1) ∗
      adt.ownNode (GF := GF) K s (DFrac.own 1) s R T' ⊢
      ∃ L' : List adt.Entry,
        ⌜if (b, e) ∈ L.map Prod.fst then
            ∃ (i : Nat) (z : adt.Entry), L[i]? = some z ∧ z.1 = (b, e) ∧ L' = L.eraseIdx i
          else L' = L⌝ ∗ adt.ownIvtK K t L' (DFrac.own 1) := by
  iintro ⟨Hr, Hc, Hs, Hsent, HT⟩
  have hin : (b, e) ∈ L.map Prod.fst :=
    List.mem_map.2 ⟨ze, List.mem_of_getElem? hget, hz⟩
  have hi : i < L.length := by
    rcases Nat.lt_or_ge i L.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hget; cases hget
  iexists L.eraseIdx i
  isplitl []
  · ipureintro; rw [ite_eq_left_of_eq_true _ _ (eq_true hin)]; exact ⟨i, ze, hget, hz, rfl⟩
  unfold adt.ownIvtK
  ihave Ht := adt.ivt_combine t R s (cnt - W64 1) htn $$ [Hr Hc Hs]
  · iframe
  iexists { root' := R, count' := cnt - W64 1, sentinel' := s }, T'
  iframe
  ipureintro
  have hl' : (L.eraseIdx i).length = L.length - 1 := List.length_eraseIdx_of_lt hi
  refine ⟨hT', hrb, hs.sublist (List.eraseIdx_sublist _ _), ?_, by omega⟩
  rw [hl', hc]
  have : 1 ≤ L.length := by omega
  word

theorem adt.intervalTree.Delete_gen.wp_proof
    (h_find : adt.intervalTree.find.spec (GF := GF) (hG := hG))
    (h_successor : adt.intervalNode.successor.spec (GF := GF) (hG := hG))
    (h_updateMax : adt.intervalNode.updateMax.spec (GF := GF) (hG := hG))
    (h_color : adt.intervalNode.color.spec (GF := GF) (hG := hG))
    (h_deleteFixup : adt.intervalTree.deleteFixup.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Delete_gen.spec (GF := GF) (hG := hG) := by
  intro K hK t L vb ve db de b e
  wp_start as ⟨Ht, Hkb, Hke⟩
  ihave %Htn := adt.ownIvtK_not_null K _ _ _ $$ Ht
  unfold adt.ownIvtK
  icases Ht with ⟨%tv, %T, Ht, Hsent, Hn, %Hp⟩
  obtain ⟨hTL, hrb, hsorted, hcnt, hlen⟩ := Hp
  icases adt.ivt_fields _ _ _ $$ Ht with ⟨Hr, Hc, Hs, -⟩
  wp_auto
  wp_apply (h_find K hK) t tv (DFrac.own 1) T vb ve db de b e $$ [Hr Hs Hn Hkb Hke]
    as %z ⟨Hr, Hs, Hkb, Hke, %pz, %C, %ls, %Tz, HP, Hz, %HTz⟩
  · iframe
  obtain ⟨Htop, Hplug, HTz⟩ := HTz
  cases hf : T.findE (b, e) with
  | none =>
    -- not found: the tree unchanged
    rw [hf] at HTz
    subst HTz
    have hnot := adt.findE_none (b, e) T (by rw [hTL]; exact hsorted) hf
    rw [hTL] at hnot
    rw [_root_.decide_eq_false hnot]
    icases adt.ownNode_leaf_open K _ _ _ _ $$ Hz with %Hzs
    rw [Hzs, _root_.decide_eq_true (rfl : tv.sentinel' = tv.sentinel')]
    wp_auto
    iapply HΦ
    iframe Hkb Hke
    iexists L
    isplitl []
    · ipureintro; simp [hnot]
    iexists tv, T
    iframe Hsent
    ihave Ht := adt.ivt_combine t tv.root' tv.sentinel' tv.count' Htn $$ [Hr Hc Hs]
    · iframe
    iframe Ht
    isplitl [HP Hz]
    · rw [← Hplug]
      rw [Hzs] at Htop
      iapply adt.ownPathAt_plug' K _ _ _ _ _ _ _ _ _ Htop
      iframe
    ipureintro; exact ⟨hTL, hrb, hsorted, hcnt, hlen⟩
  | some ze =>
    rw [hf] at HTz
    obtain ⟨cz, l, r, rfl⟩ := HTz
    obtain ⟨hzm, hz1⟩ := adt.findE_some _ T ze hf
    have hin : (b, e) ∈ L.map Prod.fst := List.mem_map.2 ⟨ze, hTL ▸ hzm, hz1⟩
    rw [_root_.decide_eq_true hin]
    icases adt.ownNode_node_open K _ _ _ _ _ _ _ _ $$ Hz with
      ⟨%lp, %rp, %Hzn, Hziv, Hzmx, Hzl, Hzr, Hzp, Hzc, Hzln, Hzrn⟩
    rw [_root_.decide_eq_false Hzn.1]
    ihave HC : adt.ownCtxAt K t tv.sentinel' C ls z pz (some (adt.nodeMax l ze r)) $$ [HP Hr]
    · unfold adt.ownCtxAt; rw [Htop]; iframe; ipureintro; rfl
    wp_auto
    ihave %Hlp := adt.ownNode_leaf_iff K _ _ _ _ _ $$ Hzln
    ihave %Hrp := adt.ownNode_leaf_iff K _ _ _ _ _ $$ Hzrn
    wp_join (v := #(decide (lp ≠ tv.sentinel' ∧ rp ≠ tv.sentinel')))
      at (if: _ then _ else #false) with [z Hzr ivt Hs]
    · by_cases hl : lp = tv.sentinel'
      · rw [_root_.decide_eq_true hl]
        wp_auto
        iframe
        ipureintro; simp [hl]
      · rw [_root_.decide_eq_false hl]
        wp_auto
        iframe
        ipureintro
        by_cases hr : rp = tv.sentinel' <;> simp [hl, hr]
    by_cases hB : lp ≠ tv.sentinel' ∧ rp ≠ tv.sentinel'
    · -- `z` has two children: its successor `y` (the leftmost node of its right subtree) is
      -- spliced out and its entry copied into `z`
      rw [_root_.decide_eq_true hB]
      wp_auto
      have hrl : r ≠ .leaf := fun h => hB.2 (Hrp.2 h)
      wp_apply (h_successor K hK) z tv.sentinel' rp r hrl $$ [Hzr Hzrn]
        as %y ⟨Hzr, %A, %lsA, %yp, %cy, %ye, %yr, HA, Hy, %HyA⟩
      · iframe
      obtain ⟨HAtop, HAplug, HAall⟩ := HyA
      icases adt.ownNode_node_open K _ _ _ _ _ _ _ _ $$ Hy with
        ⟨%ylp, %yrp, %Hyn, Hyiv, Hymx, Hyl, Hyr, Hyp, Hyc, Hyln, Hyrn⟩
      icases adt.ownNode_leaf_open K _ _ _ _ $$ Hyln with %Hyl0
      subst Hyl0
      wp_auto
      wp_join iprop(x_ptr ↦ yrp ∗ y_ptr ↦ y ∗ y.[intervalNode, go!"right"] ↦ yrp)
        with [x y Hyr] as ⟨x, y, Hyr⟩
      -- the splice: `x` in `y`'s place, `y`'s parent's `max` recomputed
      icases adt.parent_write K _ _ _ _ $$ [Hyrn Hsent] with ⟨%v, Hxp, Hxback⟩
      · iframe
      wp_auto
      ihave Hx := Hxback $$ %yp Hxp
      icases Hx with ⟨Hx, Hsent⟩
      wp_join iprop(∃ (lsB : List (Loc × Loc)) (zr' : Loc),
          adt.ownPathAt K tv.sentinel' (DFrac.own 1) A lsB yrp yp yr.maxEnd ∗
          ⌜adt.topAt A lsB yrp yp = (zr', z)⌝ ∗ adt.ownNode K tv.sentinel' (DFrac.own 1) yp yrp yr ∗
          K.ivAt z.[intervalNode, go!"iv"] (DFrac.own 1) ze ∗
          K.maxAt z.[intervalNode, go!"max"] (DFrac.own 1) (adt.nodeMaxO l.maxEnd ze (A.upMax yr.maxEnd)) ∗
          z.[intervalNode, go!"left"] ↦ lp ∗ z.[intervalNode, go!"right"] ↦ zr' ∗
          z.[intervalNode, go!"parent"] ↦ pz ∗ z.[intervalNode, go!"c"] ↦ adt.colorW cz ∗
          adt.ownNode K tv.sentinel' (DFrac.own 1) z lp l ∗
          adt.ownCtxAt K t tv.sentinel' C ls z pz
            (some (adt.nodeMaxO l.maxEnd ze (A.upMax yr.maxEnd))) ∗
          y.[intervalNode, go!"parent"] ↦ yp ∗ y_ptr ↦ y ∗ x_ptr ↦ yrp ∗ ivt_ptr ↦ t ∗
          t.[intervalTree, go!"sentinel"] ↦ tv.sentinel')
        at next with [HA Hx Hziv Hzmx Hzl Hzr Hzp Hzc Hzln HC Hyp y x ivt Hs]
        as ⟨%lsB, %zr', HP, %HPtop, Hx, Hziv, Hzmx, Hzl, Hzr, Hzp, Hzc, Hzln, HC, Hyp, y, x, ivt, Hs⟩
      · cases A with
        | inR c' l' e' A' => exact HAall.elim
        | top =>
          cases lsA with
          | cons f lsA => iexfalso; rw [adt.ownPathAt_top_cons]; icases HA with %h; exact h.elim
          | nil =>
          simp only [adt.topAt_top, Prod.mk.injEq] at HAtop
          obtain ⟨hy, hyp⟩ := HAtop
          subst hy
          have hyp' : z = yp := hyp.symm
          subst hyp'
          ihave %Hne := adt.ownNode_ne K _ _ _ _ _ _ Hyn.1 $$ Hzln Hyp
          rw [_root_.decide_eq_false Hzn.1]
          wp_auto
          rw [_root_.decide_eq_false (Ne.symm Hne)]
          wp_auto
          icases adt.ownNode_childMax K _ _ _ l $$ Hzln with ⟨Hlm, Hlback⟩
          icases adt.ownNode_childMax K _ _ _ yr $$ Hx with ⟨Hxm, Hxback⟩
          wp_apply (h_updateMax K hK) t tv.sentinel' C ls z pz lp yrp ze (adt.nodeMax l ze r) l.maxEnd
              yr.maxEnd Hzn.1
            $$ [HC Hziv Hzmx Hzl Hzr Hzp Hlm Hxm] as ⟨HC, Hziv, Hzmx, Hzl, Hzr, Hzp, Hlm, Hxm⟩
          · iframe
          ihave Hzln := Hlback $$ Hlm
          ihave Hx := Hxback $$ Hxm
          wp_join_done
          iexists [], yrp
          simp only [adt.topAt_top, adt.RbCtx.upMax]
          iframe
          iapply adt.ownPathAt_top_intro
        | inL cA A' eA rA =>
          cases lsA with
          | nil => iexfalso; rw [adt.ownPathAt_inL_nil]; icases HA with %h; exact h.elim
          | cons f lsA' =>
          obtain ⟨ppy, rAp⟩ := f
          simp only [adt.topAt_inL] at HAtop
          rw [adt.ownPathAt_inL]
          icases HA with ⟨%Hypn, Hypiv, Hypmx, Hypl, Hypr, Hypp, Hypc, HrA, HA'⟩
          ihave %HlenA := adt.ownPathAt_length K _ _ _ _ _ _ _ $$ HA'
          rw [_root_.decide_eq_false Hypn.1]
          wp_auto
          -- `y`'s parent's `max` recomputed, up the path to `z` and on to the root
          have hrmax : r.maxEnd =
              A'.upMax (some (adt.nodeMaxO (some (adt.nodeMax .leaf ye yr)) eA rA.maxEnd)) := by
            rw [← HAplug, adt.maxEnd_plug]; rfl
          have hzmax : adt.nodeMax l ze r = adt.nodeMaxO l.maxEnd ze
              (A'.upMax (some (adt.nodeMaxO (some (adt.nodeMax .leaf ye yr)) eA rA.maxEnd))) := by
            rw [adt.nodeMax_eq, hrmax]
          rw [hzmax]
          ihave HD := (adt.ownCtxAt_inR K t tv.sentinel' cz l ze C pz lp ls rp z
              (A'.upMax (some (adt.nodeMaxO (some (adt.nodeMax .leaf ye yr)) eA rA.maxEnd)))).2
            $$ [HC Hziv Hzmx Hzl Hzr Hzp Hzc Hzln]
          · iframe; ipureintro; exact Hzn
          ihave HCy := adt.ownCtxAt_comp K t tv.sentinel' (.inR cz l ze C) ((pz, lp) :: ls) rp z A'
              lsA' yp ppy _ HAtop $$ [HA' HD]
          · iframe
          icases adt.ownNode_childMax K _ _ _ yr $$ Hx with ⟨Hxm, Hxback⟩
          icases adt.ownNode_childMax K _ _ _ rA $$ HrA with ⟨HrAm, HrAback⟩
          wp_apply (h_updateMax K hK) t tv.sentinel' (A'.comp (.inR cz l ze C)) (lsA' ++ (pz, lp) :: ls)
              yp ppy yrp rAp eA (adt.nodeMaxO (some (adt.nodeMax .leaf ye yr)) eA rA.maxEnd)
              yr.maxEnd rA.maxEnd Hypn.1
            $$ [HCy Hypiv Hypmx Hypl Hypr Hypp Hxm HrAm]
            as ⟨HCy, Hypiv, Hypmx, Hypl, Hypr, Hypp, Hxm, HrAm⟩
          · iframe
          ihave Hx := Hxback $$ Hxm
          ihave HrA := HrAback $$ HrAm
          icases adt.ownCtxAt_split K t tv.sentinel' (.inR cz l ze C) ((pz, lp) :: ls) A' lsA' yp ppy
              _ HlenA $$ HCy with ⟨HA', HD⟩
          rw [HAtop]
          icases (adt.ownCtxAt_inR K _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HD with
            ⟨-, Hziv, Hzmx, Hzl, Hzr, Hzp, Hzc, Hzln, HC⟩
          ihave HP : adt.ownPathAt K tv.sentinel' (DFrac.own 1) (.inL cA A' eA rA) ((ppy, rAp) :: lsA') yrp yp
              yr.maxEnd $$ [HA' Hypiv Hypmx Hypl Hypr Hypp Hypc HrA]
          · rw [adt.ownPathAt_inL]; iframe; ipureintro; exact Hypn
          wp_join_done
          iexists (ppy, rAp) :: lsA', rp
          iframe
          ipureintro; simp only [adt.topAt_inL]; exact HAtop
      -- `y`'s entry copied into `z`, `z`'s `max` recomputed (and up to the root)
      ihave %Hyz := adt.parent_ne _ _ _ _ $$ Hyp Hzp
      rw [_root_.decide_eq_false Hyz]
      icases K.ivAt_open_raw _ _ _ $$ Hyiv with ⟨%yb, %yye, Hyiv, #Hkyb, #Hkye⟩
      icases K.ivAt_open_raw _ _ _ $$ Hziv with ⟨%zb, %zze, Hziv, -, -⟩
      wp_auto
      ihave Hziv := K.ivAt_intro _ _ _ yb yye $$ [Hziv]
      · iframe ∗ #
      icases adt.ownNode_childMax K _ _ _ l $$ Hzln with ⟨Hlm, Hlback⟩
      icases adt.ownPathAt_childMax K _ _ _ _ _ _ $$ [HP Hx] with ⟨Hrm, Hrback⟩
      · iframe
      rw [HPtop]
      wp_apply (h_updateMax K hK) t tv.sentinel' C ls z pz lp zr' ye
          (adt.nodeMaxO l.maxEnd ze (A.upMax yr.maxEnd)) l.maxEnd (A.upMax yr.maxEnd) Hzn.1
        $$ [HC Hziv Hzmx Hzl Hzr Hzp Hlm Hrm] as ⟨HC, Hziv, Hzmx, Hzl, Hzr, Hzp, Hlm, Hrm⟩
      · iframe
      ihave Hzln := Hlback $$ Hlm
      ihave HPx := Hrback $$ Hrm
      icases HPx with ⟨HP, Hx⟩
      ihave HD := (adt.ownCtxAt_inR K t tv.sentinel' cz l ye C pz lp ls zr' z
          (A.upMax yr.maxEnd)).2 $$ [HC Hziv Hzmx Hzl Hzr Hzp Hzc Hzln]
      · iframe; ipureintro; exact Hzn
      ihave HC := adt.ownCtxAt_comp K t tv.sentinel' (.inR cz l ye C) ((pz, lp) :: ls) zr' z A lsB
          yrp yp yr.maxEnd HPtop $$ [HP HD]
      · iframe
      -- `y`'s colour: the fixup if black
      have hrb' : (C.plug (.node cz l ze r)).redOk ∧ (C.plug (.node cz l ze r)).blackHeight.isSome ∧
          (C.plug (.node cz l ze r)).color = .black := by rw [Hplug]; exact hrb
      have hrb2 := adt.RbCtx.rb_entry C cz l ze ye r hrb'.1 hrb'.2.1 hrb'.2.2
      rw [← HAplug, show C.plug (.node cz l ye (A.plug (.node cy .leaf ye yr))) =
        (A.comp (.inR cz l ye C)).plug (.node cy .leaf ye yr) by rw [adt.RbCtx.plug_comp]; rfl]
        at hrb2
      obtain ⟨hstB, hstR⟩ := adt.RbCtx.del_start (A.comp (.inR cz l ye C)) cy .leaf ye yr yr
        (Or.inl ⟨rfl, rfl⟩) hrb2.1 hrb2.2.1 hrb2.2.2
      obtain ⟨hget, hord⟩ := adt.RbCtx.del_inorder_two C A cz l ze cy ye yr HAall
      rw [HAplug] at hget hord
      ihave Hyc := adt.colorAt_intro tv.sentinel' y cy (DFrac.own 1) Hyn.1 $$ Hyc
      wp_apply h_color y tv.sentinel' cy (DFrac.own 1) $$ [Hyc] as Hyc
      · iframe
      wp_join iprop(∃ (R : Loc) (T' : adt.RbT adt.Entry), t.[intervalTree, go!"root"] ↦ R ∗
          adt.ownNode K tv.sentinel' (DFrac.own 1) tv.sentinel' R T' ∗ adt.ownSentinel tv.sentinel' (DFrac.own 1) ∗
          x_ptr ↦ yrp ∗ ivt_ptr ↦ t ∗ t.[intervalTree, go!"sentinel"] ↦ tv.sentinel' ∗
          ⌜adt.RbOk T' ∧ T'.inorder = ((A.comp (.inR cz l ye C)).plug yr).inorder⌝)
        with [HC Hx Hsent x ivt Hs] as ⟨%R, %T', Hroot, HT, Hsent, x, ivt, Hs, %HT'⟩
      · have hcy : cy = .black := adt.colorW_inj Hif
        ihave HC := adt.ownCtxAt_ctx K _ _ _ _ _ _ _ $$ HC
        wp_apply (h_deleteFixup K hK) t tv.sentinel' (DFrac.own 1) (A.comp (.inR cz l ye C)) yrp yp yr
            (hstB hcy)
          $$ [Hs HC Hx Hsent] as ⟨Hs, Hsent, %R, %T', Hroot, HT, %HT'⟩
        · iframe
        wp_join_done
        iexists R, T'
        iframe
        ipureintro; exact HT'
      · have hcy : cy = .red := by
          cases cy
          · rfl
          · exact absurd rfl Hif
        ihave HC := adt.ownCtxAt_ctx K _ _ _ _ _ _ _ $$ HC
        icases adt.ownCtx_plug K _ _ _ _ _ _ $$ [HC Hx] with ⟨%R, Hroot, HT⟩
        · iframe
        ihave Hsent := adt.sentAt_ownSentinel _ _ _ $$ Hsent
        iexists R, (A.comp (.inR cz l ye C)).plug yr
        iframe
        ipureintro; exact ⟨hstR hcy, rfl⟩
      iapply HΦ
      iframe Hkb Hke
      have hpost := adt.del_post (GF := GF) K t tv.sentinel' R tv.count' T' L _ ze b e Htn
        (by rw [← hTL, ← Hplug]; exact hget) hz1 (by rw [HT'.2, hord, Hplug, hTL]) HT'.1 hsorted
        hcnt hlen
      unfold adt.ownIvtK at hpost
      iapply hpost
      iframe
    · -- `z` has at most one child: it is spliced out
      rw [_root_.decide_eq_false hB]
      wp_auto
      wp_join iprop(x_ptr ↦ (if lp = tv.sentinel' then rp else lp) ∗ y_ptr ↦ z ∗
          z.[intervalNode, go!"left"] ↦ lp ∗ z.[intervalNode, go!"right"] ↦ rp ∗ ivt_ptr ↦ t ∗
          t.[intervalTree, go!"sentinel"] ↦ tv.sentinel')
        with [x y Hzl Hzr ivt Hs] as ⟨x, y, Hzl, Hzr, ivt, Hs⟩
      · try simp only [↓reduceIte]
        wp_if_destruct
        · wp_join_done
        · isplitl []
          · ipureintro; first | rfl | trivial
          iframe
      · simp only [Hif, ↓reduceIte]
        iframe
      have hx : (l = .leaf ∧ (if lp = tv.sentinel' then r else l) = r) ∨
          (r = .leaf ∧ (if lp = tv.sentinel' then r else l) = l) := by
        by_cases hl : lp = tv.sentinel'
        · left; simp only [hl, ↓reduceIte]; exact ⟨Hlp.1 hl, trivial⟩
        · right; simp only [hl, ↓reduceIte]
          exact ⟨Hrp.1 (Classical.byContradiction fun hr => hB ⟨hl, hr⟩), trivial⟩
      icases adt.ownNode_one_child K tv.sentinel' z lp rp l r $$ [Hzln Hzrn] with Hx
      · iframe
      generalize hxl : (if lp = tv.sentinel' then rp else lp) = xl at *
      generalize htx : (if lp = tv.sentinel' then r else l) = tx at *
      icases adt.parent_write K _ _ _ _ $$ [Hx Hsent] with ⟨%v, Hxp, Hxback⟩
      · iframe
      wp_auto
      ihave Hx := Hxback $$ %pz Hxp
      icases Hx with ⟨Hx, Hsent⟩
      ihave %Hpar := adt.ownCtxAt_parent K _ _ _ _ _ _ _ $$ HC
      -- the splice: `x` in `z`'s place
      wp_join iprop(adt.ownCtxAt K t tv.sentinel' C ls xl pz tx.maxEnd ∗
          adt.ownNode K tv.sentinel' (DFrac.own 1) pz xl tx ∗ z.[intervalNode, go!"parent"] ↦ pz ∗
          y_ptr ↦ z ∗ x_ptr ↦ xl ∗ ivt_ptr ↦ t ∗ t.[intervalTree, go!"sentinel"] ↦ tv.sentinel')
        with [HC Hx Hzp y x ivt Hs] as ⟨HC, Hx, Hzp, y, x, ivt, Hs⟩
      · -- `z` was the root
        have hC : C = .top := Hpar.2 rfl
        subst hC
        cases ls with
        | cons f ls => iexfalso; iapply adt.ownCtxAt_top_cons K $$ HC
        | nil =>
        icases (adt.ownCtxAt_top K _ _ _ _ _).1 $$ HC with ⟨-, Hroot⟩
        wp_auto
        ihave HC := (adt.ownCtxAt_top K t tv.sentinel' xl tv.sentinel' tx.maxEnd).2 $$ [Hroot]
        · iframe; ipureintro; rfl
        wp_join_done
      · have hC : C ≠ .top := fun h => Hif (Hpar.1 h)
        cases C with
        | top => exact absurd rfl hC
        | inL cP CP eP rP =>
          cases ls with
          | nil => iexfalso; iapply adt.ownCtxAt_inL_nil K $$ HC
          | cons f ls' =>
          obtain ⟨ppz, rPp⟩ := f
          icases (adt.ownCtxAt_inL K _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HC with
            ⟨%Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, HrP, HC⟩
          wp_auto
          icases adt.ownNode_childMax K _ _ _ tx $$ Hx with ⟨Hxm, Hxmback⟩
          icases adt.ownNode_childMax K _ _ _ rP $$ HrP with ⟨HrPm, HrPback⟩
          wp_apply (h_updateMax K hK) t tv.sentinel' CP ls' pz ppz xl rPp eP
              (adt.nodeMaxO (some (adt.nodeMax l ze r)) eP rP.maxEnd) tx.maxEnd rP.maxEnd Hpn.1
            $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hxm HrPm] as ⟨HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hxm, HrPm⟩
          · iframe
          ihave Hx := Hxmback $$ Hxm
          ihave HrP := HrPback $$ HrPm
          ihave HC := (adt.ownCtxAt_inL K t tv.sentinel' cP CP eP rP ppz rPp ls' xl pz tx.maxEnd).2
            $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc HrP]
          · iframe; ipureintro; exact Hpn
          wp_join_done
        | inR cP lP eP CP =>
          cases ls with
          | nil => iexfalso; iapply adt.ownCtxAt_inR_nil K $$ HC
          | cons f ls' =>
          obtain ⟨ppz, lPp⟩ := f
          icases (adt.ownCtxAt_inR K _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HC with
            ⟨%Hpn, Hpiv, Hpmx, Hpl, Hpr, Hpp, Hpc, HlP, HC⟩
          ihave %Hne := adt.ownNode_ne K _ _ _ _ _ _ Hzn.1 $$ HlP Hzp
          wp_auto
          rw [_root_.decide_eq_false (Ne.symm Hne)]
          wp_auto
          icases adt.ownNode_childMax K _ _ _ tx $$ Hx with ⟨Hxm, Hxmback⟩
          icases adt.ownNode_childMax K _ _ _ lP $$ HlP with ⟨HlPm, HlPback⟩
          wp_apply (h_updateMax K hK) t tv.sentinel' CP ls' pz ppz lPp xl eP
              (adt.nodeMaxO lP.maxEnd eP (some (adt.nodeMax l ze r))) lP.maxEnd tx.maxEnd Hpn.1
            $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hxm HlPm] as ⟨HC, Hpiv, Hpmx, Hpl, Hpr, Hpp, HlPm, Hxm⟩
          · iframe
          ihave Hx := Hxmback $$ Hxm
          ihave HlP := HlPback $$ HlPm
          ihave HC := (adt.ownCtxAt_inR K t tv.sentinel' cP lP eP CP ppz lPp ls' xl pz tx.maxEnd).2
            $$ [HC Hpiv Hpmx Hpl Hpr Hpp Hpc HlP]
          · iframe; ipureintro; exact Hpn
          wp_join_done
      -- `z`'s colour: the fixup if black
      have hrb' : (C.plug (.node cz l ze r)).redOk ∧ (C.plug (.node cz l ze r)).blackHeight.isSome ∧
          (C.plug (.node cz l ze r)).color = .black := by rw [Hplug]; exact hrb
      obtain ⟨hstB, hstR⟩ := adt.RbCtx.del_start C cz l ze r tx hx hrb'.1 hrb'.2.1 hrb'.2.2
      obtain ⟨hget, hord⟩ := adt.RbCtx.del_inorder_one C cz l ze r tx hx
      ihave Hzc := adt.colorAt_intro tv.sentinel' z cz (DFrac.own 1) Hzn.1 $$ Hzc
      wp_apply h_color z tv.sentinel' cz (DFrac.own 1) $$ [Hzc] as Hzc
      · iframe
      wp_join iprop(∃ (R : Loc) (T' : adt.RbT adt.Entry), t.[intervalTree, go!"root"] ↦ R ∗
          adt.ownNode K tv.sentinel' (DFrac.own 1) tv.sentinel' R T' ∗ adt.ownSentinel tv.sentinel' (DFrac.own 1) ∗
          x_ptr ↦ xl ∗ ivt_ptr ↦ t ∗ t.[intervalTree, go!"sentinel"] ↦ tv.sentinel' ∗
          ⌜adt.RbOk T' ∧ T'.inorder = (C.plug tx).inorder⌝)
        with [HC Hx Hsent x ivt Hs] as ⟨%R, %T', Hroot, HT, Hsent, x, ivt, Hs, %HT'⟩
      · have hcz : cz = .black := adt.colorW_inj Hif
        ihave HC := adt.ownCtxAt_ctx K _ _ _ _ _ _ _ $$ HC
        wp_apply (h_deleteFixup K hK) t tv.sentinel' (DFrac.own 1) C xl pz tx (hstB hcz)
          $$ [Hs HC Hx Hsent] as ⟨Hs, Hsent, %R, %T', Hroot, HT, %HT'⟩
        · iframe
        wp_join_done
        iexists R, T'
        iframe
        ipureintro; exact HT'
      · have hcz : cz = .red := by
          cases cz
          · rfl
          · exact absurd rfl Hif
        ihave HC := adt.ownCtxAt_ctx K _ _ _ _ _ _ _ $$ HC
        icases adt.ownCtx_plug K _ _ _ _ _ _ $$ [HC Hx] with ⟨%R, Hroot, HT⟩
        · iframe
        ihave Hsent := adt.sentAt_ownSentinel _ _ _ $$ Hsent
        iexists R, C.plug tx
        iframe
        ipureintro; exact ⟨hstR hcz, rfl⟩
      iapply HΦ
      iframe Hkb Hke
      have hpost := adt.del_post (GF := GF) K t tv.sentinel' R tv.count' T' L _ ze b e Htn
        (by rw [← hTL, ← Hplug]; exact hget) hz1 (by rw [HT'.2, hord, Hplug, hTL]) HT'.1 hsorted
        hcnt hlen
      unfold adt.ownIvtK at hpost
      iapply hpost
      iframe


end proof

end EtcdGrove
end Perennial
