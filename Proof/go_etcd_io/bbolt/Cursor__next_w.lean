/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__next_w.lean` (U6z/U6aa, `notes/bbolt-proof-plan.md`,
"Writer reads at a fraction"): the outer loop's invariant is a writer stack (`wStk`) with the original
stack's target (`wNextTo`), either the original stack or an empty leaf at index `0` (restarted); the
upward scan's is `WNext.scanOK` (each level's `count()`: `WNext.wp_lvl_count`); the level found,
moved one further and truncated, is `goToFirstElementOnTheStack_w`'s prefix (`WNext.trunc_prefix`),
the descent's stack at the target (`WNext.found`, by `stackPos_nextR`); no level found, the stack is
at the end (`WNext.scan_none`). `next_we`: from `wEndAt` no level moves.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__next_w
public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack_w
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_ws
public import Proof.go_etcd_io.bbolt.Read.WNextCnt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
theorem idx_sint (x : w64) (c : Nat) (hc : c < 2 ^ 63) (h : x.toNat ≤ c) :
    sint.Z x = (x.toNat : Int) := by
  have : (x.toNat : Int) = uint.Z x := rfl
  rw [this]
  word

omit [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
/-- At the end (`wEndAt`) no level can move. -/
theorem we_noMove (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (es : List BoltEnt) (pids : List Nat) (els : List elemRef) (hp : sPathR nl v b rt els pids)
    (hend : wEndAt v es pids els) (j : Nat) (hj : j < els.length) (x : elemRef)
    (hx : els[j]? = some x) (h63 : WNext.cntAt v es pids els j < 2 ^ 63) :
    ¬ sint.Z x.index' < (WNext.cntAt v es pids els j : Int) - 1 := by
  by_cases hj1 : j + 1 < els.length
  · obtain ⟨pid, pg, hpid, hpg, -, hlt⟩ := WNext.sPathR_br nl v b rt pids els hp j hj1 x hx
    rw [WNext.cntAt_br v es pids els j pid pg hj1 hpid hpg] at h63 ⊢
    have hl := hend.1 j pid x hpid hx hj1
    rw [Prev.pidKeys_length v pid pg hpg] at hl
    rw [idx_sint x.index' _ h63 (by omega)]
    omega
  · rw [WNext.cntAt_leaf v es pids els j (by omega)] at h63 ⊢
    obtain ⟨-, e, he, h⟩ := hend
    have hl : els.getLast? = some x := by
      rw [List.getLast?_eq_getElem?, show els.length - 1 = j by omega]; exact hx
    rw [hl] at he; cases he
    rcases h with h | ⟨h0, h⟩
    · rw [h]
      have : sint.Z (W64 (leafCnt v es pids els : Int)) = (leafCnt v es pids els : Int) := by word
      omega
    · rw [h, h0]; decide

theorem Cursor.next_we.wp_proofQ
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG)) :
    Cursor.next_we.specQ (GF := GF) (hG := hG) := by
  intro K tx r m q X n bl rt ipg nl c stk els pids hc hst
  wp_start as ⟨Hw, Hc, Hs, #Hown⟩
  icases wtxWQ_pkgInit K tx r m q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  ihave IH : ("Hw" ∷ wtxWQ K tx r m q X ∗ "Hcc" ∷ c ↦ Cursor.mk bl stk ∗
      "Hs" ∷ stk ↦* els : IProp GF) $$ [Hw Hc Hs]
  · simp only [named]; iframe
  wp_for IH
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave IH2 : (∃ (kk : Nat), "i" ∷ i_ptr ↦ W64 ((kk : Int) - 1) ∗ "Hs" ∷ stk ↦* els ∗
      "Hw" ∷ wtxWQ K tx r m q X ∗ "%Hu" ∷ ⌜kk ≤ els.length⌝ : IProp GF) $$ [i Hs Hw]
  · iexists els.length
    simp only [named]
    iframe
    isplitl
    · iExactEq i; congr 1; word
    · ipureintro; exact Nat.le_refl _
  have hlen : els.length < 2 ^ 63 := by
    have h1 := Hsl.1; rw [show sint.nat stk.len = (sint.Z stk.len).toNat from rfl] at h1; word
  wp_for IH2
  wp_if_destruct
  · have hkz : sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by word
    have hk1 : 1 ≤ kk := by rw [hkz] at Hif; simp at Hif; omega
    have hkl : kk - 1 < els.length := by omega
    have hsl' : sint.Z stk.len = (els.length : Int) := by
      have h1 := Hsl.1; have h2 := Hsl.2
      rw [show sint.nat stk.len = (sint.Z stk.len).toNat from rfl] at h1; omega
    rw [if_pos ⟨by rw [hkz]; omega, by rw [hkz, hsl']; omega⟩]
    have hget : els[(sint.Z (W64 ((kk : Int) - 1))).toNat]? = some els[kk - 1] := by
      rw [hkz, show ((kk : Int) - 1).toNat = kk - 1 by omega]; simp
    rcases hst with h0 | ⟨hp, hlo, hend⟩
    · subst h0; simp at hkl
    icases ownSlice_elem_acc (sint.Z (W64 ((kk : Int) - 1))) els[kk - 1] _ _ els (by omega)
      hget $$ Hs with ⟨He, Hsback⟩
    wp_auto
    wp_apply WNext.wp_lvl_count hCnt K tx r m q X n bl rt ipg nl els pids hc hp hlo (kk - 1) hkl
      els[kk - 1] (by simp) _ $$ [Hw He] as ⟨Hw, He, %H63⟩
    · iframe; iframe #
    have hcm : sint.Z (W64 (WNext.cntAt X.v (wEs X n) pids els (kk - 1) : Int) - W64 1) =
        (WNext.cntAt X.v (wEs X n) pids els (kk - 1) : Int) - 1 := by word
    try wp_auto
    rw [hcm]
    rw [decide_eq_false (we_noMove nl X.v bl rt (wEs X n) pids els hp hend (kk - 1) hkl _ (by simp) H63)]
    wp_auto
    ihave Hs := Hsback $$ He
    rw [show els.set (sint.Z (W64 ((kk : Int) - 1))).toNat els[kk - 1] = els by
      rw [hkz, show ((kk : Int) - 1).toNat = kk - 1 by omega]; simp]
    wp_for_post
    iframe
    iexists kk - 1
    simp only [named]
    iframe
    isplitl
    · iExactEq i; congr 1
      rw [show ((kk - 1 : Nat) : Int) = (kk : Int) - 1 by omega]; word
    · ipureintro; omega
  · have hk0 : kk = 0 := by
      rcases Nat.eq_zero_or_pos kk with h | h
      · exact h
      · have hkz : sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by word
        rw [hkz] at Hif; simp at Hif; omega
    subst hk0
    rw [decide_eq_true (by rfl)]
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
    iexact Hown

theorem wtxWQ_stkAgree (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX)
    (nl : Loc → Option (Loc × Nat)) (v : View) (rt : Nat) (ipg : List w8) (els : List elemRef) :
    wtxWQ (GF := GF) K tx r m q X ∗ wStkOwn r nl v rt ipg els ⊢
      wtxWQ K tx r m q X ∗ ⌜∀ e ∈ els, e.node' ≠ null → nl e.node' = X.nloc !! e.node'⌝ := by
  unfold wStkOwn
  iintro ⟨Hw, Hn, -⟩
  iapply WBridge.wtxWQ_nodeLoc_agree K tx r m q X nl els
  iframe

theorem Cursor.next_w.wp_proofQ
    (hg : Cursor.goToFirstElementOnTheStack_w.specQ (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_ws.specQ (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG)) :
    Cursor.next_w.specQ (GF := GF) (hG := hG) := by
  intro K tx r m q X n bl rt ipg nl c stk els pids hc hst
  have hok := hc.1
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  obtain ⟨B, hB⟩ := PubW.bktLoc_rec X hok n bl hc.2.1
  wp_start as ⟨Hw, Hc, Hs, Hcap, #Hown⟩
  icases wtxWQ_pkgInit K tx r m q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  ihave IH : (∃ (stk1 : GoSlice) (els1 : List elemRef) (pids1 : List Nat)
      (nl1 : Loc → Option (Loc × Nat)),
      "Hw" ∷ wtxWQ K tx r m q X ∗ "Hcc" ∷ c ↦ Cursor.mk bl stk1 ∗ "Hs" ∷ stk1 ↦* els1 ∗
      "Hcap" ∷ ownSliceCap elemRef stk1 (DFrac.own 1) ∗ "Hown" ∷ wStkOwn r nl1 X.v rt ipg els1 ∗
      "%Hinv" ∷ ⌜wStk nl1 X.v (wEs X n) bl rt ipg els1 pids1 ∧
        wNextTo X.v (wEs X n) pids1 els1 = wNextTo X.v (wEs X n) pids els ∧
        ((els1 = els ∧ pids1 = pids ∧ nl1 = nl) ∨
         (leafIdx els1 = 0 ∧ leafCnt X.v (wEs X n) pids1 els1 = 0))⌝ : IProp GF) $$ [Hw Hc Hs Hcap]
  · iexists stk, els, pids, nl
    simp only [named]
    iframe
    isplitr
    · iexact Hown
    · ipureintro; refine ⟨hst, ?_⟩; simp
  wp_for IH
  icases Hown with #Hown1
  obtain ⟨hw1, htgt, hcase⟩ := Hinv
  have hp1 := hw1.1
  have hlo1 := hw1.2.1
  icases wtxWQ_stkAgree K tx r m q X nl1 X.v rt ipg els1 $$ [Hw] with ⟨Hw, %Hag1⟩
  · iframe; iframe #
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have hlen : els1.length < 2 ^ 63 := by
    have h1 := Hsl.1; rw [show sint.nat stk1.len = (sint.Z stk1.len).toNat from rfl] at h1; word
  have hsl' : sint.Z stk1.len = (els1.length : Int) := by
    have h1 := Hsl.1; have h2 := Hsl.2
    rw [show sint.nat stk1.len = (sint.Z stk1.len).toNat from rfl] at h1; omega
  ihave IH2 : (∃ (kk : Nat), "i" ∷ i_ptr ↦ W64 ((kk : Int) - 1) ∗ "Hs" ∷ stk1 ↦* els1 ∗
      "Hw" ∷ wtxWQ K tx r m q X ∗
      "%Hu" ∷ ⌜kk ≤ els1.length ∧ WNext.scanOK X.v (wEs X n) pids1 els1 kk⌝ : IProp GF) $$ [i Hs Hw]
  · iexists els1.length
    simp only [named]
    iframe
    isplitl
    · iExactEq i; congr 1; word
    · ipureintro; exact ⟨Nat.le_refl _, WNext.scanOK_start _ _ _ _⟩
  wp_for IH2
  wp_if_destruct
  · have hkz : sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by have := Hu.1; word
    have hk1 : 1 ≤ kk := by rw [hkz] at Hif; simp at Hif; omega
    have hkl : kk - 1 < els1.length := by have := Hu.1; omega
    rw [if_pos ⟨by rw [hkz]; omega, by rw [hkz, hsl']; have := Hu.1; omega⟩]
    have hget : els1[(sint.Z (W64 ((kk : Int) - 1))).toNat]? = some els1[kk - 1] := by
      rw [hkz, show ((kk : Int) - 1).toNat = kk - 1 by omega]; simp
    icases ownSlice_elem_acc (sint.Z (W64 ((kk : Int) - 1))) els1[kk - 1] _ _ els1 (by omega)
      hget $$ Hs with ⟨He, Hsback⟩
    wp_auto
    wp_apply WNext.wp_lvl_count hCnt K tx r m q X n bl rt ipg nl1 els1 pids1 hc hp1 hlo1 (kk - 1)
      hkl els1[kk - 1] (by simp) _ $$ [Hw He] as ⟨Hw, He, %H63⟩
    · iframe; iframe #
    have hcm : sint.Z (W64 (WNext.cntAt X.v (wEs X n) pids1 els1 (kk - 1) : Int) - W64 1) =
        (WNext.cntAt X.v (wEs X n) pids1 els1 (kk - 1) : Int) - 1 := by word
    try wp_auto
    rw [hcm]
    have hix := WNext.cntAt_idx nl1 X.v (wEs X n) bl rt ipg els1 pids1 hw1 (kk - 1) hkl els1[kk - 1] (List.getElem?_eq_getElem hkl)
    have hsz := idx_sint els1[kk - 1].index' _ H63 hix
    by_cases hlt : sint.Z els1[kk - 1].index' <
        (WNext.cntAt X.v (wEs X n) pids1 els1 (kk - 1) : Int) - 1
    · rw [decide_eq_true hlt]
      wp_auto
      ihave Hs := Hsback $$ He
      ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
      wp_for_post
      have hne : W64 ((kk : Int) - 1) ≠ W64 (-1) := by
        intro h; have := congrArg sint.Z h; rw [hkz] at this; simp at this; omega
      rw [decide_eq_false hne]
      wp_auto
      have hkw : W64 ((kk : Int) - 1) + W64 1 = W64 (kk : Int) := by word
      have hkk : sint.Z (W64 (kk : Int)) = (kk : Int) := by have := Hu.1; word
      rw [hkw]
      rw [if_pos ⟨by decide, by rw [hkk]; simp, by rw [hkk]; word⟩]
      icases ownSlice_slice_with_cap (V := elemRef) (W64 0) (W64 (kk : Int)) stk1 _
        ⟨by decide, by rw [hkk]; simp, by rw [hkk, hsl']; have := Hu.1; omega⟩ $$ [Hs Hcap]
        with ⟨-, Hs, Hcap⟩
      · iframe
      obtain ⟨E, x0, T, hE, hEl, hx0⟩ := Prev.split_at els1 (kk - 1) hkl
      obtain ⟨P, p, U, hP, hPl, hp0⟩ := Prev.split_at pids1 (kk - 1) (by rw [hp1.2.1]; exact hkl)
      have hx0' : els1[kk - 1] = x0 := by
        rw [List.getElem?_eq_getElem hkl] at hx0; exact Option.some.inj hx0
      obtain ⟨x', hx'⟩ : ∃ x' : elemRef, x' = elemRef.mk x0.page' x0.node' (x0.index' + W64 1) :=
        ⟨_, rfl⟩
      have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 (kk : Int)))
          (els1.set (sint.Z (W64 ((kk : Int) - 1))).toNat
            { page' := els1[kk - 1].page', node' := els1[kk - 1].node',
              index' := els1[kk - 1].index' + W64 1 }) = E ++ [x'] := by
        rw [hkz, show ((kk : Int) - 1).toNat = kk - 1 by omega,
          show sint.nat (W64 (kk : Int)) = kk by
            unfold sint.nat; rw [show (W64 (kk : Int)).toInt = kk from hkk]; simp,
          show sint.nat (W64 0) = 0 from rfl, hx0', ← hx']
        unfold subslice
        rw [List.drop_zero]
        subst hE
        rw [show kk - 1 = E.length by omega, show kk = E.length + 1 by omega]
        simp only [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]
        rw [List.take_length_add_append]
        simp
      rw [hsub]
      wp_auto
      have hPE : P.length = E.length := by omega
      have hkE : kk = E.length + 1 := by omega
      subst hE hP
      rw [hx0'] at hsz hlt hix
      have hcntlt : x0.index'.toNat + 1 <
          WNext.cntAt X.v (wEs X n) (P ++ p :: U) (E ++ x0 :: T) (kk - 1) := by omega
      have hidx' : x'.index'.toNat = x0.index'.toNat + 1 := by
        subst hx'
        show (x0.index' + W64 1).toNat = _
        have h1 : x0.index'.toNat + 1 < 2 ^ 64 := by omega
        rw [BitVec.toNat_add]
        simp only [W64, BitVec.toNat_ofInt]
        simp
        omega
      obtain ⟨hpre, hpath⟩ := WNext.trunc_prefix nl1 X.v hv bl rt E T x0 x' P U p hPE hp1
        (by rw [hx']) (by rw [hx']) (fun hT pg hpg => by
          rw [hidx', ← WNext.cntAt_br X.v (wEs X n) (P ++ p :: U) (E ++ x0 :: T) (kk - 1) p pg
            (by cases T with | nil => exact absurd rfl hT | cons _ _ => simp only [List.length_append, List.length_cons]; omega) hp0 hpg]
          exact hcntlt)
      have hleafok : sPathR nl1 X.v bl rt (E ++ [x']) (P ++ [p]) →
          sLeafOK X.v ipg (wEs X n) (P ++ [p]) (E ++ [x']) := fun h => by
        obtain ⟨rfl, rfl⟩ := hpath h
        exact WNext.sLeafOK_snoc X.v ipg (wEs X n) E (P ++ [p]) x0 x' (by simp; omega)
          (by rw [hx']) hlo1
      ihave #Hown' := WNext.wStkOwn_trunc r nl1 X.v rt ipg E T x0 x' (by rw [hx']) (by rw [hx'])
        $$ Hown1
      wp_apply hg K tx r m q X n bl rt ipg nl1 c _ (E ++ [x']) (P ++ [p]) hc hpre hleafok
        $$ [Hw Hcc Hs Hcap] as ⟨%stk2, %R, %Q, %nl2, Hw, Hcc, Hs, Hcap, #Hown2, %Hres⟩
      · iframe; iframe #
      obtain ⟨hp2, hlo2, hR⟩ := Hres
      icases wtxWQ_stkAgree K tx r m q X nl2 X.v rt ipg (E ++ [x'] ++ R) $$ [Hw] with ⟨Hw, %Hag2⟩
      · iframe; iframe #
      have hp1X := WGoFirst.sPathR_congr nl1 (WGoFirst.nlX X) X.v bl rt _ _ Hag1 hp1
      have hp2X := WGoFirst.sPathR_congr nl2 (WGoFirst.nlX X) X.v bl rt _ _ Hag2 hp2
      obtain ⟨hpos, hon⟩ := WNext.found X n bl rt B hc hB (wEs X n) (WGoFirst.nlX X) E T x0 x'
        P U p hPE hp1X hw1.2.2 (by rw [← hkE]; exact Hu.2) hidx'
        (fun hT => by
          subst hT
          rw [← WNext.cntAt_leaf X.v (wEs X n) _ _ (kk - 1) (by simp; omega)]
          exact hcntlt) R Q hR hp2X
      ihave %Hsl2 := ownSlice_len _ _ _ $$ Hs
      have hl2 : 0 < (E ++ [x'] ++ R).length := by simp; omega
      have hidx2 : sint.Z (stk2.len - W64 1) = (((E ++ [x'] ++ R).length - 1 : Nat) : Int) := by
        have h1 := Hsl2.1; have h2 := Hsl2.2
        rw [show sint.nat stk2.len = (sint.Z stk2.len).toNat from rfl] at h1
        have : (((E ++ [x'] ++ R).length - 1 : Nat) : Int) = ((E ++ [x'] ++ R).length : Int) - 1 := by
          omega
        rw [this]; word
      have hb2 : 0 ≤ sint.Z (stk2.len - W64 1) ∧ sint.Z (stk2.len - W64 1) < sint.Z stk2.len := by
        rw [hidx2]
        have h1 := Hsl2.1
        have h2 := Hsl2.2
        rw [show sint.nat stk2.len = (sint.Z stk2.len).toNat from rfl] at h1
        omega
      rw [if_pos hb2]
      obtain ⟨y, hy⟩ := WNext.getLast_some (E ++ [x'] ++ R) hp2.1
      have hyj := WGoFirst.getLast_idx _ y hy
      have hgl : (E ++ [x'] ++ R)[(sint.Z (stk2.len - W64 1)).toNat]? = some y := by
        rw [hidx2, Int.toNat_natCast]; exact hyj
      icases ownSlice_elem_acc (sint.Z (stk2.len - W64 1)) y _ _ (E ++ [x'] ++ R) (by omega) hgl
        $$ Hs with ⟨He2, Hsback2⟩
      wp_auto
      wp_apply WNext.wp_lvl_count hCnt K tx r m q X n bl rt ipg nl2 (E ++ [x'] ++ R)
        (P ++ [p] ++ Q) hc hp2 hlo2 _ (by omega) y hyj _ $$ [Hw He2] as ⟨Hw, He2, %H63'⟩
      · iframe; iframe #
      rw [WNext.cntAt_leaf X.v (wEs X n) _ _ _ (by omega)] at H63' ⊢
      ihave Hs := Hsback2 $$ He2
      rw [list_set_lookup_self _ _ _ hgl]
      by_cases hc0 : leafCnt X.v (wEs X n) (P ++ [p] ++ Q) (E ++ [x'] ++ R) = 0
      · rw [show W64 (leafCnt X.v (wEs X n) (P ++ [p] ++ Q) (E ++ [x'] ++ R) : Int) = W64 0 by
          rw [hc0]; rfl]
        wp_auto
        wp_for_post
        iframe
        iexists stk2, E ++ [x'] ++ R, P ++ [p] ++ Q, nl2
        simp only [named]
        iframe
        isplitr
        · iexact Hown2
        ipureintro
        have hli0 : leafIdx (E ++ [x'] ++ R) = 0 := by
          rcases hon with h | ⟨h, -⟩
          · omega
          · exact h
        refine ⟨⟨hp2, hlo2, by omega⟩, ?_, Or.inr ⟨hli0, hc0⟩⟩
        rw [← htgt, ← hpos]; unfold wNextTo; rw [if_neg (by omega)]
      · rw [decide_eq_false (show W64 (leafCnt X.v (wEs X n) (P ++ [p] ++ Q) (E ++ [x'] ++ R) : Int)
            ≠ W64 0 by
          intro h; apply hc0; have := congrArg BitVec.toNat h
          rw [WBridge.W64_toNat_lt _ (by omega)] at this; simpa using this)]
        wp_auto
        have hli : leafIdx (E ++ [x'] ++ R) < leafCnt X.v (wEs X n) (P ++ [p] ++ Q) (E ++ [x'] ++ R) := by
          rcases hon with h | ⟨-, h⟩
          · exact h
          · exact absurd h hc0
        wp_apply hkv K tx r m q X n bl rt ipg nl2 c stk2 _ _ hc hp2 hlo2 (Or.inl (by omega))
          $$ [Hw Hcc Hs] as %k %vl %fl ⟨Hw, Hcc, Hs, Hkv⟩
        · iframe; iframe #
        have hpos' : stackPos X.v (wEs X n) (P ++ [p] ++ Q) (E ++ [x'] ++ R) =
            wNextTo X.v (wEs X n) pids els := by rw [hpos, htgt]
        rw [if_pos hli, hpos']
        try wp_auto
        wp_for_post
        iapply HΦ
        iexists stk2, E ++ [x'] ++ R, nl2
        iframe
        isplitr
        · iexact Hown2
        ipureintro
        refine ⟨P ++ [p] ++ Q, hp2, hlo2, Or.inl ⟨?_, hli, hpos'⟩⟩
        rw [← hpos']; exact stackPos_lt _ _ _ _ hli
    · rw [decide_eq_false hlt]
      wp_auto
      ihave Hs := Hsback $$ He
      rw [show els1.set (sint.Z (W64 ((kk : Int) - 1))).toNat els1[kk - 1] = els1 by
        rw [hkz, show ((kk : Int) - 1).toNat = kk - 1 by omega]; simp]
      wp_for_post
      iframe
      iexists kk - 1
      simp only [named]
      iframe
      isplitl
      · iExactEq i; congr 1
        rw [show ((kk - 1 : Nat) : Int) = (kk : Int) - 1 by omega]; word
      · ipureintro
        refine ⟨by omega, WNext.scanOK_step nl1 X.v bl rt (wEs X n) pids1 els1 hp1 (kk - 1) hkl
          (by rw [Nat.sub_add_cancel hk1]; exact Hu.2) els1[kk - 1] (List.getElem?_eq_getElem hkl)
          (by omega)⟩
  · have hk0 : kk = 0 := by
      rcases Nat.eq_zero_or_pos kk with h | h
      · exact h
      · have hkz : sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by have := Hu.1; word
        rw [hkz] at Hif; simp at Hif; omega
    subst hk0
    rw [decide_eq_true (by rfl)]
    wp_auto
    wp_for_post
    iapply HΦ
    iexists stk1, els1, nl1
    have hne : els1 ≠ [] := hp1.1
    obtain ⟨hge, hend⟩ := WNext.scan_none X.v (wEs X n) pids1 els1 hp1.2.1 hne Hu.2 hw1.2.2
    rw [htgt] at hge
    iframe
    isplitr
    · iexact Hown1
    isplitr
    · ipureintro
      refine ⟨pids1, hp1, hlo1, Or.inr ⟨hge, ?_⟩⟩
      by_cases hli : leafIdx els1 < leafCnt X.v (wEs X n) pids1 els1
      · rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨h0, h0'⟩
        · exact Or.inl ⟨rfl, rfl, hli⟩
        · omega
      · exact Or.inr (hend hli)
    · unfold wEntKV
      rw [List.getElem?_eq_none hge]
      ipureintro; exact ⟨rfl, rfl, rfl⟩

end proof

end bbolt
end EtcdGrove
end Perennial
