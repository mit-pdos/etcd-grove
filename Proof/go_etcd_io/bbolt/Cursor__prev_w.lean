/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__prev_w.lean` (U6z, U6aa, `notes/bbolt-proof-plan.md`,
"Writer reads at a fraction"): `prev`'s upward scan as `prev_r`'s (the levels passed at index at
most `0`, `WPrev.below_zero`); at a branch with an index above `0`, one back and `last_w` down
(`WNext.trunc_prefix`), every entry after the new leaf in it (`WPrev.tail_up`), at its last index
(`WPrev.lastInv_new`), then `keyValue_ws`; at the root, the bucket is empty (`WPrev.tail_root`) and
`first_w`'s stack is `Last`'s invariant (`WPrev.lastInv_first`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__prev_w
public import Spec.go_etcd_io.bbolt.Cursor__first_w
public import Spec.go_etcd_io.bbolt.Cursor__last_w
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_ws
public import Proof.go_etcd_io.bbolt.Read.WPrevOwn

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

theorem Cursor.prev_w.wp_proofQ
    (hfirst : Cursor.first_w.specQ (GF := GF) (hG := hG))
    (hlast : Cursor.last_w.specQ (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue_ws.specQ (GF := GF) (hG := hG)) :
    Cursor.prev_w.specQ (GF := GF) (hG := hG) := by
  intro K tx r m q X n bl rt ipg nl c stk els pids hc hinv hN hcnt0
  have hv : viewWF X.v := hc.1.2.2.2.2.2.2.2
  obtain ⟨hp, hlo, ht, elf, helf, hlf⟩ := hinv
  have hlf' : elf.index' = W64 0 ∨ elf.index' = W64 (-1) := by
    rcases hlf with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  have hpl : pids.length = els.length := hp.2.1
  have hleafz : sint.Z elf.index' ≤ 0 := by rcases hlf' with h | h <;> rw [h] <;> decide
  wp_start as ⟨Hw, Hc, Hs, Hcap, #Hown⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have hlen : els.length < 2 ^ 63 := by
    have h1 := Hsl.1; rw [show sint.nat stk.len = (sint.Z stk.len).toNat from rfl] at h1; word
  have hsl0 : sint.Z stk.len = (els.length : Int) := by
    have h1 := Hsl.1; have h2 := Hsl.2
    rw [show sint.nat stk.len = (sint.Z stk.len).toNat from rfl] at h1; omega
  wp_auto
  ihave IH : (∃ (stk1 : GoSlice) (kk : Nat),
      "i" ∷ i_ptr ↦ W64 ((kk : Int) - 1) ∗ "Hw" ∷ wtxWQ K tx r m q X ∗
      "Hcc" ∷ c ↦ Cursor.mk bl stk1 ∗
      "Hs" ∷ stk1 ↦* els.take kk ∗ "Hcap" ∷ ownSliceCap elemRef stk1 (DFrac.own 1) ∗
      "%Hu" ∷ ⌜1 ≤ kk ∧ kk ≤ els.length ∧
        ∀ j x, kk ≤ j → els[j]? = some x → sint.Z x.index' ≤ 0⌝ : IProp GF) $$ [i Hw Hc Hs Hcap]
  · iexists stk, els.length
    simp only [named]
    rw [List.take_length]
    iframe
    isplitl
    · iExactEq i; congr 1; have := hsl0; word
    · ipureintro
      refine ⟨by omega, Nat.le_refl _, fun j x hj hx => ?_⟩
      have := (List.getElem?_eq_some_iff.1 hx).1; omega
  wp_for IH
  obtain ⟨hk1, hkl, hz⟩ := Hu
  ihave %Hsl1 := ownSlice_len _ _ _ $$ Hs
  have hsl1 : sint.Z stk1.len = (kk : Int) := by
    have h1 := Hsl1.1; have h2 := Hsl1.2
    have h3 : (sint.Z stk1.len).toNat = kk := by
      rw [← show sint.nat stk1.len = (sint.Z stk1.len).toNat from rfl, ← h1]; simp; omega
    omega
  have hkz : kk ≤ els.length → sint.Z (W64 ((kk : Int) - 1)) = (kk : Int) - 1 := by
    intro _; word
  wp_if_destruct
  · -- the up-loop's body at element `kk - 1`
    have hkl' : kk - 1 < els.length := by omega
    rw [if_pos ⟨by rw [hkz hkl]; omega, by rw [hkz hkl, hsl1]; omega⟩]
    have hget : (els.take kk)[(sint.Z (W64 ((kk : Int) - 1))).toNat]? = some els[kk - 1] := by
      rw [hkz hkl, show ((kk : Int) - 1).toNat = kk - 1 by omega, List.getElem?_take,
        if_pos (by omega)]
      exact List.getElem?_eq_getElem hkl'
    icases ownSlice_elem_acc (sint.Z (W64 ((kk : Int) - 1))) els[kk - 1] _ _ (els.take kk) (by omega)
      hget $$ Hs with ⟨He, Hsback⟩
    wp_auto
    by_cases hgt : 0 < sint.Z els[kk - 1].index'
    · rw [decide_eq_true (show sint.Z (W64 0) < sint.Z els[kk - 1].index' from hgt)]
      wp_auto
      ihave Hs := Hsback $$ He
      wp_for_post
      -- the level found is a branch
      have hkN : kk < els.length := by
        refine Nat.lt_of_le_of_ne hkl fun h => ?_
        subst h
        have h2 : els[els.length - 1]? = some elf := WGoFirst.getLast_idx els elf helf
        rw [List.getElem?_eq_getElem hkl'] at h2
        rw [Option.some.inj h2] at hgt
        omega
      obtain ⟨e', he'⟩ : ∃ e' : elemRef,
          e' = { els[kk - 1] with index' := els[kk - 1].index' - W64 1 } := ⟨_, rfl⟩
      have hset : (els.take kk).set (sint.Z (W64 ((kk : Int) - 1))).toNat
          { page' := els[kk - 1].page', node' := els[kk - 1].node',
            index' := els[kk - 1].index' - W64 1 } = els.take (kk - 1) ++ [e'] := by
        rw [hkz hkl, show ((kk : Int) - 1).toNat = kk - 1 by omega]
        have := WPrev.take_set_last els (kk - 1) e' hkl'
        rw [Nat.sub_add_cancel hk1, he'] at this
        rw [he']; exact this
      rw [hset]
      have hpk : kk - 1 < pids.length := by omega
      have hEls : els.take (kk - 1) ++ els[kk - 1] :: els.drop kk = els := by
        have := List.take_append_drop (kk - 1) els
        rw [List.drop_eq_getElem_cons hkl', Nat.sub_add_cancel hk1] at this; exact this
      have hPids : pids.take (kk - 1) ++ pids[kk - 1] :: pids.drop kk = pids := by
        have := List.take_append_drop (kk - 1) pids
        rw [List.drop_eq_getElem_cons hpk, Nat.sub_add_cancel hk1] at this; exact this
      have hPE : (pids.take (kk - 1)).length = (els.take (kk - 1)).length := by simp; omega
      have hTne : els.drop kk ≠ [] := by
        intro h; have := List.length_drop (l := els) (i := kk); rw [h] at this; simp at this; omega
      have hpS : sPathR nl X.v bl rt (els.take (kk - 1) ++ els[kk - 1] :: els.drop kk)
          (pids.take (kk - 1) ++ pids[kk - 1] :: pids.drop kk) := by rw [hEls, hPids]; exact hp
      obtain ⟨pg, hpg, hfb, hlt0, -⟩ := (hp.2.2.2 (kk - 1) els[kk - 1] pids[kk - 1]
        (List.getElem?_eq_getElem hkl') (List.getElem?_eq_getElem hpk)).2.2.1 (by omega)
      have hpc : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
      have hidx : e'.index'.toNat + 1 = els[kk - 1].index'.toNat := by
        rw [he']; exact WPrev.idx_pred _ (by omega) hgt
      have htr := WNext.trunc_prefix nl X.v hv bl rt (els.take (kk - 1)) (els.drop kk) els[kk - 1] e'
        (pids.take (kk - 1)) (pids.drop kk) pids[kk - 1] hPE hpS (by rw [he']) (by rw [he'])
        (fun _ pg' hpg' => by rw [hpg] at hpg'; cases hpg'; omega)
      have hne : stk1.len ≠ W64 0 := by
        intro h; rw [h] at hsl1; simp at hsl1; omega
      have hown1 := WPrev.wStkOwn_trunc (GF := GF) r nl X.v rt ipg (els.take (kk - 1)) (els.drop kk)
        els[kk - 1] e' (by rw [he']) (by rw [he'])
      rw [hEls] at hown1
      ihave #Hown1 := hown1 $$ Hown
      try wp_auto
      rw [decide_eq_false hne]
      try wp_auto
      wp_apply hlast K tx r m q X n bl rt ipg nl c stk1 (els.take (kk - 1) ++ [e'])
        (pids.take (kk - 1) ++ [pids[kk - 1]]) hc htr.1 (fun h => absurd (htr.2 h).1 hTne)
        $$ [Hw Hcc Hs Hcap] as ⟨%stk2, %R, %Q, %nl2, Hw, Hcc, Hs, Hcap, #Hown2, %Hpost⟩
      · iframe; iexact Hown1
      obtain ⟨hp2, hlo2, hsuf, htopR, -⟩ := Hpost
      have hlenP : (pids.take (kk - 1) ++ [pids[kk - 1]]).length = kk := by simp; omega
      have hlenE : (els.take (kk - 1) ++ [e']).length = kk := by simp; omega
      have hQR : Q.length = R.length := by
        have := hp2.2.1; simp only [List.length_append] at this hlenP hlenE; omega
      have hRne : R ≠ [] := by
        intro hR
        subst hR
        have hQ : Q = [] := List.eq_nil_of_length_eq_zero (by simpa using hQR)
        subst hQ
        simp only [List.append_nil] at hp2
        have hlt1 : (els.take (kk - 1)).length = kk - 1 := by simp; omega
        have hlt2 : (pids.take (kk - 1)).length = kk - 1 := by simp; omega
        have := (hp2.2.2.2 (kk - 1) e' pids[kk - 1]
          (by rw [List.getElem?_append_right (by omega), hlt1, Nat.sub_self]; rfl)
          (by rw [List.getElem?_append_right (by omega), hlt2, Nat.sub_self]; rfl)).2.2.2
          (by rw [List.length_append, hlt1]; simp)
        exact WNext.leaf_not_branch X.v hv _ pg hpg hfb this
      -- every entry after the new leaf is in it
      have hTs := List.dropLast_concat_getLast hTne
      have htail : sTailEmpty X.v (wEs X n) (pids.take (kk - 1) ++ pids[kk - 1] :: Q)
          (els.take (kk - 1) ++ e' :: R) := by
        refine WPrev.tail_up X.v (wEs X n) (els.take (kk - 1)) (pids.take (kk - 1)) pids[kk - 1]
          els[kk - 1] e' ((els.drop kk).getLast hTne) (els.drop kk).dropLast R (pids.drop kk) Q
          hPE (by simp; omega) hQR hRne hidx
          (by rw [Prev.pidKeys_length _ _ pg hpg]; exact hlt0) ?_ ?_ ?_ ?_
        · intro x hx
          obtain ⟨i, hi, hxi⟩ := WPrev.mem_dropLast_idx _ x hx
          rw [List.getElem?_drop] at hxi
          exact WPrev.below_zero nl X.v bl rt els pids hp kk hz (kk + i) x (by omega)
            (by simp at hi; omega) hxi
        · intro j pid x hq hx hj
          exact hsuf (kk + j) pid x
            (by rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]; exact hq)
            (by rw [List.getElem?_append_right (by omega), hlenE, Nat.add_sub_cancel_left]; exact hx)
            (by omega) (by simp only [List.length_append] at hlenE ⊢; omega)
        · rw [hTs, hEls, hPids]; exact ht
        · rw [hTs, hEls, hPids]; exact hcnt0
      have htail' : sTailEmpty X.v (wEs X n) ((pids.take (kk - 1) ++ [pids[kk - 1]]) ++ Q)
          ((els.take (kk - 1) ++ [e']) ++ R) := by
        simp only [List.append_assoc, List.singleton_append]; exact htail
      icases WPrev.leafCnt_lt K tx r m q X n bl rt ipg nl2 _ _ hc hp2 hlo2 $$ [Hw] with ⟨Hw, %Hcnt⟩
      · iframe; iframe #
      have hinv2 := WPrev.lastInv_new nl2 X.v hv (wEs X n) bl rt ipg _ _ hp2 hlo2 htail'
        (htopR hRne) Hcnt
      have hix : leafIdx ((els.take (kk - 1) ++ [e']) ++ R) ≤
            leafCnt X.v (wEs X n) ((pids.take (kk - 1) ++ [pids[kk - 1]]) ++ Q)
              ((els.take (kk - 1) ++ [e']) ++ R) ∨
          wEndAt X.v (wEs X n) ((pids.take (kk - 1) ++ [pids[kk - 1]]) ++ Q)
              ((els.take (kk - 1) ++ [e']) ++ R) ∨
          (leafCnt X.v (wEs X n) ((pids.take (kk - 1) ++ [pids[kk - 1]]) ++ Q)
              ((els.take (kk - 1) ++ [e']) ++ R) = 0 ∧
            ∃ e, ((els.take (kk - 1) ++ [e']) ++ R).getLast? = some e ∧ e.index' = W64 (-1)) := by
        obtain ⟨e3, he3, h3⟩ := hinv2.2.2.2
        rw [WNext.leafIdx_of _ e3 he3]
        rcases h3 with ⟨h0, h | h⟩ | ⟨-, h⟩
        · left; rw [h, h0]; exact Nat.le_refl _
        · right; right; exact ⟨h0, e3, he3, h⟩
        · left; omega
      try wp_auto
      wp_apply hkv K tx r m q X n bl rt ipg nl2 c stk2 _ _ hc hp2 hlo2 hix
        $$ [Hw Hcc Hs] as %k %vl %fl ⟨Hw, Hcc, Hs, -⟩
      · iframe; iframe #
      try wp_auto
      iapply HΦ
      iexists stk2, _, _, nl2, ipg
      iframe
      isplitl []
      · iexact Hown2
      · ipureintro
        exact hinv2
    · rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z els[kk - 1].index' from hgt)]
      wp_auto
      ihave Hs := Hsback $$ He
      rw [show (els.take kk).set (sint.Z (W64 ((kk : Int) - 1))).toNat els[kk - 1] = els.take kk by
        rw [hkz hkl, show ((kk : Int) - 1).toNat = kk - 1 by omega]
        have h : (els.take kk)[kk - 1]'(by simp; omega) = els[kk - 1] := by simp
        rw [← h, List.set_getElem_self]]
      by_cases hk1' : kk = 1
      · -- at the root: `first`, nil
        subst hk1'
        have hl1 : stk1.len = W64 1 := by
          apply BitVec.eq_of_toInt_eq; rw [show (W64 1).toInt = 1 from rfl]; exact hsl1
        rw [decide_eq_true hl1]
        wp_auto
        wp_apply hfirst K tx r m q X n bl rt c stk1 (els.take 1) hc
          $$ [Hw Hcc Hs Hcap] as %k0 %vl0 %fl0
            ⟨%stk2, %els2, %nl2, %ipg2, Hw, Hcc, Hs, Hcap, #Hown2, %Hcur, -⟩
        · iframe
        have hne : els ≠ [] := hp.1
        have hall : ∀ j x, 0 ≤ j → els[j]? = some x → sint.Z x.index' ≤ 0 := by
          intro j x _ hx
          rcases Nat.eq_zero_or_pos j with h | h
          · subst h
            rw [List.getElem?_eq_getElem (by omega)] at hx
            rw [← Option.some.inj hx]; exact Int.le_of_not_gt hgt
          · exact hz j x h hx
        have hes : wEs X n = [] := by
          have hsp := List.dropLast_concat_getLast hne
          refine WPrev.tail_root X.v (wEs X n) els.dropLast (els.getLast hne) pids
            (by simp; omega) ?_ (by rw [hsp]; exact ht) (by rw [hsp]; exact hcnt0)
          intro x hx
          obtain ⟨j, hj, hxj⟩ := WPrev.mem_dropLast_idx _ x hx
          exact WPrev.below_zero nl X.v bl rt els pids hp 0 hall j x (Nat.zero_le _) hj hxj
        rw [hes] at Hcur
        obtain ⟨pids2, hinv2⟩ := WPrev.lastInv_first nl2 X.v bl rt ipg2 els2 Hcur
        try wp_auto
        wp_for_post
        iapply HΦ
        iexists stk2, els2, pids2, nl2, ipg2
        iframe
        isplitl []
        · iexact Hown2
        · ipureintro
          rw [hes]; exact hinv2
      · -- truncate the stack
        have hl1 : stk1.len ≠ W64 1 := by
          intro h; rw [h] at hsl1; simp at hsl1; omega
        rw [decide_eq_false hl1]
        wp_auto
        ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
        rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 ((kk : Int) - 1)) ∧
          sint.Z (W64 ((kk : Int) - 1)) ≤ sint.Z stk1.cap by rw [hkz hkl]; simp; omega)]
        icases ownSlice_slice_with_cap (V := elemRef) (W64 0) (W64 ((kk : Int) - 1)) stk1 _
          ⟨by decide, by rw [hkz hkl]; simp; omega, by rw [hkz hkl, hsl1]; omega⟩ $$ [Hs Hcap]
          with ⟨-, Hs, Hcap⟩
        · iframe
        have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 ((kk : Int) - 1))) (els.take kk) =
            els.take (kk - 1) := by
          have h1 : sint.nat (W64 ((kk : Int) - 1)) = kk - 1 := by
            unfold sint.nat; rw [show (W64 ((kk : Int) - 1)).toInt = (kk : Int) - 1 from hkz hkl]
            omega
          rw [h1, show sint.nat (W64 0) = 0 from rfl]
          unfold subslice; rw [List.drop_zero, List.take_take]; congr 1; omega
        rw [hsub]
        wp_auto
        wp_for_post
        iframe
        iexists _, kk - 1
        simp only [named]
        iframe
        isplitl
        · iExactEq i; congr 1; rw [show ((kk - 1 : Nat) : Int) = (kk : Int) - 1 by omega]; word
        · ipureintro
          refine ⟨by omega, by omega, fun j x hj hx => ?_⟩
          rcases Nat.lt_or_ge j kk with h | h
          · have hj' : j = kk - 1 := by omega
            subst hj'
            rw [List.getElem?_eq_getElem hkl'] at hx
            rw [← Option.some.inj hx]; exact Int.le_of_not_gt hgt
          · exact hz j x h hx
  · -- the up-loop never runs out (`kk ≥ 1`)
    exfalso
    rw [hkz hkl] at Hif; simp at Hif; omega

end proof

end bbolt
end EtcdGrove
end Perennial
