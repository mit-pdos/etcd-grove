/- Lean-first (no Rocq counterpart). The proof of `checkRangeAt` (mvccrand's `checkRange`, with the
compacted case): the outcome's arms (the context's error excluded by `res ≠ null`); the future and
the compacted arms' checks from their results (`ErrFutureRev`, `ErrCompacted`: `errVars.law`);
otherwise the match loop over the run's keys gives `matchKeys` (`Model.lean`), which is the index's
answers (`answers_keys_eq_match`), so the count and the key-values are the contract's. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkKV

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `checkRange`'s `taken`: the limit when positive and below the count `n`, else `n`. -/
def takenOf (lim n : w64) : w64 := if 0 < sint.Z lim ∧ sint.Z lim < sint.Z n then lim else n

/-- `checkRange`'s `total`: `taken` when the limit is positive, the total not asked for and the
range not a single key, else `n`. -/
def totalOfT (lim n : w64) (wt endNil : Bool) : w64 :=
  if 0 < sint.Z lim ∧ wt = false ∧ endNil = false then takenOf lim n else n

theorem takeLimit_length_takenOf {α : Type} (A : List α) (lim n : w64) (hn : A.length = sint.nat n)
    (h0 : 0 ≤ sint.Z n) :
    (takeLimit (limitOf lim) A).length = sint.nat (takenOf lim n) := by
  have hn' : (A.length : Int) = sint.Z n := by
    have : sint.nat n = (sint.Z n).toNat := rfl
    rw [hn, this]; omega
  unfold takeLimit limitOf takenOf
  by_cases h1 : 0 < sint.Z lim
  · simp only [h1, ↓reduceIte, List.length_take]
    by_cases h2 : sint.Z lim < sint.Z n
    · simp only [h2, and_self, ↓reduceIte]
      have : sint.nat lim = (sint.Z lim).toNat := rfl
      rw [this]; omega
    · simp only [h2, and_false, ↓reduceIte]
      have : sint.nat n = (sint.Z n).toNat := rfl
      rw [this]; omega
  · simp only [h1, ↓reduceIte, false_and]; exact hn

theorem totalOf_eq (lim n : w64) (wt endNil : Bool) (N : Nat) (hn : N = sint.nat n)
    (h0 : 0 ≤ sint.Z n) (hend : endNil = true → N ≤ 1) :
    W64 (totalOf (limitOf lim) wt N : Int) = totalOfT lim n wt endNil := by
  have hn' : (N : Int) = sint.Z n := by
    have : sint.nat n = (sint.Z n).toNat := rfl
    rw [hn, this]; omega
  unfold totalOf limitOf totalOfT takenOf
  by_cases h1 : 0 < sint.Z lim
  · simp only [h1, ↓reduceIte, true_and]
    cases wt
    · cases endNil
      · simp only [and_self, ↓reduceIte]
        by_cases h2 : sint.Z lim < sint.Z n
        · simp only [h2, and_self, ↓reduceIte]; word
        · simp only [h2, and_false, ↓reduceIte]; word
      · have := hend rfl
        simp only [Bool.true_eq_false, and_false, ↓reduceIte]; word
    · simp only [Bool.true_eq_false, false_and, ↓reduceIte]; word
  · simp only [h1, ↓reduceIte, false_and]; word

theorem kv_of_find (ks : List GoString) (M : GMap GoString kvRec) (s : List EtcdKv) (key : GoString)
    (kv : EtcdKv) (hM : stMatch ks M s) (hf : findKey key s = some kv) :
    ∃ r, M !! key = some r ∧ kv = kvOfRec key r := by
  have h := hM.1 key
  rw [hf] at h
  cases hk : M !! key with
  | none => rw [hk] at h; cases h
  | some r => rw [hk] at h; exact ⟨r, rfl, Option.some.inj h⟩

theorem taken_keys {α : Type} (A : List (GoString × α)) (ks : List GoString) (lim : w64)
    (hA : A.map Prod.fst = ks) (i : Nat) (a : GoString × α)
    (h : (takeLimit (limitOf lim) A)[i]? = some a) : ks[i]? = some a.1 := by
  have hi : A[i]? = some a := by
    unfold takeLimit at h; split at h
    · rw [List.getElem?_take] at h; split at h
      · exact h
      · cases h
    · exact h
  rw [← hA, List.getElem?_map, hi]; rfl

theorem checkRangeAt.wp_proof (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_inRange : inRange.spec (GF := GF) (hG := hG))
    (wp_checkKV : checkKV.spec (GF := GF) (hG := hG))
    (errVars : mvcc.api.errVars.law (GF := GF)) :
    checkRangeAt.spec (GF := GF) (hG := hG) := by
  intro keys ks dks states dsl ms Ms dqs cur cmp q kk e dk de res err L hks hok hcur hlen hM
  wp_start as ⟨Hksl, Hsl, Hst, Hk, He, %Hres, Hout⟩
  ihave Hinit := errVars $$ Hpkg2
  icases Hinit with ⟨#HeCmp, #HeFut, -⟩
  iunfold errorsNewVar at HeFut
  icases HeFut with ⟨%xf, #HeFut, -⟩
  iunfold errorsNewVar at HeCmp
  icases HeCmp with ⟨%xc, #HeCmp, -⟩
  iunfold rangeOutcomeC at Hout
  wp_auto
  wp_if_destruct
  · -- a future revision: the first arm
    icases Hout with (⟨%Hc, -⟩ | ⟨-, Hout⟩)
    · exfalso; rename_i Hlt; omega
    iunfold rangeOutcome at Hout
    icases Hout with (⟨-, ⟨%ef, #Hef, %Herr⟩, Hr⟩ | ⟨%Hn, -, %Hnull, -⟩ | ⟨%Hn, -⟩)
    rotate_left
    · exfalso; exact Hres Hnull
    · exfalso; rename_i Hlt; omega
    ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hef HeFut
    subst Herr
    simp only [interface.mkOk] at Hag
    injection Hag with Hag
    subst Hag
    wp_auto
    wp_apply wp_check
    · itrivial
    icases typedPointsto_split _ _ _ $$ Hr with Hr
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hr
    simp only [decide_eq_false Hres, Bool.not_false]
    (try wp_auto)
    wp_apply wp_check
    · itrivial
    (try wp_auto)
    iapply HΦ; iframe
  · -- not a future revision
    have Hnf : sint.Z q.ro'.Rev' ≤ sint.Z cur := by word
    wp_join iprop(rev_ptr ↦ rangeRev cur q.ro'.Rev' ∗ cur_ptr ↦ cur) with [rev cur]
      as ⟨rev, cur⟩
    · have hRR : rangeRev cur q.ro'.Rev' = cur := by
        unfold rangeRev; rw [ite_eq_left (by word)]
      rw [hRR]; (try wp_auto); iframe
    · have hRR : rangeRev cur q.ro'.Rev' = q.ro'.Rev' := by
        unfold rangeRev; rw [ite_eq_right (by word)]
      rw [hRR]; (try wp_auto); iframe
    (try wp_auto)
    wp_if_destruct
    · -- a compacted revision: the first arm
      icases Hout with (⟨%Hc, ⟨%ec, #Hec, %Herr⟩, Hr⟩ | ⟨%Hc, -⟩)
      rotate_left
      · exfalso; have := Hc Hnf; word
      ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hec HeCmp
      subst Herr
      simp only [interface.mkOk] at Hag
      injection Hag with Hag
      subst Hag
      wp_auto
      wp_apply wp_check
      · itrivial
      icases typedPointsto_split _ _ _ $$ Hr with Hr
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hr
      simp only [decide_eq_false Hres, Bool.not_false]
      (try wp_auto)
      wp_apply wp_check
      · itrivial
      (try wp_auto)
      iapply HΦ; iframe
    have Hnc : sint.Z cmp ≤ sint.Z (rangeRev cur q.ro'.Rev') := by word
    icases Hout with (⟨%Hc, -⟩ | ⟨-, Hout⟩)
    · exfalso; omega
    iunfold rangeOutcome at Hout
    icases Hout with (⟨%Hf, -⟩ | ⟨%Hn, -, %Hnull, -⟩ | ⟨%Hn, %Herr, Hr⟩)
    · exfalso; omega
    · exfalso; exact Hres Hnull
    subst Herr
    -- the result's fields, its two shapes in one
    ihave Hr' : (∃ (kvs : GoSlice) (cnt : w64),
        res ↦ ({ KVs' := kvs, Rev' := cur, Count' := cnt } : go_etcd_io.etcd.server.v3.storage.mvcc.RangeResult) ∗
        (if q.ro'.CountOnly' then
          ⌜kvs = slice.nil ∧ cnt = W64 (rangeAnswers L (decide (q.end' = slice.nil)) kk e
            (rangeRev cur q.ro'.Rev')).length⌝
        else
          ⌜cnt = W64 (rangeTotal L (decide (q.end' = slice.nil)) kk e (rangeRev cur q.ro'.Rev')
            q.ro'.Limit' q.ro'.WithTotalCount')⌝ ∗
          rangeKvs (!q.ro'.FastKeysOnly') kvs (stateAt L (sint.nat (rangeRev cur q.ro'.Rev')))
            (rangeTaken L (decide (q.end' = slice.nil)) kk e (rangeRev cur q.ro'.Rev') q.ro'.Limit')) :
        IProp GF) $$ [Hr]
    · cases hco : q.ro'.CountOnly'
      · simp only [hco, Bool.false_eq_true, ↓reduceIte]
        icases Hr with ⟨%kvs, Hr, Hkvs⟩
        iexists kvs, _
        iframe
        ipureintro; rfl
      · simp only [hco, ↓reduceIte]
        iexists slice.nil, _
        iframe
        ipureintro; exact ⟨rfl, rfl⟩
    icases Hr' with ⟨%kvs, %cnt, Hr, Hro⟩
    icases typedPointsto_split _ _ _ $$ Hr with Hr
    simp only [TypedPointsto.typedPointstoDef]
    icases Hr with ⟨KVs, Rev, Count, -⟩
    (try wp_auto)
    wp_apply wp_check
    · itrivial
    (try wp_auto)
    simp only [decide_eq_false Hres, Bool.not_false]
    (try wp_auto)
    wp_apply wp_check
    · itrivial
    (try wp_auto)
    have hR0 : 0 ≤ sint.Z (rangeRev cur q.ro'.Rev') := by unfold rangeRev; split <;> word
    have hRle : sint.Z (rangeRev cur q.ro'.Rev') ≤ sint.Z cur := by unfold rangeRev; split <;> word
    obtain ⟨M, hMs, hMm⟩ := hM (sint.nat (rangeRev cur q.ro'.Rev'))
      (by have : sint.nat (rangeRev cur q.ro'.Rev') = (sint.Z (rangeRev cur q.ro'.Rev')).toNat := rfl
          omega) (Int.toNat_le_toNat hRle)
    iunfold statesAt at Hst
    icases Hst with ⟨%Hlens, Hst⟩
    have hidx : (sint.Z (rangeRev cur q.ro'.Rev')).toNat < ms.length := by
      exact Nat.lt_of_le_of_lt (Int.toNat_le_toNat hRle) hlen
    ihave %Hsll := ownSlice_len $$ Hsl
    have hb : 0 ≤ sint.Z (rangeRev cur q.ro'.Rev') ∧
        sint.Z (rangeRev cur q.ro'.Rev') < sint.Z states.len := by
      refine ⟨hR0, ?_⟩
      obtain ⟨h1, h2⟩ := Hsll
      have h3 := hidx; rw [h1] at h3
      have h4 : sint.nat states.len = (sint.Z states.len).toNat := rfl
      rw [h4] at h3
      have := Int.toNat_of_nonneg hR0; have := Int.toNat_of_nonneg h2; omega
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index states (sint.Z (rangeRev cur q.ro'.Rev')) ms dsl
      (ms[(sint.Z (rangeRev cur q.ro'.Rev')).toNat]'hidx) hR0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact List.getElem?_eq_getElem hidx
    -- the map of revision `rr`, and the keys
    have hidx2 : (sint.Z (rangeRev cur q.ro'.Rev')).toNat < dqs.length := by omega
    have hzip : (ms.zip (Ms.zip dqs))[(sint.Z (rangeRev cur q.ro'.Rev')).toNat]? =
        some (ms[(sint.Z (rangeRev cur q.ro'.Rev')).toNat]'hidx,
          (M, dqs[(sint.Z (rangeRev cur q.ro'.Rev')).toNat]'hidx2)) := by
      rw [List.getElem?_zip_eq_some]
      refine ⟨List.getElem?_eq_getElem hidx, ?_⟩
      rw [List.getElem?_zip_eq_some]
      exact ⟨hMs, List.getElem?_eq_getElem hidx2⟩
    generalize hmp : ms[(sint.Z (rangeRev cur q.ro'.Rev')).toNat]'hidx = mp at hzip
    generalize hdqm : dqs[(sint.Z (rangeRev cur q.ro'.Rev')).toNat]'hidx2 = dqm at hzip
    ihave ⟨Hm, Hback⟩ := (BigSepL.bigSepL_lookup_acc hzip).1 $$ Hst
    have hset : (ms.zip (Ms.zip dqs)).set (sint.Z (rangeRev cur q.ro'.Rev')).toNat (mp, (M, dqm)) =
        ms.zip (Ms.zip dqs) := by
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hzip
      rw [← heq, List.set_getElem_self]
    ihave Hback : (mp ↦${dqm} M -∗ [∗list] x ∈ ms.zip (Ms.zip dqs), x.1 ↦${x.2.2} x.2.1) $$ [Hback]
    · iintro Hm
      ihave H := Hback $$ %(mp, (M, dqm)) Hm
      rw [hset]; iexact H
    ihave %Hksn := ownSlice_len $$ Hksl
    have hks6 : sint.Z keys.len = ks.length := by
      have h := Hksn.1
      have h4 : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
      have := Hksn.2; omega
    (try wp_auto)
    -- the match loop
    ihave HI : (∃ (j : w64) (msl : GoSlice) (kv0 : GoString),
        "i" ∷ i_ptr ↦ j ∗ "Hmatch" ∷ match_ptr ↦ msl ∗
        "Hml" ∷ msl ↦* ((ks.take (sint.nat j)).filter
          (fun key => (M !! key).isSome && inRangeM (decide (q.end' = slice.nil)) kk e key)) ∗
        "Hmc" ∷ ownSliceCap GoString msl (DFrac.own 1) ∗ "k" ∷ k_ptr ↦ kv0 ∗
        "Hm" ∷ mp ↦${dqm} M ∗
        "q" ∷ q_ptr ↦ q ∗ "Hk" ∷ q.key' ↦*{dk} kk ∗ "He" ∷ q.end' ↦*{de} e ∗
        "Hksl" ∷ keys ↦*{dks} ks ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ ks.length⌝ : IProp GF) $$ [i «match» k Hm q Hk He Hksl]
    · iexists W64 0, slice.nil, _
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil]
      iframe
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      ipureintro; constructor <;> word
    wp_for HI
    have hmatch_succ : ∀ (n : Nat) (x : GoString) (pr : GoString → Bool), ks[n]? = some x →
        (ks.take (n + 1)).filter pr =
          (ks.take n).filter pr ++ (if pr x then [x] else []) := by
      intro n x pr hx
      rw [List.take_add_one, hx, List.filter_append]
      cases h : pr x <;> simp [List.filter, h]
    by_cases Hlt : sint.Z j < sint.Z keys.len
    · -- an iteration
      rw [decide_eq_true Hlt]; simp only [↓reduceIte]
      have hj6 : sint.Z j < ks.length := by rw [← hks6]; exact Hlt
      list_elem ks (sint.nat j) as x
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z keys.len := ⟨Hj.1, Hlt⟩
      (try wp_auto)
      (try simp only [hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index keys (sint.Z j) ks dks x Hj.1 $$ [Hksl] as Hksl
      · iframe; ipureintro; exact Hx_lookup
      (try wp_auto)
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      wp_apply (wp_map_lookup2 go.string kvRec.ty mp M x dqm) $$ [$Hm] as Hm
      (try wp_auto)
      wp_if_destruct
      · -- present: the range check
        wp_apply wp_inRange q.key' q.end' kk e x dk de $$ [$Hk $He] as ⟨Hk, He⟩
        (try wp_auto)
        cases hin : inRangeM (decide (q.end' = slice.nil)) kk e x
        rotate_left
        · -- in the range: appended
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %osl ⟨Hosl, -⟩
          (try wp_auto)
          wp_apply wp_slice_append $$ [$Hml $Hmc $Hosl] as %msl' ⟨Hml, Hmc, -⟩
          wp_for_post
          iframe
          iexists j + W64 1, msl', x
          rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
          simp only [hin, Bool.and_true, Hif, ↓reduceIte]
          iframe
          ipureintro; constructor <;> word
        · (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, msl, x
          rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
          simp only [hin, Bool.and_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          iframe
          ipureintro; constructor <;> word
      · (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, msl, x
        rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
        have hpf : (M !! x).isSome = false := by simpa using Hif
        simp only [hpf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil]
        iframe
        ipureintro; constructor <;> word
    · -- the loop's end: `match` is `matchKeys`, the index's answers' keys
      rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hj6 : sint.nat j = ks.length := by
        have : ¬ sint.Z j < ks.length := by rw [← hks6]; exact Hlt
        have h0 := Hj.2; have h4 : sint.nat j = (sint.Z j).toNat := rfl; rw [h4]; omega
      have htk : ks.take ks.length = ks := List.take_length
      simp only [hj6, htk]
      have hW : W64 ((sint.nat (rangeRev cur q.ro'.Rev') : Nat) : Int) = rangeRev cur q.ro'.Rev' := by
        word
      have hA : (rangeAnswers L (decide (q.end' = slice.nil)) kk e (rangeRev cur q.ro'.Rev')).map
          Prod.fst = matchKeys ks M (decide (q.end' = slice.nil)) kk e := by
        have h := answers_keys_eq_match ks hks L hok (decide (q.end' = slice.nil)) kk e
          (sint.nat (rangeRev cur q.ro'.Rev')) (by word) M hMm
        rwa [hW] at h
      ihave %Hmll := ownSlice_len $$ Hml
      have hAl : (rangeAnswers L (decide (q.end' = slice.nil)) kk e (rangeRev cur q.ro'.Rev')).length =
          sint.nat msl.len := by
        have := congrArg List.length hA
        rw [List.length_map] at this
        rw [this, ← Hmll.1]; rfl
      (try wp_auto)
      cases hco : q.ro'.CountOnly'
      · simp only [hco, Bool.false_eq_true, ↓reduceIte]
        simp only [hco, Bool.false_eq_true, ↓reduceIte] at *
        (try wp_auto)
        icases Hro with ⟨%Hcnt, Hkvs⟩
        iunfold rangeKvs at Hkvs
        icases Hkvs with ⟨%ps, Hps, %Hpsl, Hall⟩
        ihave %Hpsn := ownSlice_len $$ Hps
        have hmsl0 : 0 ≤ sint.Z msl.len := Hmll.2
        have h00 : sint.Z (W64 0) = 0 := rfl
        -- taken
        wp_join iprop(taken_ptr ↦ takenOf q.ro'.Limit' msl.len ∗ n_ptr ↦ msl.len ∗ q_ptr ↦ q) at next
          with [taken n q] as ⟨taken, n, q⟩
        · simp only [h00]
          by_cases h1 : 0 < sint.Z q.ro'.Limit'
          · rw [decide_eq_true h1]; (try wp_auto)
            by_cases h2 : sint.Z q.ro'.Limit' < sint.Z msl.len
            · rw [decide_eq_true h2]; (try wp_auto)
              rw [show takenOf q.ro'.Limit' msl.len = q.ro'.Limit' from if_pos ⟨h1, h2⟩]
              wp_join_done
            · rw [decide_eq_false h2]; (try wp_auto)
              rw [show takenOf q.ro'.Limit' msl.len = msl.len from if_neg (fun h => h2 h.2)]
              wp_join_done
          · rw [decide_eq_false h1]; (try wp_auto)
            rw [show takenOf q.ro'.Limit' msl.len = msl.len from if_neg (fun h => h1 h.1)]
            wp_join_done
        -- total
        wp_join iprop(total_ptr ↦ totalOfT q.ro'.Limit' msl.len q.ro'.WithTotalCount'
            (decide (q.end' = slice.nil)) ∗ taken_ptr ↦ takenOf q.ro'.Limit' msl.len ∗ q_ptr ↦ q) at next
          with [total taken q] as ⟨total, taken, q⟩
        · simp only [h00]
          by_cases h1 : 0 < sint.Z q.ro'.Limit'
          · rw [decide_eq_true h1]; (try wp_auto)
            cases hwt : q.ro'.WithTotalCount'
            · (try wp_auto)
              by_cases hn : q.end' = slice.nil
              · simp only [hn, decide_true, Bool.not_true]; (try wp_auto)
                rw [show totalOfT q.ro'.Limit' msl.len false true = msl.len from if_neg (by simp)]
                wp_join_done
              · simp only [hn, decide_false, Bool.not_false]; (try wp_auto)
                rw [show totalOfT q.ro'.Limit' msl.len false false = takenOf q.ro'.Limit' msl.len
                  from if_pos ⟨h1, rfl, rfl⟩]
                wp_join_done
            · (try wp_auto)
              rw [show totalOfT q.ro'.Limit' msl.len true (decide (q.end' = slice.nil)) = msl.len
                from if_neg (by simp)]
              wp_join_done
          · rw [decide_eq_false h1]; (try wp_auto)
            rw [show totalOfT q.ro'.Limit' msl.len q.ro'.WithTotalCount' (decide (q.end' = slice.nil)) =
              msl.len from if_neg (fun h => h1 h.1)]
            wp_join_done
        -- the count and the number of key-values
        have hr : sint.nat (rangeRev cur q.ro'.Rev') < 2 ^ 63 := by word
        have hTot : cnt = totalOfT q.ro'.Limit' msl.len q.ro'.WithTotalCount'
            (decide (q.end' = slice.nil)) := by
          rw [Hcnt, ← hW, txn.rangeTotal_stateAt L hok _ kk e _ hr,
            ← txn.rangeAnswers_length L hok _ kk e _ hr, hW]
          apply totalOf_eq _ _ _ _ _ hAl hmsl0
          intro hend; rw [hend]; exact mvcc.rangeAnswers_nil_length_le L kk e _
        have hTK : (rangeTaken L (decide (q.end' = slice.nil)) kk e (rangeRev cur q.ro'.Rev')
            q.ro'.Limit').length = sint.nat (takenOf q.ro'.Limit' msl.len) := by
          rw [txn.rangeTaken_eq]; exact takeLimit_length_takenOf _ _ _ hAl hmsl0
        wp_apply wp_check
        · ipureintro; simp [hTot]
        (try wp_auto)
        wp_apply wp_check
        · ipureintro
          have h1 := Hpsn.1; rw [Hpsl, hTK] at h1
          have : kvs.len = takenOf q.ro'.Limit' msl.len := by
            have := Hpsn.2
            have h3 : 0 ≤ sint.Z (takenOf q.ro'.Limit' msl.len) := by
              unfold takenOf; split <;> word
            unfold sint.nat at h1; apply BitVec.eq_of_toInt_eq; unfold sint.Z at *; omega
          simp [this]
        (try wp_auto)
        -- the key-values, one by one
        rw [txn.rangeTaken_eq] at hTK Hpsl
        generalize hTKd : takeLimit (limitOf q.ro'.Limit') (rangeAnswers L (decide (q.end' = slice.nil))
          kk e (rangeRev cur q.ro'.Rev')) = TK at hTK Hpsl
        rw [txn.rangeTaken_eq, hTKd]
        have hTKk : ∀ (i : Nat) (a : GoString × Rev × w64 × w64), TK[i]? = some a →
            (matchKeys ks M (decide (q.end' = slice.nil)) kk e)[i]? = some a.1 := by
          intro i a h; rw [← hTKd] at h; exact taken_keys _ _ _ hA i a h
        ihave HJ : (∃ i0 : w64, "i" ∷ i_ptr ↦ i0 ∗ "Hps" ∷ kvs ↦* ps ∗
            "Hall" ∷ ([∗list] pa ∈ (ps.zip TK).drop (sint.nat i0), ∃ kv : EtcdKv,
              ⌜findKey pa.2.1 (stateAt L (sint.nat (rangeRev cur q.ro'.Rev'))) = some kv⌝ ∗
              kvPtrIs (!q.ro'.FastKeysOnly') pa.1 kv) ∗
            "%Hi" ∷ ⌜0 ≤ sint.Z i0 ∧ sint.Z i0 ≤ sint.Z (takenOf q.ro'.Limit' msl.len)⌝ : IProp GF)
          $$ [i Hps Hall]
        · iexists W64 0
          iframe
          ipureintro
          have : 0 ≤ sint.Z (takenOf q.ro'.Limit' msl.len) := by unfold takenOf; split <;> word
          constructor <;> word
        wp_for HJ
        have hT0 : 0 ≤ sint.Z (takenOf q.ro'.Limit' msl.len) := by unfold takenOf; split <;> word
        have hTle : sint.Z (takenOf q.ro'.Limit' msl.len) ≤ sint.Z msl.len := by
          unfold takenOf; split <;> omega
        by_cases Hlt : sint.Z i0 < sint.Z (takenOf q.ro'.Limit' msl.len)
        · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
          have hn : ∀ x : w64, sint.nat x = (sint.Z x).toNat := fun _ => rfl
          have hi0 : sint.nat i0 < TK.length := by rw [hTK, hn, hn]; omega
          have hip : sint.nat i0 < ps.length := by rw [Hpsl]; exact hi0
          have hiz : sint.nat i0 < (ps.zip TK).length := by simp; omega
          rw [List.drop_eq_getElem_cons hiz, List.getElem_zip]
          icases Hall with ⟨⟨%kv, %hfk, Hkv⟩, Hall⟩
          have hka := hTKk (sint.nat i0) (TK[sint.nat i0]'hi0) (List.getElem?_eq_getElem hi0)
          obtain ⟨r, hr, hkv⟩ := kv_of_find ks M _ _ kv hMm hfk
          subst hkv
          have hkb : 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z kvs.len := by
            refine ⟨Hi.1, ?_⟩; have h5 := Hpsn.1; rw [Hpsl, hTK, hn, hn] at h5; omega
          have hmb : 0 ≤ sint.Z i0 ∧ sint.Z i0 < sint.Z msl.len := ⟨Hi.1, by omega⟩
          (try wp_auto)
          (try simp only [hkb, hmb, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index kvs (sint.Z i0) ps (DFrac.own 1) (ps[sint.nat i0]'hip) Hi.1
            $$ [Hps] as Hps
          · iframe; ipureintro; exact List.getElem?_eq_getElem hip
          (try wp_auto)
          (try simp only [hkb, hmb, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index msl (sint.Z i0) _ (DFrac.own 1) (TK[sint.nat i0]'hi0).1 Hi.1
            $$ [Hml] as Hml
          · iframe; ipureintro; exact hka
          (try wp_auto)
          (try simp only [hkb, hmb, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index msl (sint.Z i0) _ (DFrac.own 1) (TK[sint.nat i0]'hi0).1 Hi.1
            $$ [Hml] as Hml
          · iframe; ipureintro; exact hka
          (try wp_auto)
          wp_apply (wp_map_lookup1 go.string kvRec.ty mp M (TK[sint.nat i0]'hi0).1 dqm) $$ [$Hm] as Hm
          rw [hr]; simp only [Option.getD_some]
          (try wp_auto)
          iunfold kvPtrIs at Hkv
          icases Hkv with ⟨%ks0, %st0, %uf0, %sc0, #Hks0, Hkv⟩
          cases hfo : q.ro'.FastKeysOnly'
          · simp only [hfo, Bool.not_false, ↓reduceIte] at *
            icases Hkv with ⟨%vs0, #Hvs0, Hp⟩
            wp_apply (wp_checkKV _ _ (DFrac.own 1) DFrac.discard DFrac.discard _ _
              (TK[sint.nat i0]'hi0).1 r false (by
                refine ⟨rfl, rfl, rfl, rfl, ?_⟩; simp [kvOfRec])) $$ [$Hp $Hks0 $Hvs0] as -
            wp_for_post
            iframe
            iexists i0 + W64 1
            rw [show sint.nat (i0 + W64 1) = sint.nat i0 + 1 by word]
            iframe
            ipureintro; constructor <;> word
          · simp only [hfo, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at *
            ihave Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
            · iapply ownSlice_nil
            wp_apply (wp_checkKV _ _ (DFrac.own 1) DFrac.discard DFrac.discard _ []
              (TK[sint.nat i0]'hi0).1 r true (by
                refine ⟨rfl, rfl, rfl, rfl, ?_⟩; simp)) $$ [$Hkv $Hks0 $Hnil] as -
            wp_for_post
            iframe
            iexists i0 + W64 1
            rw [show sint.nat (i0 + W64 1) = sint.nat i0 + 1 by word]
            iframe
            ipureintro; constructor <;> word
        · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
          (try wp_auto)
          iapply HΦ
          iframe
          iunfold statesAt
          isplitr
          · ipureintro; exact Hlens
          iapply Hback $$ Hm
      · simp only [hco, ↓reduceIte]
        icases Hro with %Hro
        obtain ⟨rfl, rfl⟩ := Hro
        (try wp_auto)
        wp_apply wp_check
        · ipureintro; rw [hAl]; simp; word
        (try wp_auto)
        iapply HΦ
        iframe
        iunfold statesAt
        isplitr
        · ipureintro; exact Hlens
        iapply Hback $$ Hm

end proof

end mvccfull
end EtcdGrove
end Perennial
