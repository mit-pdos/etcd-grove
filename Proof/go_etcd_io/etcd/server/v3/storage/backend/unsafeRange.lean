/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/unsafeRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.unsafeRange
public import Spec.go_etcd_io.bbolt.Cursor__Seek_kv
public import Spec.go_etcd_io.bbolt.Cursor__Next_kv
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `cursorRange` as the loop computes it: the entries from the seek position matching
`isMatch`, at most the effective limit. -/
theorem backend.cursorRange_eq (es : List Ent) (kb eb : GoString) (limit : w64) :
    cursorRange es kb eb limit =
      ((es.drop (seekIdx es kb)).takeWhile (fun e =>
          if eb = [] then decide (e.1 = kb) else decide (strLt e.1 eb))).take
        (sint.Z (if eb = [] then W64 1 else
          (if sint.Z limit ≤ 0 then W64 (2 ^ 63 - 1) else limit))).toNat := by
  unfold cursorRange
  by_cases heb : eb = []
  · simp only [heb, ite_true]; rfl
  · simp only [heb, ite_false]
    by_cases hl : sint.Z limit ≤ 0
    · simp only [hl, ite_true]; rfl
    · simp only [hl, ite_false]

/-- The loop's result at its exit: the first `i` entries from the seek position match, and the
loop stopped at the end, at an entry that does not match, or at the limit. -/
theorem backend.cursorRange_take (es : List Ent) (kb eb : GoString) (limit : w64) (i : Nat)
    (hall : ∀ (k : Nat) (x : Ent), k < i → (es.drop (seekIdx es kb))[k]? = some x →
      (if eb = [] then decide (x.1 = kb) else decide (strLt x.1 eb)) = true)
    (hle : i ≤ (sint.Z (if eb = [] then W64 1 else
          (if sint.Z limit ≤ 0 then W64 (2 ^ 63 - 1) else limit))).toNat)
    (hend : i = (es.drop (seekIdx es kb)).length ∨
      (∃ x, (es.drop (seekIdx es kb))[i]? = some x ∧
        (if eb = [] then decide (x.1 = kb) else decide (strLt x.1 eb)) = false) ∨
      i = (sint.Z (if eb = [] then W64 1 else
          (if sint.Z limit ≤ 0 then W64 (2 ^ 63 - 1) else limit))).toNat) :
    cursorRange es kb eb limit = (es.drop (seekIdx es kb)).take i := by
  rw [cursorRange_eq]
  exact takeWhile_take_eq _ _ _ _ hall hle hend

theorem backend.unsafeRange.wp_proof
    (hSeek : bbolt.Cursor.Seek_kv.spec (GF := GF) (hG := hG))
    (hNext : bbolt.Cursor.Next_kv.spec (GF := GF) (hG := hG)) :
    backend.unsafeRange.spec (GF := GF) (hG := hG) := by
  intro tx c es pos q key endKey kb eb dk de limit
  wp_start as ⟨Hcur, Hlive, Hk, He⟩
  wp_auto
  wp_join iprop(limit_ptr ↦ (if sint.Z limit ≤ 0 then W64 (2 ^ 63 - 1) else limit))
    with [limit] as limit
  · rw [if_pos (show sint.Z limit ≤ 0 by word)]; iframe
  · rw [if_neg (show ¬ sint.Z limit ≤ 0 by word)]; iframe
  ihave %Hel := ownSlice_len _ _ _ $$ He
  -- `isMatch` and the limit
  let mt : GoString → Bool := fun b => if eb = [] then decide (b = kb) else decide (strLt b eb)
  let lim1 : w64 := if eb = [] then W64 1 else (if sint.Z limit ≤ 0 then W64 (2 ^ 63 - 1) else limit)
  wp_join iprop(∃ f : GoFunc, isMatch_ptr ↦ f ∗ limit_ptr ↦ lim1 ∗
      □ (∀ (b : GoSlice) (dq : DFrac) (bs : GoString),
        {{ key_ptr ↦ key ∗ endKey_ptr ↦ endKey ∗ key ↦*{dk} kb ∗ endKey ↦*{de} eb ∗ b ↦*{dq} bs }}
          (App (Val #f) (Val #b))
        {{ RET #(mt bs); key_ptr ↦ key ∗ endKey_ptr ↦ endKey ∗ key ↦*{dk} kb ∗
            endKey ↦*{de} eb ∗ b ↦*{dq} bs }}))
    with [limit isMatch] as ⟨%f, isMatch, limit, #Hf⟩
  · have heb : eb ≠ [] := by intro h; subst h; simp at Hel; word
    iexists _
    iframe
    isplitl [limit]
    · simp only [lim1, heb, ite_false]; iframe
    imodintro
    iintro %b %dq %bs
    wp_start_folded as ⟨key, endKey, Hk, He, Hb⟩
    wp_auto
    wp_apply (bytes.wp_Compare _ _ dq de bs eb) $$ [$Hb $He] as ⟨Hb, He⟩
    rw [compareResult_neg, show decide (strLt bs eb) = mt bs by simp only [mt, heb, ite_false]]
    iapply HΦ
    iframe
  · have heb : eb = [] := List.eq_nil_of_length_eq_zero (by rw [Hel.1]; word)
    iexists _
    iframe
    isplitl [limit]
    · simp only [lim1, heb, ite_true]; iframe
    imodintro
    iintro %b %dq %bs
    wp_start_folded as ⟨key, endKey, Hk, He, Hb⟩
    wp_auto
    wp_apply (bytes.wp_Equal _ _ dq dk bs kb) $$ [$Hb $Hk] as ⟨Hb, Hk⟩
    rw [show decide (bs = kb) = mt bs by simp only [mt, heb, ite_true]]
    iapply HΦ
    iframe
  wp_apply hSeek $$ [$Hcur $Hlive $Hk] as %ck0 %cv0 ⟨Hcur, Hlive, Hk, #Hat⟩
  have Hseek_le : seekIdx es kb ≤ es.length := by
    unfold seekIdx; exact (List.takeWhile_sublist _).length_le
  -- the loop, over the entries from the seek position while they match, at most `lim1`
  have hL1 : 1 ≤ sint.Z lim1 := by
    simp only [lim1]; split
    · decide
    · split
      · decide
      · word
  have hL2 : sint.Z lim1 ≤ 2 ^ 63 - 1 := by
    simp only [lim1]; split
    · decide
    · split
      · decide
      · word
  ihave Hn1 := ownSlice_nil (GF := GF) (V := GoSlice) (DFrac.own 1)
  ihave Hn1c := ownSliceCap_nil (GF := GF) (V := GoSlice)
  ihave Hn2 := ownSlice_nil (GF := GF) (V := GoSlice) (DFrac.own 1)
  ihave Hn2c := ownSliceCap_nil (GF := GF) (V := GoSlice)
  ihave Hr1 := rdSlices_nil (GF := GF) tx
  ihave Hr2 := rdSlices_nil (GF := GF) tx
  ihave HI : (∃ (i : Nat) (ck cv ks vs : GoSlice) (kl vl : List GoSlice),
      "ck" ∷ ck_ptr ↦ ck ∗ "cv" ∷ cv_ptr ↦ cv ∗ "keys" ∷ keys_ptr ↦ ks ∗ "vs" ∷ vs_ptr ↦ vs ∗
      "Hks" ∷ ks ↦* kl ∗ "Hksc" ∷ ownSliceCap GoSlice ks (DFrac.own 1) ∗
      "Hvs" ∷ vs ↦* vl ∗ "Hvsc" ∷ ownSliceCap GoSlice vs (DFrac.own 1) ∗
      "Hka" ∷ rdSlices tx kl (((es.drop (seekIdx es kb)).take i).map Prod.fst) ∗
      "Hva" ∷ rdSlices tx vl (((es.drop (seekIdx es kb)).take i).map Prod.snd) ∗
      "Hcur" ∷ ownCur tx c es (some (seekIdx es kb + i)) ∗
      "#Hat" ∷ curAt tx es (seekIdx es kb + i) ck cv ∗
      "%Hall" ∷ ⌜∀ (k : Nat) (x : Ent), k < i → (es.drop (seekIdx es kb))[k]? = some x →
        mt x.1 = true⌝ ∗
      "%Hi" ∷ ⌜(i : Int) < sint.Z lim1 ∧ seekIdx es kb + i ≤ es.length⌝ : IProp GF)
    $$ [ck cv keys vs Hn1 Hn1c Hn2 Hn2c Hr1 Hr2 Hcur Hat]
  · iexists 0, ck0, cv0, slice.nil, slice.nil, [], []
    simp only [List.take_zero, List.map_nil, Nat.add_zero]
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    iframe
    iframe #
    ipureintro
    refine ⟨fun k x hk _ => absurd hk (Nat.not_lt_zero _), by push_cast; word, Hseek_le⟩
  wp_for HI
  ihave %Hksl := ownSlice_len _ _ _ $$ Hks
  ihave %Hkal := rdSlices_length _ _ _ $$ Hka
  ihave %Hval := rdSlices_length _ _ _ $$ Hva
  simp only [List.length_map, List.length_take, List.length_drop] at Hkal Hval
  have Hmi : min i (es.length - seekIdx es kb) = i := by omega
  rw [Hmi] at Hkal Hval
  cases he : es[seekIdx es kb + i]? with
  | none =>
    -- the end of the bucket: `ck` is nil
    iclear Hf
    icases curAt_none _ _ _ _ _ he $$ Hat with %Hnil
    obtain ⟨rfl, rfl⟩ := Hnil
    wp_auto
    cleanup_bool_decide
    wp_auto
    have hlen : seekIdx es kb + i = es.length := by
      have := List.getElem?_eq_none_iff.1 he; omega
    rw [cursorRange_take es kb eb limit i Hall (by word) (Or.inl (by simp; omega))]
    iapply HΦ
    iframe
    unfold kvsOutRd
    iexists kl, vl
    iframe
  | some e =>
    icases curAt_some _ _ _ _ _ _ he $$ Hat with ⟨%Hnn, #Hek, #Hev⟩
    have hrest : (es.drop (seekIdx es kb))[i]? = some e := by
      rw [List.getElem?_drop]; exact he
    rw [_root_.decide_eq_false Hnn]
    wp_auto
    icases txBytes_acc tx ck e.1 q $$ [$Hek $Hlive] with ⟨%dq, Hck, Hlive⟩
    wp_apply Hf $$ [$key $endKey $Hk $He $Hck] as ⟨key, endKey, Hk, He, Hck⟩
    ihave Hlive := Hlive $$ Hck
    cases hm : mt e.1 with
    | false =>
      -- the entry does not match: the loop ends
      cleanup_bool_decide
      wp_auto
      rw [cursorRange_take es kb eb limit i Hall (by word) (Or.inr (Or.inl ⟨e, hrest, hm⟩))]
      iapply HΦ
      iframe
      unfold kvsOutRd
      iexists kl, vl
      iframe
    | true =>
      cleanup_bool_decide
      wp_auto
      wp_apply (wp_slice_literal (V := GoSlice) [cv])
      try (isplitr; (ipureintro; rfl))
      iintro %lv ⟨Hlv, -⟩
      wp_apply (wp_slice_append vs vl _ [cv] (DFrac.own 1)) $$ [Hvs Hvsc Hlv] as %vs' ⟨Hvs, Hvsc, -⟩
      · iframe
      wp_apply (wp_slice_literal (V := GoSlice) [ck])
      try (isplitr; (ipureintro; rfl))
      iintro %lk ⟨Hlk, -⟩
      wp_apply (wp_slice_append ks kl _ [ck] (DFrac.own 1)) $$ [Hks Hksc Hlk] as %ks' ⟨Hks, Hksc, -⟩
      · iframe
      ihave %Hksl' := ownSlice_len _ _ _ $$ Hks
      ihave Hka := rdSlices_snoc tx _ _ ck e.1 $$ [Hka]
      · iframe Hka; unfold rdB; iright; iexact Hek
      ihave Hva := rdSlices_snoc tx _ _ cv e.2 $$ [Hva]
      · iframe Hva; unfold rdB; iright; iexact Hev
      have htake : ((es.drop (seekIdx es kb)).take (i + 1)) =
          (es.drop (seekIdx es kb)).take i ++ [e] := by
        rw [List.take_add_one, hrest]; rfl
      have Hall' : ∀ (k : Nat) (x : Ent), k < i + 1 → (es.drop (seekIdx es kb))[k]? = some x →
          mt x.1 = true := by
        intro k x hk hx
        by_cases hki : k < i
        · exact Hall k x hki hx
        · have : k = i := by omega
          subst this; rw [hrest] at hx; cases hx; exact hm
      have Hlenk : sint.Z ks'.len = (i : Int) + 1 := by
        have := Hksl'.1; simp only [List.length_append, List.length_singleton] at this; word
      by_cases hlim : lim1 = ks'.len
      · -- the limit: the loop breaks
        rw [_root_.decide_eq_true hlim]
        wp_auto
        wp_for_post
        rw [cursorRange_take es kb eb limit (i + 1) Hall'
          (show i + 1 ≤ (sint.Z lim1).toNat by rw [hlim]; word)
          (Or.inr (Or.inr (show i + 1 = (sint.Z lim1).toNat by rw [hlim]; word)))]
        iapply HΦ
        iframe
        unfold kvsOutRd
        iexists kl ++ [ck], vl ++ [cv]
        rw [htake]
        simp only [List.map_append, List.map_cons, List.map_nil]
        iframe
      · rw [_root_.decide_eq_false hlim]
        wp_auto
        wp_for_post
        have hlt : seekIdx es kb + i < es.length := (List.getElem?_eq_some_iff.1 he).1
        wp_apply hNext $$ [$Hcur $Hlive] as %ck2 %cv2 ⟨Hcur, Hlive, #Hat2⟩
        rw [show min (seekIdx es kb + i + 1) es.length = seekIdx es kb + (i + 1) by omega]
        iframe
        iexists i + 1, ck2, cv2, ks', vs', kl ++ [ck], vl ++ [cv]
        rw [show seekIdx es kb + i + 1 = seekIdx es kb + (i + 1) by omega] at *
        rw [htake]
        simp only [List.map_append, List.map_cons, List.map_nil]
        iframe
        iframe #
        ipureintro
        refine ⟨Hall', ?_, by omega⟩
        have : sint.Z lim1 ≠ (i : Int) + 1 := by
          intro h; apply hlim; apply BitVec.eq_of_toInt_eq; rw [← Hlenk] at h; exact h
        push_cast; omega

end proof

end EtcdGrove
end Perennial
