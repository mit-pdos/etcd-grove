/-
Proof of `Spec/.../backend/bucketBuffer__Range.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Range
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RangeLemmas

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

/-- `Range`'s search predicate on the entries: the `i`-th key is not below `key`. -/
def rangePred (es : List Ent) (key : GoString) (i : Int) : Bool :=
  match es[i.toNat]? with
  | some e => !decide (strLt e.1 key)
  | none => true

theorem rangePred_mono (es : List Ent) (key : GoString) (hs : entsSorted es) :
    sort.IsMonoPred (rangePred es key) es.length := by
  intro i j ⟨hi, hij, hj⟩ hfi
  have hil : i.toNat < es.length := by omega
  have hjl : j.toNat < es.length := by omega
  unfold rangePred at hfi ⊢
  rw [List.getElem?_eq_getElem hil] at hfi
  rw [List.getElem?_eq_getElem hjl]
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hfi ⊢
  intro hj'
  apply hfi
  have hlt : strLt es[i.toNat].1 es[j.toNat].1 :=
    List.pairwise_iff_getElem.mp hs _ _ hil hjl (by omega)
  exact strLt_trans hlt hj'

theorem slicesAre_length (ss : List GoSlice) (bs : List GoString) :
    slicesAre (GF := GF) ss bs ⊢ ⌜ss.length = bs.length⌝ := by
  unfold slicesAre; iintro ⟨%H, _⟩; ipureintro; exact H

/-- `Range`'s results at the exit of its loop: the first `m` entries from `idx`, all below
`endKey`, and the loop stopped at the end, at an entry not below `endKey`, or at `limit`. -/
theorem range_finish (L : List Ent) (eb : GoString) (m lim : Nat) (ks vs : GoSlice)
    (kl vl : List GoSlice)
    (hall : ∀ (k : Nat) (x : Ent), k < m → L[k]? = some x → decide (strLt x.1 eb) = true)
    (hle : m ≤ lim)
    (hend : m = L.length ∨ (∃ x, L[m]? = some x ∧ decide (strLt x.1 eb) = false) ∨ m = lim) :
    ks ↦* kl ∗ ownSliceCap GoSlice ks (DFrac.own 1) ∗ vs ↦* vl ∗
      ownSliceCap GoSlice vs (DFrac.own 1) ∗
      slicesAre kl ((L.take m).map Prod.fst) ∗ slicesAre vl ((L.take m).map Prod.snd) ⊢
    kvsOut (GF := GF) ks vs ((L.takeWhile (fun e => decide (strLt e.1 eb))).take lim) := by
  rw [takeWhile_take_eq _ L m lim hall hle hend]
  unfold kvsOut
  iintro ⟨Hks, Hksc, Hvs, Hvsc, Hka, Hva⟩
  iexists kl, vl
  iframe

theorem backend.bucketBuffer.Range.wp_proof : backend.bucketBuffer.Range.spec (GF := GF) (hG := hG) := by
  intro bb dq p es key endKey kb eb dk de limit Hsorted
  wp_start as ⟨H, Hk, He⟩
  iunfold bbAt at H
  icases H with ⟨Hbb, Hs, Hcap, #Hro, #Hin⟩
  icases bb_fields_acc _ _ _ $$ Hbb with ⟨Hbuf, Hused, Hbb⟩
  ihave #Hin2 := Hin
  iunfold entsIn at Hin2
  icases Hin2 with ⟨%Hle, -⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have Hlen : sint.Z (W64 (es.length : Int)) = es.length := by have := Hl.1; have := Hl.2; word
  wp_auto
  wp_apply sort.wp_Search (W64 (es.length : Int)) _ (rangePred es kb)
    iprop(bb_ptr ↦ bb ∗ key_ptr ↦ key ∗
      bb.[bucketBuffer, go!"buf"] ↦{dq} p.buf ∗ p.buf ↦*{dq} p.kvs ∗ key ↦*{dk} kb)
    $$ [bb key Hbuf Hs Hk]
  · iframe
    isplitl []
    · ipureintro; word
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨⟨bb, key, Hbuf, Hs, Hk⟩, %Hb⟩
      wp_auto
      have hil : sint.nat i < es.length := by rw [Hlen] at Hb; word
      have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.buf.len := by
        have := Hl.1; refine ⟨Hb.1, ?_⟩; word
      try simp only [Hbi, _root_.and_self, ite_true]
      list_elem es (sint.nat i) as e
      list_elem p.kvs (sint.nat i) as x
      wp_apply wp_load_slot_key p.buf (sint.Z i) p.kvs dq x Hb.1 Hx_lookup $$ Hs as Hs
      ihave ⟨#Hek, -⟩ := entsIn_lookup _ _ _ _ _ Hx_lookup He_lookup $$ Hin
      wp_apply (bytes.wp_Compare _ _ DFrac.discard dk e.1 kb) $$ [$Hek $Hk] as ⟨-, Hk⟩
      rw [compareResult_ge]
      iapply HΦ
      iframe
      ipureintro
      unfold rangePred
      rw [show (sint.Z i).toNat = sint.nat i from rfl, He_lookup]
    · ipureintro
      rw [Hlen]
      exact rangePred_mono es kb Hsorted
  iintro %idx ⟨⟨bb, key, Hbuf, Hs, Hk⟩, %Hidx0, %Hfound, %Hoob, %Hlow⟩
  rw [Hlen] at Hfound Hoob
  have Hidx_le : sint.Z idx ≤ es.length := by
    apply Classical.byContradiction
    intro h
    have := Hoob (fun i hi => Hlow i ⟨hi.1, by omega⟩)
    omega
  have hall : ∀ (k : Nat) (x : Ent), k < sint.nat idx → es[k]? = some x →
      decide (strLt x.1 kb) = true := by
    intro k x hk hx
    have := Hlow k ⟨by omega, by word⟩
    unfold rangePred at this
    rw [show ((k : Int)).toNat = k by omega, hx] at this
    simpa using this
  have hstop : ∀ x, es[sint.nat idx]? = some x → decide (strLt x.1 kb) = false := by
    intro x hx
    have hlt : sint.nat idx < es.length := (List.getElem?_eq_some_iff.1 hx).1
    have := Hfound (by word)
    unfold rangePred at this
    rw [show (sint.Z idx).toNat = sint.nat idx from rfl, hx] at this
    simpa using this
  have hdrop : es.dropWhile (fun e => decide (strLt e.1 kb)) = es.drop (sint.nat idx) :=
    dropWhile_eq_drop _ es (sint.nat idx) (by word) hall hstop
  wp_auto
  rw [_root_.decide_eq_false (show ¬ sint.Z idx < sint.Z (W64 0) by word)]
  wp_auto
  wp_if_destruct
  · -- every entry is below `key`
    have hnil : es.dropWhile (fun e => decide (strLt e.1 kb)) = [] := by
      rw [hdrop]; exact List.drop_of_length_le (by word)
    rw [bbRange_of_dropWhile_nil es kb eb limit hnil]
    ihave Hbb := Hbb $$ Hbuf Hused
    ihave Hout := kvsOut_nil_r (GF := GF)
    iapply HΦ
    iunfold bbAt
    iframe # ∗
  have hidx : sint.nat idx < es.length := by word
  list_elem es (sint.nat idx) as e
  list_elem p.kvs (sint.nat idx) as x
  have hcons : es.dropWhile (fun e => decide (strLt e.1 kb)) = e :: es.drop (sint.nat idx + 1) := by
    rw [hdrop, List.drop_eq_getElem_cons hidx, (List.getElem?_eq_some_iff.1 He_lookup).2]
  rw [bbRange_of_dropWhile_cons es kb eb limit e _ hcons]
  have Hbx : 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z p.buf.len := by
    have := Hl.1; refine ⟨Hidx0, ?_⟩; word
  ihave ⟨#Hek, #Hev⟩ := entsIn_lookup _ _ _ _ _ Hx_lookup He_lookup $$ Hin
  ihave %Hel := ownSlice_len _ _ _ $$ He
  wp_if_destruct
  · -- no `endKey`: the entry at `idx` if it is `key`
    have heb : eb = [] := List.eq_nil_of_length_eq_zero (by rw [Hel.1]; word)
    subst heb
    simp only [ite_true]
    try simp only [Hbx, _root_.and_self, ite_true]
    wp_apply wp_load_slot_key p.buf (sint.Z idx) p.kvs dq x Hidx0 Hx_lookup $$ Hs as Hs
    wp_apply (bytes.wp_Equal _ _ dk DFrac.discard kb e.1) $$ [$Hk $Hek] as ⟨Hk, -⟩
    wp_if_destruct
    · try simp only [Hbx, _root_.and_self, ite_true]
      wp_apply wp_load_slot_key p.buf (sint.Z idx) p.kvs dq x Hidx0 Hx_lookup $$ Hs as Hs
      wp_apply (wp_slice_literal (V := GoSlice) [x.key'])
      try (isplitr; (ipureintro; rfl))
      iintro %lk ⟨Hlk, -⟩
      ihave Hn1 := ownSlice_nil (GF := GF) (V := GoSlice) (DFrac.own 1)
      ihave Hn1c := ownSliceCap_nil (GF := GF) (V := GoSlice)
      rw [show (zero_val GoSlice) = slice.nil from rfl]
      wp_apply (wp_slice_append slice.nil ([] : List GoSlice) _ [x.key'] (DFrac.own 1))
        $$ [Hn1 Hn1c Hlk] as %ks ⟨Hks, Hkscap, -⟩
      · iframe Hlk; isplitr
        · iexact Hn1
        iexact Hn1c
      try simp only [Hbx, _root_.and_self, ite_true]
      wp_apply wp_load_slot_val p.buf (sint.Z idx) p.kvs dq x Hidx0 Hx_lookup $$ Hs as Hs
      wp_apply (wp_slice_literal (V := GoSlice) [x.val'])
      try (isplitr; (ipureintro; rfl))
      iintro %lv ⟨Hlv, -⟩
      wp_apply (wp_slice_append slice.nil ([] : List GoSlice) _ [x.val'] (DFrac.own 1))
        $$ [Hn1 Hn1c Hlv] as %vs ⟨Hvs, Hvscap, -⟩
      · iframe Hlv; isplitr
        · iexact Hn1
        iexact Hn1c
      ihave Hbb := Hbb $$ Hbuf Hused
      ihave Hsk := slicesAre_snoc [] [] x.key' e.1 $$ [Hek]
      · iframe Hek; iapply slicesAre_nil
      ihave Hsv := slicesAre_snoc [] [] x.val' e.2 $$ [Hev]
      · iframe Hev; iapply slicesAre_nil
      iapply HΦ
      iunfold bbAt
      iframe # ∗
      iunfold kvsOut
      iexists [x.key'], [x.val']
      simp only [List.nil_append, List.map_cons, List.map_nil]
      iframe
    · -- the entry at `idx` is not `key`
      ihave Hbb := Hbb $$ Hbuf Hused
      ihave Hout := kvsOut_nil_r (GF := GF)
      iapply HΦ
      iunfold bbAt
      simp only [show (e.1 = kb) = False from eq_false (Ne.symm Hif), ite_false]
      iframe # ∗
  -- an `endKey`
  have heb : eb ≠ [] := by
    intro h; subst h; apply Hif; have := Hel.1; simp at this; word
  simp only [heb, ite_false]
  try simp only [Hbx, _root_.and_self, ite_true]
  wp_apply wp_load_slot_key p.buf (sint.Z idx) p.kvs dq x Hidx0 Hx_lookup $$ Hs as Hs
  wp_apply (bytes.wp_Compare _ _ de DFrac.discard eb e.1) $$ [$He $Hek] as ⟨He, -⟩
  rw [compareResult_le]
  wp_if_destruct
  · -- the loop, over the entries from `idx` while below `endKey`, at most `limit`
    have hlt0 : strLt e.1 eb := by simpa using Hif
    have hL : es.drop (sint.nat idx) = e :: es.drop (sint.nat idx + 1) := by
      rw [List.drop_eq_getElem_cons hidx, (List.getElem?_eq_some_iff.1 He_lookup).2]
    rw [← hL]
    try wp_auto
    ihave HI : (∃ (i : w64) (ks vs : GoSlice) (kl vl : List GoSlice),
        "i" ∷ i_ptr ↦ i ∗ "keys" ∷ keys_ptr ↦ ks ∗ "vals" ∷ vals_ptr ↦ vs ∗
        "Hks" ∷ ks ↦* kl ∗ "Hksc" ∷ ownSliceCap GoSlice ks (DFrac.own 1) ∗
        "Hvs" ∷ vs ↦* vl ∗ "Hvsc" ∷ ownSliceCap GoSlice vs (DFrac.own 1) ∗
        "Hka" ∷ slicesAre kl (((es.drop (sint.nat idx)).take (sint.nat i - sint.nat idx)).map
          Prod.fst) ∗
        "Hva" ∷ slicesAre vl (((es.drop (sint.nat idx)).take (sint.nat i - sint.nat idx)).map
          Prod.snd) ∗
        "%Hi" ∷ ⌜sint.Z idx ≤ sint.Z i ∧ sint.Z i ≤ es.length⌝ ∗
        "%Hbelow" ∷ ⌜∀ (k : Nat) (y : Ent), k < sint.nat i - sint.nat idx →
          (es.drop (sint.nat idx))[k]? = some y → decide (strLt y.1 eb) = true⌝ ∗
        "%Hlim" ∷ ⌜sint.nat i - sint.nat idx ≤ (sint.Z limit).toNat⌝ : IProp GF)
      $$ [i keys vals]
    · iexists idx, slice.nil, slice.nil, [], []
      simp only [Nat.sub_self, List.take_zero, List.map_nil]
      iframe
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      isplitr
      · iapply slicesAre_nil
      isplitr
      · iapply slicesAre_nil
      ipureintro
      refine ⟨⟨Int.le_refl _, Hidx_le⟩, fun k y hk _ => absurd hk (Nat.not_lt_zero _), Nat.zero_le _⟩
    wp_for HI
    ihave %Hksl := ownSlice_len _ _ _ $$ Hks
    ihave %Hkal := slicesAre_length _ _ $$ Hka
    simp only [List.length_map, List.length_take, List.length_drop] at Hkal
    have Hm : min (sint.nat i - sint.nat idx) (es.length - sint.nat idx) = sint.nat i - sint.nat idx := by
      have := Hi.2; have := Hi.1; word
    have Hkm : kl.length = sint.nat i - sint.nat idx := by rw [Hkal, Hm]
    wp_if_destruct
    · wp_if_destruct
      · -- the body
        have hin : sint.nat i < es.length := by word
        list_elem es (sint.nat i) as y
        list_elem p.kvs (sint.nat i) as xi
        have Hi0 : 0 ≤ sint.Z i := by word
        have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.buf.len := by
          have := Hl.1; refine ⟨Hi0, by word⟩
        have hLy : (es.drop (sint.nat idx))[sint.nat i - sint.nat idx]? = some y := by
          rw [List.getElem?_drop, show sint.nat idx + (sint.nat i - sint.nat idx) = sint.nat i by word]
          exact Hy_lookup
        try simp only [Hbi, _root_.and_self, ite_true]
        wp_apply wp_load_slot_key p.buf (sint.Z i) p.kvs dq xi Hi0 Hxi_lookup $$ Hs as Hs
        ihave ⟨#Hyk, #Hyv⟩ := entsIn_lookup _ _ _ _ _ Hxi_lookup Hy_lookup $$ Hin
        wp_apply (bytes.wp_Compare _ _ de DFrac.discard eb y.1) $$ [$He $Hyk] as ⟨He, -⟩
        rw [compareResult_le]
        wp_if_destruct
        · -- below `endKey`: appended
          have hylt : strLt y.1 eb := by simpa using Hif
          try simp only [Hbi, _root_.and_self, ite_true]
          wp_apply wp_load_slot_key p.buf (sint.Z i) p.kvs dq xi Hi0 Hxi_lookup $$ Hs as Hs
          wp_apply (wp_slice_literal (V := GoSlice) [xi.key'])
          try (isplitr; (ipureintro; rfl))
          iintro %lk ⟨Hlk, -⟩
          wp_apply (wp_slice_append ks kl _ [xi.key'] (DFrac.own 1))
            $$ [Hks Hksc Hlk] as %ks' ⟨Hks, Hksc, -⟩
          · iframe
          try simp only [Hbi, _root_.and_self, ite_true]
          wp_apply wp_load_slot_val p.buf (sint.Z i) p.kvs dq xi Hi0 Hxi_lookup $$ Hs as Hs
          wp_apply (wp_slice_literal (V := GoSlice) [xi.val'])
          try (isplitr; (ipureintro; rfl))
          iintro %lv ⟨Hlv, -⟩
          wp_apply (wp_slice_append vs vl _ [xi.val'] (DFrac.own 1))
            $$ [Hvs Hvsc Hlv] as %vs' ⟨Hvs, Hvsc, -⟩
          · iframe
          wp_for_post
          ihave Hka := slicesAre_snoc _ _ xi.key' y.1 $$ [Hka]
          · iframe Hka; iexact Hyk
          ihave Hva := slicesAre_snoc _ _ xi.val' y.2 $$ [Hva]
          · iframe Hva; iexact Hyv
          iframe
          iexists i + W64 1, ks', vs', kl ++ [xi.key'], vl ++ [xi.val']
          have hm1 : sint.nat (i + W64 1) - sint.nat idx = (sint.nat i - sint.nat idx) + 1 := by
            word
          rw [hm1, List.take_add_one, hLy]
          simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
          iframe
          ipureintro
          refine ⟨⟨by word, by word⟩, ?_, ?_⟩
          · intro k z hk hz
            by_cases hkm : k < sint.nat i - sint.nat idx
            · exact Hbelow k z hkm hz
            · have : k = sint.nat i - sint.nat idx := by omega
              subst this
              rw [hLy] at hz; cases hz
              simpa using hylt
          · have := Hksl.1; word
        · -- not below `endKey`: the loop breaks
          have hyn : decide (strLt y.1 eb) = false := by simpa using Hif
          wp_for_post
          ihave Hbb := Hbb $$ Hbuf Hused
          ihave Hout := range_finish (GF := GF) (es.drop (sint.nat idx)) eb _ (sint.Z limit).toNat
            ks vs kl vl Hbelow Hlim (Or.inr (Or.inl ⟨y, hLy, hyn⟩)) $$ [Hks Hksc Hvs Hvsc Hka Hva]
          · iframe
          iapply HΦ
          iunfold bbAt
          iframe # ∗
      · -- `limit` results
        ihave Hbb := Hbb $$ Hbuf Hused
        ihave Hout := range_finish (GF := GF) (es.drop (sint.nat idx)) eb _ (sint.Z limit).toNat
          ks vs kl vl Hbelow Hlim (Or.inr (Or.inr (by have := Hksl.1; word))) $$ [Hks Hksc Hvs Hvsc Hka Hva]
        · iframe
        iapply HΦ
        iunfold bbAt
        iframe # ∗
    · -- the end of the buffer
      cleanup_bool_decide
      try wp_auto
      ihave Hbb := Hbb $$ Hbuf Hused
      ihave Hout := range_finish (GF := GF) (es.drop (sint.nat idx)) eb _ (sint.Z limit).toNat
        ks vs kl vl Hbelow Hlim (Or.inl (by rw [List.length_drop]; word)) $$ [Hks Hksc Hvs Hvsc Hka Hva]
      · iframe
      iapply HΦ
      iunfold bbAt
      iframe # ∗
  -- the entry at `idx` is not below `endKey`
  have hnlt : ¬ strLt e.1 eb := by simpa using Hif
  ihave Hbb := Hbb $$ Hbuf Hused
  ihave Hout := kvsOut_nil_r (GF := GF)
  iapply HΦ
  iunfold bbAt
  rw [List.takeWhile_cons, _root_.decide_eq_false hnlt]
  simp only [Bool.false_eq_true, ite_false, List.take_nil]
  iframe # ∗


end proof

end EtcdGrove
end Perennial
