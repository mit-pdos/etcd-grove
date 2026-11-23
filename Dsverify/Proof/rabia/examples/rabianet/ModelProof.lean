/-
`Model()` (kit.go) meets the store's porcupine model spec `kvS` (notes/dsv-rabia.md; as paxos's
`ModelProof.lean`): the state's helpers `push`, `has`, `cat`, `erase`, `equalStrs`, `find`, `set`,
`equal` and `step` over read-only slices, and the pure `stepG_pSeq` (`ModelSet.lean`); the
decoder's laws and `PendDec` (porcupine's model is the pending-writes model of `kvR γ`).
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.ModelLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace rabia.examples.rabianet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote Perennial.rabia
  Perennial.rabia.model

/-! ## The state's helpers -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : rabia.examples.rabianet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.rabia.examples.rabianet

set_option goose.wp.extras true

theorem wp_push (p : GoSlice) (P : List GoString) (v : GoString) (hP : P.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! rabia.examples.rabianet.push)) (Val #p)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* (P ++ [v]) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) $$ [] as %q ⟨Hq, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [$Hq $Hp] as %n ⟨-, Hq, -⟩
  have hn : sint.nat (p.len + W64 1) = P.length + 1 := by rw [Hl.1]; word
  rw [hn, List.take_of_length_le (by simp), List.drop_replicate,
    show P.length + 1 - P.length = 1 by omega, List.replicate_one]
  ihave %Hql := ownSlice_len _ _ _ $$ Hq
  have hb : 0 ≤ sint.Z p.len ∧ sint.Z p.len < sint.Z q.len := by
    have := Hql.1; simp only [List.length_append, List.length_singleton] at this; word
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index q (sint.Z p.len) _ v $$ [Hq] as Hq
  · iframe Hq; ipureintro; simp only [List.length_append, List.length_singleton]; word
  rw [show (sint.Z p.len).toNat = P.length by rw [Hl.1],
    List.set_append_right _ _ (by omega), Nat.sub_self, List.set_cons_zero]
  wp_auto
  iapply HΦ
  iexact Hq

theorem wp_has (p : GoSlice) (P : List GoString) (v : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! rabia.examples.rabianet.has)) (Val #p)) (Val #v))
    {{ RET #(decide (v ∈ P)); True }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ v ∉ P.take (sint.nat i)⌝ : IProp GF)
      $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, ?_⟩
    rw [h0]; simp
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := Hif
    list_elem P (sint.nat i) as x
    rw [ite_eq_left ⟨Hi.1, hlt⟩]
    wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi.1 $$ [Hp] as -
    · iframe Hp; ipureintro; exact Hx_lookup
    wp_if_destruct
    · wp_for_post
      have : v ∈ P := Hif ▸ List.mem_of_getElem? Hx_lookup
      rw [show decide (v ∈ P) = true from decide_eq_true this]
      iapply HΦ
      itrivial
    · wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hs, List.take_add_one, Hx_lookup]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hi.2.2, fun h => Hif h.symm⟩
  · have heq : sint.Z i = sint.Z p.len := by omega
    have hv : v ∉ P := by
      have := Hi.2.2
      rwa [show sint.nat i = P.length by rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq],
        List.take_length] at this
    rw [show decide (v ∈ P) = false from decide_eq_false hv]
    iapply HΦ
    itrivial

theorem erase_take_succ (P : List GoString) (v x : GoString) (n : Nat) (hx : P[n]? = some x)
    (f : Bool) (hf : f = false → v ∉ P.take n) (hf2 : f = true → v ∈ P.take n) :
    (if (!f && decide (x = v)) then P.take n else
      (if f then (P.take n).erase v else P.take n) ++ [x]) =
    (if (f || decide (x = v)) then (P.take (n + 1)).erase v else P.take (n + 1)) := by
  rw [List.take_add_one, hx, Option.toList_some]
  cases f
  · have hv := hf rfl
    by_cases h : x = v
    · subst h
      simp [List.erase_append_right _ hv]
    · have hv' : v ∉ P.take n ++ [x] := by simp [hv, Ne.symm h]
      simp [h]
  · have hv := hf2 rfl
    simp [List.erase_append_left _ hv]

theorem wp_erase (p : GoSlice) (P : List GoString) (v : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! rabia.examples.rabianet.erase)) (Val #p)) (Val #v))
    {{ (q : GoSlice), RET #q; q ↦* P.erase v }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) p.len (by word)) as %q0 ⟨Hq, Hcap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (i : w64) (f : Bool) (q : GoSlice), "i" ∷ i_ptr ↦ i ∗ "found" ∷ found_ptr ↦ f ∗
      "q" ∷ q_ptr ↦ q ∗
      "Hq" ∷ q ↦* (if f then (P.take (sint.nat i)).erase v else P.take (sint.nat i)) ∗
      "Hcap" ∷ ownSliceCap GoString q (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z p.len ∧ (f = false → v ∉ P.take (sint.nat i)) ∧
        (f = true → v ∈ P.take (sint.nat i))⌝ : IProp GF) $$ [i found q Hq Hcap]
  · iexists W64 0, false, q0
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0]
    simp only [Bool.false_eq_true, ↓reduceIte, List.take_zero]
    iframe
    ipureintro
    refine ⟨by word, by word, fun _ => by simp, fun h => by cases h⟩
  wp_for HI
  obtain ⟨Hi0, Hil, hf1, hf2⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z p.len := Hif
    list_elem P (sint.nat i) as x
    have e := erase_take_succ P v x (sint.nat i) Hx_lookup f hf1 hf2
    have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    cases f
    · wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
      wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
      · iframe Hp; ipureintro; exact Hx_lookup
      by_cases hxv : x = v
      · subst hxv
        simp only [Bool.not_false, decide_true, Bool.and_self, ↓reduceIte, Bool.or_true] at e
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, true, q
        rw [hs, ← e]
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro
        refine ⟨by word, by word, ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
        rw [List.take_add_one, Hx_lookup]; simp
      · simp only [Bool.not_false, hxv, decide_false, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, Bool.or_false] at e
        rw [decide_eq_false hxv]
        wp_auto
        rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
        wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
        · iframe Hp; ipureintro; exact Hx_lookup
        wp_apply wp_slice_literal (V := GoString) [x]
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        wp_auto
        wp_apply wp_slice_append (V := GoString) $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
        wp_for_post
        iframe
        iexists i + W64 1, false, q'
        rw [hs, ← e]
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro
        refine ⟨by word, by word, ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
        exact ⟨hf1 rfl, Ne.symm hxv⟩
    · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        Bool.true_or] at e
      wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.len from ⟨Hi0, hlt⟩)]
      wp_apply wp_load_slice_index p (sint.Z i) P _ x Hi0 $$ [Hp] as -
      · iframe Hp; ipureintro; exact Hx_lookup
      wp_apply wp_slice_literal (V := GoString) [x]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append (V := GoString) $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
      wp_for_post
      iframe
      iexists i + W64 1, true, q'
      rw [hs, ← e]
      simp only [↓reduceIte]
      iframe
      ipureintro
      refine ⟨by word, by word, ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
      rw [List.take_add_one, Hx_lookup]
      simp [hf2 rfl]
  · have heq : sint.Z i = sint.Z p.len := by omega
    have hn : sint.nat i = P.length := by
      rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq]
    rw [hn, List.take_length]
    iapply HΦ
    cases f
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hv : v ∉ P := by
        have := hf1 rfl
        rwa [show sint.nat i = P.length by rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq],
          List.take_length] at this
      rw [List.erase_of_not_mem hv]
      iexact Hq
    · simp only [↓reduceIte]
      iexact Hq

/-! ### Entries -/

theorem ents_nil : ⊢ entsRep (GF := GF) [] [] := by
  unfold entsRep
  isplitr
  · ipureintro; simp
  · simp only [List.zip_nil_left]
    iapply BigSepL.bigSepL_nil.2
    itrivial

theorem ents_len {evs : List Entry} {es : List EntV} :
    entsRep (GF := GF) evs es ⊢ ⌜evs.length = es.length⌝ := by
  unfold entsRep
  iintro ⟨%h, -⟩
  ipureintro
  have := congrArg List.length h.1
  simpa using this

/-- An entry of `evs` holds the entry of `es` at its index. -/
theorem ents_lookup {evs : List Entry} {es : List EntV} {i : Nat} {ev : Entry}
    (h : evs[i]? = some ev) :
    entsRep (GF := GF) evs es ⊢ ∃ e, ⌜es[i]? = some e⌝ ∗ entRep ev e := by
  unfold entsRep
  iintro ⟨%hm, #Hl⟩
  have hl : evs.length = es.length := by simpa using congrArg List.length hm.1
  have hi : i < es.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 h).1
  obtain ⟨e, he⟩ : ∃ e, es[i]? = some e := ⟨es[i], List.getElem?_eq_getElem hi⟩
  have hk : ev.K' = e.k := by
    have := congrArg (fun l => l[i]?) hm.1
    simp only [List.getElem?_map, h, he, Option.map_some, Option.some.injEq] at this
    exact this
  have hc : ev.Cur' = e.cur := by
    have := congrArg (fun l => l[i]?) hm.2
    simp only [List.getElem?_map, h, he, Option.map_some, Option.some.injEq] at this
    exact this
  have hz : (evs.zip es)[i]? = some (ev, e) := List.getElem?_zip_eq_some.2 ⟨h, he⟩
  ihave ⟨#Ho, #Hp⟩ := (BigSepL.bigSepL_lookup (Φ := fun _ p => iprop(p.1.Old' ↦*□ p.2.old ∗
    p.1.Pend' ↦*□ p.2.new)) hz) $$ Hl
  iexists e
  isplitr
  · ipureintro; exact he
  unfold entRep
  iframe Ho Hp
  ipureintro; exact ⟨hk, hc⟩

theorem ents_snoc (evs : List Entry) (es : List EntV) (eve : Entry) (e : EntV) :
    entsRep (GF := GF) evs es ∗ entRep eve e ⊢ entsRep (evs ++ [eve]) (es ++ [e]) := by
  iintro ⟨Hs, He⟩
  ihave %hl := ents_len $$ Hs
  unfold entsRep entRep
  icases Hs with ⟨%hm, #Hl⟩
  icases He with ⟨%he, #Ho, #Hp⟩
  isplitr
  · ipureintro
    simp [hm.1, hm.2, he.1, he.2]
  rw [List.zip_append hl]
  iapply BigSepL.bigSepL_append.2
  iframe Hl
  simp only [List.zip_cons_cons, List.zip_nil_left]
  iapply BigSepL.bigSepL_singleton.2
  iframe Ho Hp

/-- Every entry of `e`'s key replaced by `e` (kit.go's `set`'s loop). -/
theorem ents_map (evs : List Entry) (es : List EntV) (eve : Entry) (e : EntV) :
    entsRep (GF := GF) evs es ∗ entRep eve e ⊢
      entsRep (evs.map fun x => if x.K' = eve.K' then eve else x)
        (es.map fun x => if x.k = e.k then e else x) := by
  induction evs generalizing es with
  | nil =>
    iintro ⟨Hs, -⟩
    ihave %hl := ents_len $$ Hs
    rw [List.length_nil] at hl
    rw [List.eq_nil_of_length_eq_zero hl.symm]
    simp only [List.map_nil]
    iapply ents_nil
  | cons ev evs ih =>
    cases es with
    | nil =>
      iintro ⟨Hs, -⟩
      ihave %hl := ents_len $$ Hs
      simp at hl
    | cons x xs =>
      iintro ⟨Hs, #He⟩
      ihave Hs' := Hs
      iunfold entsRep at Hs'
      icases Hs' with ⟨%hm, #Hl⟩
      rw [List.zip_cons_cons] at *
      ihave ⟨⟨#Ho, #Hp⟩, #Hrest⟩ := (BigSepL.bigSepL_cons).1 $$ Hl
      simp only [List.map_cons, List.cons.injEq] at hm
      ihave #Ht := ih xs $$ [He]
      · isplitr
        · unfold entsRep; isplitr
          · ipureintro; exact ⟨hm.1.2, hm.2.2⟩
          · iexact Hrest
        · iexact He
      unfold entRep
      icases He with ⟨%hk, #Ho', #Hp'⟩
      unfold entsRep
      icases Ht with ⟨%hm', #Hl'⟩
      have hkx : (ev.K' = eve.K') ↔ (x.k = e.k) := by rw [hm.1.1, hk.1]
      isplitr
      · ipureintro
        simp only [List.map_cons, List.cons.injEq]
        refine ⟨⟨?_, hm'.1⟩, ⟨?_, hm'.2⟩⟩
        · by_cases h : x.k = e.k
          · simp [h, hkx.2 h, hk.1]
          · have h' : ¬ ev.K' = eve.K' := fun h2 => h (hkx.1 h2)
            simp only [h, h', ↓reduceIte]; exact hm.1.1
        · by_cases h : x.k = e.k
          · simp [h, hkx.2 h, hk.2]
          · have h' : ¬ ev.K' = eve.K' := fun h2 => h (hkx.1 h2)
            simp only [h, h', ↓reduceIte]; exact hm.2.1
      simp only [List.map_cons, List.zip_cons_cons]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · by_cases h : x.k = e.k
        · simp only [h, ↓reduceIte, hkx.2 h]; iframe Ho' Hp'
        · have h' : ¬ ev.K' = eve.K' := fun h2 => h (hkx.1 h2)
          simp only [h, h', ↓reduceIte]; iframe Ho Hp
      · iexact Hl'

/-- kit.go's `set`'s result: `setE`'s entries. -/
theorem ents_set (evs : List Entry) (es : List EntV) (eve : Entry) (e : EntV) :
    entsRep (GF := GF) evs es ∗ entRep eve e ⊢
      entsRep (if evs.any (fun x => decide (x.K' = eve.K')) then
          evs.map (fun x => if x.K' = eve.K' then eve else x) else evs ++ [eve])
        (setE es e) := by
  iintro ⟨#Hs, #He⟩
  ihave #Hs' := Hs
  iunfold entsRep at Hs'
  icases Hs' with ⟨%hm, -⟩
  ihave #He' := He
  iunfold entRep at He'
  icases He' with ⟨%hk, -⟩
  have hany : evs.any (fun x => decide (x.K' = eve.K')) = es.any (fun x => decide (x.k = e.k)) := by
    have : evs.any (fun x => decide (x.K' = eve.K')) = (evs.map (·.K')).any (fun x => decide (x = eve.K')) := by
      simp [List.any_map, Function.comp_def]
    rw [this, hm.1, hk.1]; simp [List.any_map, Function.comp_def]
  unfold setE
  rw [hany]
  split
  · iapply ents_map; iframe Hs He
  · iapply ents_snoc; iframe Hs He

/-! ### `cat`, `equalStrs` -/

theorem wp_cat (a b : GoSlice) (A B : List GoString) (hl : A.length + B.length < 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ a ↦*□ A ∗ b ↦*□ B }}
      (App (App (Val (@! rabia.examples.rabianet.cat)) (Val #a)) (Val #b))
    {{ (q : GoSlice), RET #q; q ↦* (A ++ B) }} := by
  wp_start as ⟨#Ha, #Hb⟩
  ihave %HA := ownSlice_len _ _ _ $$ Ha
  ihave %HB := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) $$ [] as %q ⟨Hq, -⟩
  · ipureintro; word
  have hN : sint.nat (a.len + b.len) = A.length + B.length := by rw [HA.1, HB.1]; word
  rw [hN]
  wp_apply wp_slice_copy $$ [$Hq $Ha] as %n ⟨-, Hq, -⟩
  rw [List.length_replicate, List.take_of_length_le (by omega), List.drop_replicate,
    show A.length + B.length - A.length = B.length by omega]
  ihave %Hql := ownSlice_len _ _ _ $$ Hq
  ihave %Hqw := ownSlice_wf _ _ _ $$ Hq
  have hb : 0 ≤ sint.Z a.len ∧ sint.Z a.len ≤ sint.Z q.len := by
    have := Hql.1; simp only [List.length_append, List.length_replicate] at this; constructor <;> word
  rw [ite_eq_left ⟨hb.1, hb.2, Hqw.2⟩]
  icases (ownSlice_split_all a.len q _ _ hb).1 $$ Hq with ⟨Hq1, Hq2⟩
  have hA : sint.nat a.len = A.length := HA.1.symm
  rw [hA, List.take_left, List.drop_left]
  wp_auto
  wp_apply wp_slice_copy $$ [$Hq2 $Hb] as %m ⟨-, Hq2, -⟩
  rw [List.length_replicate, List.take_of_length_le (by omega), List.drop_of_length_le (by simp),
    List.append_nil]
  ihave Hq := (ownSlice_split_all a.len q (DFrac.own 1) (A ++ B) hb).2 $$ [Hq1 Hq2]
  · rw [hA, List.take_left, List.drop_left]; iframe Hq1 Hq2
  iapply HΦ
  iexact Hq

theorem wp_equalStrs (a b : GoSlice) (A B : List GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ a ↦*□ A ∗ b ↦*□ B }}
      (App (App (Val (@! rabia.examples.rabianet.equalStrs)) (Val #a)) (Val #b))
    {{ RET #(decide (A = B)); True }} := by
  wp_start as ⟨#Ha, #Hb⟩
  ihave %HA := ownSlice_len _ _ _ $$ Ha
  ihave %HB := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_if_destruct
  rotate_left
  · have hne : A ≠ B := fun h => Hif (by
      have := congrArg List.length h; rw [HA.1, HB.1] at this; word)
    rw [decide_eq_false hne]
    iapply HΦ; itrivial
  have h3 : a.len = b.len := Hif
  have hAB : A.length = B.length := by rw [HA.1, HB.1, h3]
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.len ∧
        A.take (sint.nat i) = B.take (sint.nat i)⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, by rw [h0]; simp⟩
  wp_for HI
  obtain ⟨Hi0, Hil, Ht⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z a.len := Hif
    list_elem A (sint.nat i) as x
    list_elem B (sint.nat i) as y
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.len from ⟨Hi0, hlt⟩)]
    wp_apply wp_load_slice_index a (sint.Z i) A _ x Hi0 $$ [Ha] as -
    · iframe Ha; ipureintro; exact Hx_lookup
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len from ⟨Hi0, h3 ▸ hlt⟩)]
    wp_apply wp_load_slice_index b (sint.Z i) B _ y Hi0 $$ [Hb] as -
    · iframe Hb; ipureintro; exact Hy_lookup
    wp_if_destruct
    rotate_left
    · have hne : A ≠ B := by
        intro h
        rw [h, Hy_lookup] at Hx_lookup
        exact Hif (Option.some.inj Hx_lookup).symm
      rw [decide_eq_false hne]
      wp_for_post
      iapply HΦ; itrivial
    · wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      refine ⟨by word, by word, ?_⟩
      rw [hs, List.take_add_one, List.take_add_one, Ht, Hx_lookup, Hy_lookup, Hif]
  · have heq : sint.Z i = sint.Z a.len := by omega
    have hn : sint.nat i = A.length := by
      rw [HA.1]; show (sint.Z i).toNat = _; rw [heq]
    have e : A = B := by
      rw [hn, List.take_length, hAB, List.take_length] at Ht
      exact Ht
    rw [decide_eq_true e]
    iapply HΦ; itrivial

/-! ### `find` -/

/-- An entry's fields, read-only. -/
theorem entry_fields (l : Loc) (v : Entry) :
    (l ↦□ v : IProp GF) ⊢ l.[Entry, go!"K"] ↦□ v.K' ∗ l.[Entry, go!"Cur"] ↦□ v.Cur' ∗
      l.[Entry, go!"Old"] ↦□ v.Old' ∗ l.[Entry, go!"Pend"] ↦□ v.Pend' := by
  iintro #H
  icases (AccessStrict.access_strict (A := l.[Entry, go!"K"] ↦□ v.K')
      (A' := l.[Entry, go!"K"] ↦□ v.K') (P := l ↦□ v)) $$ H with ⟨H1, -⟩
  icases (AccessStrict.access_strict (A := l.[Entry, go!"Cur"] ↦□ v.Cur')
      (A' := l.[Entry, go!"Cur"] ↦□ v.Cur') (P := l ↦□ v)) $$ H with ⟨H2, -⟩
  icases (AccessStrict.access_strict (A := l.[Entry, go!"Old"] ↦□ v.Old')
      (A' := l.[Entry, go!"Old"] ↦□ v.Old') (P := l ↦□ v)) $$ H with ⟨H3, -⟩
  icases (AccessStrict.access_strict (A := l.[Entry, go!"Pend"] ↦□ v.Pend')
      (A' := l.[Entry, go!"Pend"] ↦□ v.Pend') (P := l ↦□ v)) $$ H with ⟨H4, -⟩
  iframe H1 H2 H3 H4

theorem findE_hit (es : List EntV) (k : GoString) (n : Nat) (e : EntV) (he : es[n]? = some e)
    (hk : e.k = k) (hpre : k ∉ (es.map (·.k)).take n) : findE es k = e := by
  induction es generalizing n with
  | nil => simp at he
  | cons x xs ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      simp [findE, List.find?_cons, hk]
    | succ n =>
      simp only [List.getElem?_cons_succ] at he
      simp only [List.map_cons, List.take_succ_cons, List.mem_cons, not_or] at hpre
      have := ih n he hpre.2
      unfold findE at this ⊢
      rw [List.find?_cons, decide_eq_false (Ne.symm hpre.1)]
      exact this

theorem findE_miss (es : List EntV) (k : GoString) (h : k ∉ es.map (·.k)) :
    findE es k = ⟨k, [], [], []⟩ := by
  unfold findE
  rw [List.find?_eq_none.2]
  · rfl
  · intro x hx
    simp only [decide_eq_true_eq]
    intro hxk
    exact h (List.mem_map.2 ⟨x, hx, hxk⟩)

theorem wp_find (sl : GoSlice) (evs : List Entry) (es : List EntV) (k : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*□ evs ∗ entsRep evs es }}
      (App (App (Val (@! rabia.examples.rabianet.find)) (Val #(State.mk sl))) (Val #k))
    {{ (ev : Entry), RET #ev; entRep ev (findE es k) }} := by
  wp_start as ⟨#Hsl, #Hs⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  ihave #Hs' := Hs
  iunfold entsRep at Hs'
  icases Hs' with ⟨%hm, -⟩
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len ∧
        k ∉ (evs.map (·.K')).take (sint.nat i)⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, by rw [h0]; simp⟩
  wp_for HI
  obtain ⟨Hi0, Hil, Hnk⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z sl.len := Hif
    list_elem evs (sint.nat i) as ev
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi0, hlt⟩
    ihave Hev := (ownSlice_elem_acc (sint.Z i) ev sl DFrac.discard evs Hi0 Hev_lookup) $$ Hsl
    icases Hev with ⟨#Hev, -⟩
    ihave ⟨#HK, -⟩ := entry_fields _ ev $$ Hev
    rw [ite_eq_left hb]
    wp_auto
    have hn : sint.nat i < evs.length := by rw [Hl.1]; word
    wp_if_destruct
    · rw [ite_eq_left hb]
      wp_apply wp_load_slice_index sl (sint.Z i) evs _ ev Hi0 $$ [Hsl] as -
      · iframe Hsl; ipureintro; exact Hev_lookup
      iapply wp_for_post_return
      wp_auto
      ihave ⟨%e, %he, #He⟩ := ents_lookup Hev_lookup $$ Hs
      ihave #He' := He
      iunfold entRep at He'
      icases He' with ⟨%hk, -⟩
      have hfe : findE es ev.K' = e := by
        refine findE_hit es ev.K' (sint.nat i) e he hk.1.symm ?_
        rw [← hm.1]; exact Hnk
      rw [hfe]
      iapply HΦ
      iexact He
    · wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      refine ⟨by word, by word, ?_⟩
      rw [hs, List.take_add_one, List.getElem?_map, Hev_lookup]
      simp only [Option.map_some, Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hnk, fun h => Hif h.symm⟩
  · have heq : sint.Z i = sint.Z sl.len := by omega
    have hn : sint.nat i = evs.length := by
      rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq]
    rw [hn, List.take_of_length_le (by simp), hm.1] at Hnk
    rw [findE_miss es k Hnk]
    iapply HΦ
    unfold entRep
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitl
    · iapply ownSlice_nil
    · iapply ownSlice_nil

/-! ### `set` -/

theorem map_set_none (evs : List Entry) (eve : Entry)
    (hf : evs.any (fun x => decide (x.K' = eve.K')) = false) :
    evs.map (fun x => if x.K' = eve.K' then eve else x) = evs := by
  induction evs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
    simp only [List.map_cons, hf.1, ↓reduceIte, ih hf.2]

theorem wp_set (sl : GoSlice) (evs : List Entry) (es : List EntV) (eve : Entry) (e : EntV)
    (hlen : evs.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*□ evs ∗ entsRep evs es ∗ entRep eve e }}
      (App (App (Val (@! rabia.examples.rabianet.set)) (Val #(State.mk sl))) (Val #eve))
    {{ (sl' : GoSlice), RET #(State.mk sl');
        sl' ↦* (if evs.any (fun x => decide (x.K' = eve.K')) then
          evs.map (fun x => if x.K' = eve.K' then eve else x) else evs ++ [eve]) ∗
        entsRep (if evs.any (fun x => decide (x.K' = eve.K')) then
          evs.map (fun x => if x.K' = eve.K' then eve else x) else evs ++ [eve]) (setE es e) }} := by
  wp_start as ⟨#Hsl, #Hs, #He⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  ihave #Hset := ents_set evs es eve e $$ [Hs He]
  · iframe Hs He
  wp_auto
  wp_apply (wp_slice_make3 (V := Entry) (W64 0) (sl.len + W64 1) (by word)) as %q0 ⟨Hq, Hcap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (i : w64) (f : Bool) (q : GoSlice), "i" ∷ i_ptr ↦ i ∗ "found" ∷ found_ptr ↦ f ∗
      "es" ∷ es_ptr ↦ q ∗
      "Hq" ∷ q ↦* (evs.take (sint.nat i)).map (fun x => if x.K' = eve.K' then eve else x) ∗
      "Hcap" ∷ ownSliceCap Entry q (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len ∧
        f = (evs.take (sint.nat i)).any (fun x => decide (x.K' = eve.K'))⌝ : IProp GF)
      $$ [i found es Hq Hcap]
  · iexists W64 0, false, q0
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0]
    simp only [List.take_zero, List.map_nil, List.any_nil]
    iframe
    ipureintro
    refine ⟨by word, by word, by simp⟩
  wp_for HI
  obtain ⟨Hi0, Hil, hf⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z sl.len := Hif
    list_elem evs (sint.nat i) as ev
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi0, hlt⟩
    have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    ihave Hev := (ownSlice_elem_acc (sint.Z i) ev sl DFrac.discard evs Hi0 Hev_lookup) $$ Hsl
    icases Hev with ⟨#Hev, -⟩
    ihave ⟨#HK, -⟩ := entry_fields _ ev $$ Hev
    rw [ite_eq_left hb]
    wp_auto
    have htake : evs.take (sint.nat i + 1) = evs.take (sint.nat i) ++ [ev] := by
      rw [List.take_add_one, Hev_lookup]; rfl
    by_cases hk : ev.K' = eve.K'
    · rw [decide_eq_true hk]
      wp_auto
      wp_apply wp_slice_literal (V := Entry) [eve]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply wp_slice_append (V := Entry) $$ [$Hq $Hcap $Hsl1] as %q' ⟨Hq', Hcap', -⟩
      wp_for_post
      iframe
      iexists i + W64 1, true, q'
      rw [hs, htake]
      simp only [List.map_append, List.map_cons, List.map_nil, hk, ↓reduceIte]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      simp [hk]
    · rw [decide_eq_false hk]
      wp_auto
      rw [ite_eq_left hb]
      wp_apply wp_load_slice_index sl (sint.Z i) evs _ ev Hi0 $$ [Hsl] as -
      · iframe Hsl; ipureintro; exact Hev_lookup
      wp_apply wp_slice_literal (V := Entry) [ev]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply wp_slice_append (V := Entry) $$ [$Hq $Hcap $Hsl1] as %q' ⟨Hq', Hcap', -⟩
      wp_for_post
      iframe
      iexists i + W64 1, f, q'
      rw [hs, htake]
      simp only [List.map_append, List.map_cons, List.map_nil, hk, ↓reduceIte]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      simp [hf, hk]
  · have heq : sint.Z i = sint.Z sl.len := by omega
    have hn : sint.nat i = evs.length := by
      rw [Hl.1]; show (sint.Z i).toNat = _; rw [heq]
    rw [hn, List.take_length] at hf
    rw [hn, List.take_length]
    cases f
    · wp_auto
      wp_apply wp_slice_literal (V := Entry) [eve]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply wp_slice_append (V := Entry) $$ [$Hq $Hcap $Hsl1] as %q' ⟨Hq2, Hcap', -⟩
      iapply HΦ
      rw [← hf]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [map_set_none evs eve hf.symm]
      iframe Hq2
      iexact Hset
    · wp_auto
      iapply HΦ
      rw [← hf]
      simp only [↓reduceIte]
      iframe Hq
      iexact Hset

/-! ### `step` -/

/-- The `Out` of an answer (`ansV`'s, unboxed). -/
def ansOut : linkv.Ans KOut → Out
  | .ok o => outVal o.1
  | .err => Out.mk true false false []

theorem ansV_ansOut (a : linkv.Ans KOut) : ansV a = interface.mkOk Out.ty #(ansOut a) := by
  cases a <;> rfl

theorem outVal_put (o : KOut) : (outVal o.1).Put' = decide (o.1 = .done) := by
  rcases o with ⟨o, _⟩
  cases o with
  | done => rfl
  | got w => cases w <;> rfl

theorem findE_k (es : List EntV) (k : GoString) : (findE es k).k = k := by
  unfold findE
  rcases h : es.find? (fun e => decide (e.k = k)) with _ | e
  · rw [h]; rfl
  · have := List.find?_some h
    rw [h]; simpa using this

theorem pSeq_ne {S T : linkv.PSet KSt KIn} {i : KIn} {a : linkv.Ans KOut}
    (h : (linkv.pSeq kvB).step S (i, a) = some T) : ∃ c, T c := by
  simp only [linkv.pSeq] at h
  split at h
  · rename_i hc; cases h; exact hc
  · cases h

theorem wp_step (sl : GoSlice) (evs : List Entry) (es : List EntV) (n : Nat) (hn : n < 2 ^ 60)
    (hEB : EB n es) (i : KIn) (a : linkv.Ans KOut) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*□ evs ∗ entsRep evs es }}
      (App (App (App (Val (@! rabia.examples.rabianet.step)) (Val #(State.mk sl)))
        (Val #(inVal i.1))) (Val #(ansOut a)))
    {{ (ok : Bool) (s' : State), RET (PairV #ok #s'); ∃ (sl' : GoSlice) (evs' : List Entry),
        ⌜ok = (stepG es i a).1 ∧ s' = State.mk sl'⌝ ∗ sl' ↦*□ evs' ∗
        entsRep evs' (stepG es i a).2 }} := by
  wp_start as ⟨#Hsl, #Hs⟩
  ihave %Hel := ents_len $$ Hs
  have hlen : evs.length < 2 ^ 60 := by have := hEB.1; omega
  have hk := EB_findE hEB
  rcases hi : i.1 with k | ⟨k, v⟩
  · cases a with
    | err =>
      simp only [inVal, ansOut]
      wp_auto
      wp_apply wp_find sl evs es k $$ [$Hsl $Hs] as %ev #Hev
      iapply HΦ
      iexists sl, evs
      simp only [stepG, hi]
      iframe Hsl Hs
      ipureintro; simp
    | ok o =>
      rcases o with ⟨o, ho⟩
      cases o with
      | done =>
        simp only [inVal, ansOut, outVal]
        wp_auto
        wp_apply wp_find sl evs es k $$ [$Hsl $Hs] as %ev #Hev
        iapply HΦ
        iexists sl, evs
        simp only [stepG, hi]
        iframe Hsl Hs
        ipureintro; simp
      | got w =>
        simp only [inVal, ansOut]
        wp_auto
        wp_apply wp_find sl evs es k $$ [$Hsl $Hs] as %ev #Hev
        ihave #Hev' := Hev
        iunfold entRep at Hev'
        icases Hev' with ⟨%hev, #Hold, #Hpend⟩
        cases w with
        | none =>
          simp only [outVal]
          wp_auto
          by_cases hc : ([] : GoString) = (findE es k).cur
          · rw [hev.2, decide_eq_true hc]
            wp_auto
            iapply HΦ
            iexists sl, evs
            simp only [stepG, hi, Option.getD_none, hc, ↓reduceIte]
            iframe Hsl Hs
            ipureintro; simp
          · rw [hev.2, decide_eq_false hc]
            wp_auto
            wp_apply +noauto wp_cat ev.Old' ev.Pend' (findE es k).old (findE es k).new
              (by have := hk k; omega) $$ [$Hold $Hpend] as %q Hq
            wp_auto
            iapply HΦ
            iexists sl, evs
            simp only [stepG, hi, Option.getD_none, hc, ↓reduceIte, ne_eq, not_true_eq_false,
              false_and]
            iframe Hsl Hs
            ipureintro; simp
        | some x =>
          simp only [outVal]
          have hx : x ≠ [] := ho.1
          wp_auto
          by_cases hc : x = (findE es k).cur
          · rw [hev.2, decide_eq_true hc]
            wp_auto
            iapply HΦ
            iexists sl, evs
            simp only [stepG, hi, Option.getD_some, hc, ↓reduceIte]
            iframe Hsl Hs
            ipureintro; simp
          · rw [hev.2, decide_eq_false hc]
            wp_auto
            wp_apply +noauto wp_cat ev.Old' ev.Pend' (findE es k).old (findE es k).new
              (by have := hk k; omega) $$ [$Hold $Hpend] as %q Hq
            iapply fupd_wp
            imod ownSlice_persist _ _ _ $$ Hq with #Hq
            imodintro
            wp_auto
            rw [decide_eq_false hx]
            wp_auto
            wp_apply wp_has q ((findE es k).old ++ (findE es k).new) x $$ [$Hq]
            by_cases hm : x ∈ (findE es k).old ++ (findE es k).new
            · rw [decide_eq_true hm]
              wp_auto
              wp_apply +noauto wp_erase q ((findE es k).old ++ (findE es k).new) x $$ [$Hq]
                as %q2 Hq2
              iapply fupd_wp
              imod ownSlice_persist _ _ _ $$ Hq2 with #Hq2
              imodintro
              wp_auto
              wp_apply +noauto wp_set sl evs es (Entry.mk k x q2 slice.nil)
                ⟨k, x, ((findE es k).old ++ (findE es k).new).erase x, []⟩ hlen $$ [$Hsl $Hs]
                as %sl' ⟨Hsl', #Hs'⟩
              · unfold entRep
                iframe Hq2
                isplitr
                · ipureintro; exact ⟨rfl, rfl⟩
                iapply ownSlice_nil
              iapply fupd_wp
              imod ownSlice_persist _ _ _ $$ Hsl' with #Hsl'
              imodintro
              wp_auto
              iapply HΦ
              iexists sl', _
              simp only [stepG, hi, Option.getD_some, hc, ↓reduceIte, ne_eq, hx, not_false_eq_true,
                hm, and_self]
              iframe Hsl' Hs'
            · rw [decide_eq_false hm]
              wp_auto
              iapply HΦ
              iexists sl, evs
              simp only [stepG, hi, Option.getD_some, hc, ↓reduceIte, ne_eq, hx, not_false_eq_true,
                hm, _root_.and_false]
              iframe Hsl Hs
              ipureintro; simp
  · cases a with
    | err =>
      simp only [inVal, ansOut]
      wp_auto
      wp_apply wp_find sl evs es k $$ [$Hsl $Hs] as %ev #Hev
      ihave #Hev' := Hev
      iunfold entRep at Hev'
      icases Hev' with ⟨%hev, #Hold, #Hpend⟩
      wp_apply +noauto wp_push ev.Pend' (findE es k).new v (by have := hk k; omega) $$ [$Hpend]
        as %q Hq
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hq with #Hq
      imodintro
      wp_auto
      wp_apply +noauto wp_set sl evs es (Entry.mk k ev.Cur' ev.Old' q)
        ⟨k, (findE es k).cur, (findE es k).old, (findE es k).new ++ [v]⟩ hlen $$ [$Hsl $Hs]
        as %sl' ⟨Hsl', #Hs'⟩
      · unfold entRep
        iframe Hold Hq
        ipureintro; exact ⟨rfl, hev.2⟩
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hsl' with #Hsl'
      imodintro
      wp_auto
      iapply HΦ
      iexists sl', _
      simp only [stepG, hi]
      iframe Hsl' Hs'
      ipureintro; simp
    | ok o =>
      simp only [inVal, ansOut]
      wp_auto
      wp_apply wp_find sl evs es k $$ [$Hsl $Hs] as %ev #Hev
      ihave #Hev' := Hev
      iunfold entRep at Hev'
      icases Hev' with ⟨%hev, #Hold, #Hpend⟩
      rw [outVal_unknown o]
      wp_auto
      wp_apply +noauto wp_cat ev.Old' ev.Pend' (findE es k).old (findE es k).new
        (by have := hk k; omega) $$ [$Hold $Hpend] as %q Hq
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hq with #Hq
      imodintro
      wp_auto
      wp_apply +noauto wp_set sl evs es (Entry.mk k v q slice.nil)
        ⟨k, v, (findE es k).old ++ (findE es k).new, []⟩ hlen $$ [$Hsl $Hs]
        as %sl' ⟨Hsl', #Hs'⟩
      · unfold entRep
        iframe Hq
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        iapply ownSlice_nil
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hsl' with #Hsl'
      imodintro
      wp_auto
      iapply HΦ
      iexists sl', _
      simp only [stepG, hi, outVal_put o]
      iframe Hsl' Hs'
      ipureintro; simp

/-! ### `equal` -/

theorem wp_equal (sa sb : GoSlice) (evs fvs : List Entry) (es fs : List EntV) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sa ↦*□ evs ∗ entsRep evs es ∗ sb ↦*□ fvs ∗
        entsRep fvs fs }}
      (App (App (Val (@! rabia.examples.rabianet.equal)) (Val #(State.mk sa)))
        (Val #(State.mk sb)))
    {{ (r : Bool), RET #r; ⌜r = true → es = fs⌝ }} := by
  wp_start as ⟨#Ha, #Hea, #Hb, #Heb⟩
  ihave %HA := ownSlice_len _ _ _ $$ Ha
  ihave %HB := ownSlice_len _ _ _ $$ Hb
  ihave %hla := ents_len $$ Hea
  ihave %hlb := ents_len $$ Heb
  wp_auto
  wp_if_destruct
  rotate_left
  · have hne : es ≠ fs := fun h => Hif (by
      have := congrArg List.length h; rw [← hla, ← hlb, HA.1, HB.1] at this; word)
    iapply HΦ; ipureintro; intro h; cases h
  have h3 : sa.len = sb.len := Hif
  have hAB : evs.length = fvs.length := by rw [HA.1, HB.1, h3]
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sa.len ∧
        es.take (sint.nat i) = fs.take (sint.nat i)⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, by rw [h0]; simp⟩
  wp_for HI
  obtain ⟨Hi0, Hil, Ht⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z sa.len := Hif
    list_elem evs (sint.nat i) as ev
    list_elem fvs (sint.nat i) as fv
    have hba : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sa.len := ⟨Hi0, hlt⟩
    have hbb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sb.len := ⟨Hi0, h3 ▸ hlt⟩
    ihave Hev := (ownSlice_elem_acc (sint.Z i) ev sa DFrac.discard evs Hi0 Hev_lookup) $$ Ha
    icases Hev with ⟨#Hev, -⟩
    ihave ⟨#HK, #HC, #HO, #HP⟩ := entry_fields _ ev $$ Hev
    ihave Hfv := (ownSlice_elem_acc (sint.Z i) fv sb DFrac.discard fvs Hi0 Hfv_lookup) $$ Hb
    icases Hfv with ⟨#Hfv, -⟩
    ihave ⟨#HK', #HC', #HO', #HP'⟩ := entry_fields _ fv $$ Hfv
    ihave ⟨%e, %he, #He⟩ := ents_lookup Hev_lookup $$ Hea
    ihave ⟨%f, %hf, #Hf⟩ := ents_lookup Hfv_lookup $$ Heb
    unfold entRep
    icases He with ⟨%hke, #Hoe, #Hpe⟩
    icases Hf with ⟨%hkf, #Hof, #Hpf⟩
    rw [ite_eq_left hba]
    wp_auto
    rw [ite_eq_left hbb]
    wp_auto
    by_cases h1 : ev.K' = fv.K'
    rotate_left
    · rw [decide_eq_false h1]
      wp_auto
      wp_for_post
      iapply HΦ; ipureintro; intro h; cases h
    rw [decide_eq_true h1]
    wp_auto
    rw [ite_eq_left hba]
    wp_auto
    rw [ite_eq_left hbb]
    wp_auto
    by_cases h2 : ev.Cur' = fv.Cur'
    rotate_left
    · rw [decide_eq_false h2]
      wp_auto
      wp_for_post
      iapply HΦ; ipureintro; intro h; cases h
    rw [decide_eq_true h2]
    wp_auto
    rw [ite_eq_left hba]
    wp_auto
    rw [ite_eq_left hbb]
    wp_auto
    wp_apply wp_equalStrs ev.Old' fv.Old' e.old f.old $$ [$Hoe $Hof]
    by_cases h4 : e.old = f.old
    rotate_left
    · rw [decide_eq_false h4]
      wp_auto
      wp_for_post
      iapply HΦ; ipureintro; intro h; cases h
    rw [decide_eq_true h4]
    wp_auto
    rw [ite_eq_left hba]
    wp_auto
    rw [ite_eq_left hbb]
    wp_auto
    wp_apply wp_equalStrs ev.Pend' fv.Pend' e.new f.new $$ [$Hpe $Hpf]
    by_cases h5 : e.new = f.new
    rotate_left
    · rw [decide_eq_false h5]
      wp_auto
      wp_for_post
      iapply HΦ; ipureintro; intro h; cases h
    rw [decide_eq_true h5]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1
    iframe
    ipureintro
    have hef : e = f := by
      cases e; cases f
      simp only at hke hkf h4 h5
      rw [← hke.1, ← hkf.1, ← hke.2, ← hkf.2, h1, h2, h4, h5]
    have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    refine ⟨by word, by word, ?_⟩
    rw [hs, List.take_add_one, List.take_add_one, Ht, he, hf, hef]
  · have heq : sint.Z i = sint.Z sa.len := by omega
    have hn : sint.nat i = es.length := by
      rw [← hla, HA.1]; show (sint.Z i).toNat = _; rw [heq]
    have e : es = fs := by
      rw [hn, List.take_length, show es.length = fs.length by rw [← hla, ← hlb, hAB],
        List.take_length] at Ht
      exact Ht
    iapply HΦ
    ipureintro; intro _; exact e

/-! ### `Model()` -/

theorem Model.wp_proof : Model.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold isModel isEqHash
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · -- Init
    unfold initSpec
    iintro !> %Φ' _ HΦ'
    wp_auto
    iapply HΦ'
    simp only [kvS, kvRep]
    iexists slice.nil, [], []
    isplitr
    · ipureintro
      exact ⟨rfl, kvSet_init.symm, WF_nil, EB_nil, kvSet_init_ne⟩
    isplitl
    · iapply ownSlice_nil
    · iapply ents_nil
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %k %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [kvS, kvS0]
    icases Hpre with ⟨%Hk, Hrep, %Hio⟩
    obtain ⟨⟨x, rfl⟩, a, rfl⟩ := Hio
    unfold kvRep
    icases Hrep with ⟨%esl, %es, %evs, %Hr, #Hsl, #Hs⟩
    obtain ⟨rfl, rfl, hwf, hEB, hne⟩ := Hr
    have hpm := linkv.pM_step kvB kvDec (kvSet es) _ x a (kvDec_box x a)
    have H := stepG_pSeq es hwf hne x a
    rw [ansV_ansOut] at hpm ⊢
    wp_auto
    wp_apply wp_step esl evs es k Hk hEB x a $$ [$Hsl $Hs]
      as %ok %s' ⟨%sl', %evs', %Hst, #Hsl', #Hs'⟩
    obtain ⟨rfl, rfl⟩ := Hst
    iapply HΦ'
    isplitr
    · iexists esl, es, evs
      iframe Hsl Hs
      ipureintro; exact ⟨rfl, rfl, hwf, hEB, hne⟩
    isplitr
    · ipureintro
      rw [hpm, H]
      cases (stepG es x a).1 <;> rfl
    · unfold stepPost
      simp only [hpm, H]
      cases hok : (stepG es x a).1
      · simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      · simp only [↓reduceIte]
        have hs := H
        rw [hok, if_pos rfl] at hs
        iexists sl', (stepG es x a).2, evs'
        iframe Hsl' Hs'
        ipureintro
        exact ⟨rfl, rfl, WF_stepG hwf x a, EB_stepG hEB x a, pSeq_ne hs⟩
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal
    unfold equalSpec
    iintro %k %j %v %w %s %t
    iintro !> %Φ' Hpre HΦ'
    simp only [kvS]
    unfold kvRep
    icases Hpre with ⟨⟨%esl, %es, %evs, %Hr, #Hsl, #Hs⟩, ⟨%fsl, %fs, %fvs, %Hr', #Hfsl, #Hfs⟩⟩
    obtain ⟨rfl, rfl, hwf, hEB, hne⟩ := Hr
    obtain ⟨rfl, rfl, hwf', hEB', hne'⟩ := Hr'
    wp_auto
    wp_apply wp_equal esl fsl evs fvs es fs $$ [$Hsl $Hs $Hfsl $Hfs] as %r %Hr
    iapply HΦ'
    isplitr
    · iexists esl, es, evs
      iframe Hsl Hs
      ipureintro; exact ⟨rfl, rfl, hwf, hEB, hne⟩
    isplitr
    · iexists fsl, fs, fvs
      iframe Hfsl Hfs
      ipureintro; exact ⟨rfl, rfl, hwf', hEB', hne'⟩
    ipureintro
    intro h
    rw [Hr h]
  ileft
  ipureintro; trivial

end proof

end rabia.examples.rabianet
end Perennial
