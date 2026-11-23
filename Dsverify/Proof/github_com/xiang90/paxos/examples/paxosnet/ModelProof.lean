/-
`Model()` (kit.go) meets the register's porcupine model spec `woS` (notes/dsv-paxos.md): the
state's helpers `push`, `has`, `erase`, `equal` and `step` over read-only slices of strings, and the
pure `stepG_pSeq` (`ModelSet.lean`).
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.ModelSet

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.xiang90.paxos.examples.paxosnet

open EtcdGrove EtcdGrove.linkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.xiang90.paxos.examples.paxosnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.xiang90.paxos.examples.paxosnet

set_option goose.wp.extras true

theorem wp_push (p : GoSlice) (P : List GoString) (v : GoString) (hP : P.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.push)) (Val #p)) (Val #v))
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
      (App (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.has)) (Val #p)) (Val #v))
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
      (App (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.erase)) (Val #p)) (Val #v))
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

theorem wp_equal (a b : State) (A B : List GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ a.Pend' ↦*□ A ∗ b.Pend' ↦*□ B }}
      (App (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.equal)) (Val #a)) (Val #b))
    {{ (r : Bool), RET #r; ⌜r = true → a.Known' = b.Known' ∧ a.Val' = b.Val' ∧ A = B⌝ }} := by
  wp_start as ⟨#Ha, #Hb⟩
  ihave %HA := ownSlice_len _ _ _ $$ Ha
  ihave %HB := ownSlice_len _ _ _ $$ Hb
  wp_auto
  by_cases h1 : ¬ a.Known' = b.Known'
  · simp only [h1, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ
    ipureintro; intro h; cases h
  have h1 := Classical.not_not.mp h1
  simp only [h1, decide_true, Bool.not_true]
  wp_auto
  by_cases h2 : ¬ a.Val' = b.Val'
  · simp only [h2, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ
    ipureintro; intro h; cases h
  have h2 := Classical.not_not.mp h2
  simp only [h2, decide_true, Bool.not_true]
  wp_auto
  by_cases h3 : ¬ a.Pend'.len = b.Pend'.len
  · simp only [h3, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ
    ipureintro; intro h; cases h
  have h3 := Classical.not_not.mp h3
  simp only [h3, decide_true, Bool.not_true]
  wp_auto
  have hAB : A.length = B.length := by rw [HA.1, HB.1, h3]
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.Pend'.len ∧
        A.take (sint.nat i) = B.take (sint.nat i)⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, by rw [h0]; simp⟩
  wp_for HI
  obtain ⟨Hi0, Hil, Ht⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z a.Pend'.len := Hif
    list_elem A (sint.nat i) as x
    list_elem B (sint.nat i) as y
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.Pend'.len from ⟨Hi0, hlt⟩)]
    wp_apply wp_load_slice_index a.Pend' (sint.Z i) A _ x Hi0 $$ [Ha] as -
    · iframe Ha; ipureintro; exact Hx_lookup
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.Pend'.len from ⟨Hi0, h3 ▸ hlt⟩)]
    wp_apply wp_load_slice_index b.Pend' (sint.Z i) B _ y Hi0 $$ [Hb] as -
    · iframe Hb; ipureintro; exact Hy_lookup
    by_cases hxy : ¬ x = y
    · simp only [hxy, decide_false, Bool.not_false]
      wp_auto
      wp_for_post
      iapply HΦ
      ipureintro; intro h; cases h
    have hxy := Classical.not_not.mp hxy
    subst hxy
    simp only [decide_true, Bool.not_true]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1
    iframe
    ipureintro
    have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    refine ⟨by word, by word, ?_⟩
    rw [hs, List.take_add_one, List.take_add_one, Ht, Hx_lookup, Hy_lookup]
  · have heq : sint.Z i = sint.Z a.Pend'.len := by omega
    have hn : sint.nat i = A.length := by
      rw [HA.1]; show (sint.Z i).toNat = _; rw [heq]
    have e : A = B := by
      rw [hn, List.take_length, hAB, List.take_length] at Ht
      exact Ht
    iapply HΦ
    ipureintro; intro _; exact ⟨trivial, trivial, e⟩

theorem map_val_erase (pend : List BStr) (w : BStr) :
    (pend.map Subtype.val).erase w.1 = (pend.erase w).map Subtype.val := by
  induction pend with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = w
    · subst h; simp
    · have h' : x.1 ≠ w.1 := fun e => h (Subtype.ext e)
      simp only [List.map_cons, List.erase_cons, beq_iff_eq, h, h', ↓reduceIte, ih]

theorem mem_map_val (pend : List BStr) (w : BStr) : w.1 ∈ pend.map Subtype.val ↔ w ∈ pend := by
  constructor
  · intro h
    obtain ⟨x, hx, e⟩ := List.mem_map.1 h
    rwa [← Subtype.ext e]
  · intro h; exact List.mem_map_of_mem h

theorem wp_stepGo (kn : Bool) (val : GoString) (sl : GoSlice) (pend : List BStr)
    (hp : pend.length < 2 ^ 60) (i : BStr) (u : Bool) (w : BStr) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*□ pend.map Subtype.val }}
      (App (App (App (Val (@! github_com.xiang90.paxos.examples.paxosnet.step))
        (Val #(State.mk kn val sl))) (Val #i.1)) (Val #(Out.mk u w.1)))
    {{ (ok : Bool) (s' : State), RET (PairV #ok #s'); ∃ (sl' : GoSlice),
        ⌜ok = (stepG kn val pend i u w).1 ∧
          s' = State.mk (stepG kn val pend i u w).2.1 (stepG kn val pend i u w).2.2.1 sl'⌝ ∗
        sl' ↦*□ (stepG kn val pend i u w).2.2.2.map Subtype.val }} := by
  wp_start as #Hsl
  wp_auto
  have hpm : (pend.map Subtype.val).length < 2 ^ 60 := by simpa using hp
  cases u
  · simp only
    wp_auto
    cases kn
    · wp_auto
      by_cases h1 : ¬ w.1 = i.1
      · simp only [h1, _root_.decide_false]
        wp_auto
        wp_apply wp_has sl (pend.map Subtype.val) w.1 $$ [$Hsl]
        by_cases h2 : w ∈ pend
        · rw [decide_eq_true ((mem_map_val pend w).2 h2)]
          wp_auto
          wp_apply +noauto wp_erase sl (pend.map Subtype.val) w.1 $$ [$Hsl] as %q Hq
          iapply fupd_wp
          imod ownSlice_persist _ _ _ $$ Hq with #Hq
          imodintro
          wp_auto
          iapply HΦ
          iexists q
          rw [map_val_erase] at *
          simp only [stepG, h1, h2, Bool.false_eq_true, ↓reduceIte]
          iframe Hq
          ipureintro; simp
        · rw [decide_eq_false (fun h => h2 ((mem_map_val pend w).1 h))]
          wp_auto
          iapply HΦ
          iexists sl
          simp only [stepG, h1, h2, Bool.false_eq_true, ↓reduceIte]
          iframe Hsl
          ipureintro; simp
      · have h1 := Classical.not_not.mp h1
        simp only [h1, _root_.decide_true]
        wp_auto
        iapply HΦ
        iexists sl
        simp only [stepG, h1, Bool.false_eq_true, ↓reduceIte]
        iframe Hsl
        ipureintro; simp
    · wp_auto
      by_cases h1 : ¬ w.1 = val
      · simp only [h1, _root_.decide_false]
        wp_auto
        iapply HΦ
        iexists sl
        simp only [stepG, h1, Bool.false_eq_true, ↓reduceIte]
        iframe Hsl
        ipureintro; simp
      · have h1 := Classical.not_not.mp h1
        simp only [h1, _root_.decide_true]
        wp_auto
        iapply HΦ
        iexists sl
        simp only [stepG, h1, Bool.false_eq_true, ↓reduceIte]
        iframe Hsl
        ipureintro; simp
  · simp only
    wp_auto
    wp_apply +noauto wp_push sl (pend.map Subtype.val) i.1 hpm $$ [$Hsl] as %q Hq
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hq with #Hq
    imodintro
    wp_auto
    iapply HΦ
    iexists q
    simp only [stepG, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
    iframe Hq
    ipureintro; simp

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
    simp only [woS, woRep]
    iexists false, [], slice.nil, []
    isplitr
    · ipureintro
      exact ⟨rfl, woSet_init.symm, by simp, by decide⟩
    · rw [List.map_nil]; iapply ownSlice_nil
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %k %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [woS, woS0]
    icases Hpre with ⟨%Hk, Hrep, %Hio⟩
    obtain ⟨⟨x, rfl⟩, u, w, rfl⟩ := Hio
    unfold woRep
    icases Hrep with ⟨%kn, %val, %sl, %pend, %Hr, #Hsl⟩
    obtain ⟨rfl, rfl, hlen, hv⟩ := Hr
    wp_auto
    wp_apply wp_stepGo kn val sl pend (by omega) x u w $$ [$Hsl]
      as %ok %s' ⟨%sl', %Hst, #Hsl'⟩
    obtain ⟨rfl, rfl⟩ := Hst
    have H := stepG_pSeq kn val hv pend x u w
    have hpm := linkv.pM_step woB woDec (woSet kn val pend) _ x _ (woDec_box x u w)
    obtain ⟨hb1, hb2⟩ := stepG_bounds kn val hv pend x u w
    iapply HΦ'
    isplitr
    · iexists kn, val, sl, pend
      iframe Hsl
      ipureintro; exact ⟨rfl, rfl, hlen, hv⟩
    isplitr
    · ipureintro
      rw [hpm, H]
      cases (stepG kn val pend x u w).1 <;> rfl
    · unfold stepPost
      simp only [hpm, H]
      cases hok : (stepG kn val pend x u w).1
      · simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      · simp only [↓reduceIte]
        iexists (stepG kn val pend x u w).2.1, (stepG kn val pend x u w).2.2.1, sl',
          (stepG kn val pend x u w).2.2.2
        iframe Hsl'
        ipureintro
        exact ⟨rfl, rfl, by omega, hb1⟩
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal
    unfold equalSpec
    iintro %k %j %v %w %s %t
    iintro !> %Φ' Hpre HΦ'
    simp only [woS]
    unfold woRep
    icases Hpre with ⟨⟨%kn, %val, %sl, %pend, %Hr, #Hsl⟩, ⟨%kn', %val', %sl', %pend', %Hr', #Hsl'⟩⟩
    obtain ⟨rfl, rfl, hlen, hv⟩ := Hr
    obtain ⟨rfl, rfl, hlen', hv'⟩ := Hr'
    wp_auto
    wp_apply wp_equal ⟨kn, val, sl⟩ ⟨kn', val', sl'⟩ _ _ $$ [$Hsl $Hsl'] as %r %Hr
    iapply HΦ'
    isplitr
    · iexists kn, val, sl, pend
      iframe Hsl
      ipureintro; exact ⟨rfl, rfl, hlen, hv⟩
    isplitr
    · iexists kn', val', sl', pend'
      iframe Hsl'
      ipureintro; exact ⟨rfl, rfl, hlen', hv'⟩
    ipureintro
    intro h
    obtain ⟨e1, e2, e3⟩ := Hr h
    simp only at e1 e2
    have e4 : pend = pend' := List.map_inj_right (fun a b h => Subtype.ext h) |>.1 e3
    rw [e1, e2, e4]
  ileft
  ipureintro; trivial

end proof

end github_com.xiang90.paxos.examples.paxosnet
end Perennial
