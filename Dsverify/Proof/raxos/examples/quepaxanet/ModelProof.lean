/-
`Model()` (`model.go`) meets the store's porcupine model spec `qS` (`Model.lean`): the helpers on
read-only slices of strings (`push`, `has`, `cat`, `erase`; the first three as paxos's
`ModelProof.lean`), the state's `lookup`, `set`, `stepE`, `step`, `equal`, and the pure
`stepL_pSeq`.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.Model

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace raxos.examples.quepaxanet

open EtcdGrove.linkv raxos.pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

theorem wp_push (p : GoSlice) (P : List GoString) (v : GoString) (hP : P.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! raxos.examples.quepaxanet.push)) (Val #p)) (Val #v))
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
      (App (App (Val (@! raxos.examples.quepaxanet.has)) (Val #p)) (Val #v))
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
      (App (App (Val (@! raxos.examples.quepaxanet.erase)) (Val #p)) (Val #v))
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

theorem wp_cat (p q : GoSlice) (P Q : List GoString) (hl : P.length + Q.length < 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P ∗ q ↦*□ Q }}
      (App (App (Val (@! raxos.examples.quepaxanet.cat)) (Val #p)) (Val #q))
    {{ (r : GoSlice), RET #r; r ↦* (P ++ Q) }} := by
  wp_start as ⟨#Hp, #Hq⟩
  ihave %Hlp := ownSlice_len _ _ _ $$ Hp
  ihave %Hlq := ownSlice_len _ _ _ $$ Hq
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) $$ [] as %r ⟨Hr, Hcap⟩
  · ipureintro; word
  have hn : sint.nat (p.len + q.len) = P.length + Q.length := by
    rw [Hlp.1, Hlq.1]; word
  rw [hn]
  wp_apply wp_slice_copy $$ [$Hr $Hp] as %n ⟨-, Hr, -⟩
  rw [List.length_replicate, List.take_of_length_le (by omega), List.drop_replicate,
    show P.length + Q.length - P.length = Q.length by omega]
  ihave %Hrl := ownSlice_len _ _ _ $$ Hr
  ihave %Hrw := ownSlice_wf _ _ _ $$ Hr
  simp only [List.length_append, List.length_replicate] at Hrl
  rw [ite_eq_left (show 0 ≤ sint.Z p.len ∧ sint.Z p.len ≤ sint.Z r.len ∧
    sint.Z r.len ≤ sint.Z r.cap by refine ⟨Hlp.2, ?_, Hrw.2⟩; have := Hrl.1; word)]
  wp_auto
  icases (ownSlice_split_all p.len r _ _ ⟨Hlp.2, by have := Hrl.1; word⟩).1 $$ Hr with ⟨Hr1, Hr2⟩
  have hp : sint.nat p.len = P.length := Hlp.1.symm
  rw [hp, List.take_left, List.drop_left]
  wp_apply wp_slice_copy $$ [$Hr2 $Hq] as %m ⟨-, Hr2, -⟩
  rw [List.length_replicate, List.take_of_length_le (by omega), List.drop_of_length_le (by simp)]
  iapply HΦ
  iapply (ownSlice_split_all p.len r _ (P ++ Q) ⟨Hlp.2, by have := Hrl.1; word⟩).2
  rw [hp, List.take_left, List.drop_left, List.append_nil]
  iframe

theorem entry_K_disc (l : Loc) (v : Entry) :
    (l ↦□ v : IProp GF) ⊢ l.[Entry, go!"K"] ↦□ v.K' := by
  iintro #H
  icases (AccessStrict.access_strict (A := l.[Entry, go!"K"] ↦□ v.K')
      (A' := l.[Entry, go!"K"] ↦□ v.K') (P := l ↦□ v)) $$ H with ⟨H1, -⟩
  iexact H1

theorem findIdx_lk_found (E : List KEnt) (k : GoString) (n : Nat) (hn : n < E.length)
    (hk : E[n].1 = k) (hpre : ∀ p ∈ E.take n, p.1 ≠ k) :
    E.findIdx (fun p => decide (p.1 = k)) = n ∧ lk E k = E[n].2 := by
  induction E generalizing n with
  | nil => simp at hn
  | cons q E ih =>
    cases n with
    | zero =>
      simp only [List.getElem_cons_zero] at hk
      simp [List.findIdx_cons, hk, lk_cons]
    | succ n =>
      simp only [List.take_succ_cons, List.mem_cons, forall_eq_or_imp] at hpre
      simp only [List.getElem_cons_succ] at hk
      obtain ⟨h1, h2⟩ := ih n (by simp at hn; omega) hk hpre.2
      simp [List.findIdx_cons, hpre.1, lk_cons, h1, h2]

theorem findIdx_lk_none (E : List KEnt) (k : GoString) (hpre : ∀ p ∈ E, p.1 ≠ k) :
    E.findIdx (fun p => decide (p.1 = k)) = E.length ∧ lk E k = Ent.empty := by
  induction E with
  | nil => exact ⟨rfl, rfl⟩
  | cons q E ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hpre
    obtain ⟨h1, h2⟩ := ih hpre.2
    simp [List.findIdx_cons, hpre.1, lk_cons, h1, h2]

theorem wp_lookup (sl : State) (es : List Entry) (E : List KEnt) (k : GoString) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*□ es ∗ □ ([∗list] e;p ∈ es;E, entRep e p) }}
      (App (App (Val (@! raxos.examples.quepaxanet.lookup')) (Val #sl)) (Val #k))
    {{ (i : w64) (e : Entry), RET (PairV #i #e);
        ⌜sint.nat i = E.findIdx (fun p => decide (p.1 = k)) ∧ 0 ≤ sint.Z i⌝ ∗
        entRep e (k, lk E k) }} := by
  wp_start as ⟨#Hs, #HE⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  ihave %HlE := BigSepL2.bigSepL2_length $$ HE
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len ∧ ∀ p ∈ E.take (sint.nat i), p.1 ≠ k⌝ :
      IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, by rw [h0]; simp⟩
  wp_for HI
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z sl.len := Hif
    list_elem es (sint.nat i) as e
    list_elem E (sint.nat i) as p
    ihave #Hep := BigSepL2.bigSepL2_lookup He_lookup Hp_lookup $$ HE
    ihave #He := ownSlice_elem_acc (sint.Z i) e sl _ es Hi.1 He_lookup $$ Hs
    rw [ite_eq_left ⟨Hi.1, hlt⟩]
    icases He with ⟨#He, -⟩
    iunfold entRep at Hep
    icases Hep with ⟨%Hk, #Hold, #Hnew⟩
    have hiE : sint.nat i < E.length := by rw [← HlE, Hl.1]; word
    have hp : E[sint.nat i] = p := by
      rw [List.getElem?_eq_some_iff] at Hp_lookup; exact Hp_lookup.2
    ihave #HeK := entry_K_disc _ e $$ He
    wp_auto
    wp_if_destruct
    · rw [ite_eq_left ⟨Hi.1, hlt⟩]
      wp_auto
      wp_for_post
      obtain ⟨h1, h2⟩ := findIdx_lk_found E e.K' (sint.nat i) hiE (by rw [hp, Hk.1]) Hi.2.2
      iapply HΦ
      isplitr
      · ipureintro; exact ⟨h1.symm, Hi.1⟩
      iunfold entRep
      rw [h2, hp]
      iframe Hold Hnew
      ipureintro; exact ⟨rfl, Hk.2⟩
    · wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      refine ⟨by word, by word, ?_⟩
      rw [hs, List.take_add_one, Hp_lookup]
      simp only [Option.toList_some, List.mem_append, List.mem_singleton]
      rintro q (hq | rfl)
      · exact Hi.2.2 q hq
      · rw [← Hk.1]; exact Hif
  · have heq : sint.Z i = sint.Z sl.len := by omega
    have hn : sint.nat i = E.length := by
      rw [← HlE, Hl.1]; show (sint.Z i).toNat = _; rw [heq]
    obtain ⟨h1, h2⟩ := findIdx_lk_none E k (by have := Hi.2.2; rwa [hn, List.take_length] at this)
    iapply HΦ
    isplitr
    · ipureintro; refine ⟨?_, by omega⟩; rw [h1, ← hn]; show (sint.Z sl.len).toNat = (sint.Z i).toNat; rw [heq]
    iunfold entRep
    rw [h2]
    dsimp only [Ent.empty]
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    isplitl
    · iapply ownSlice_nil
    · iapply ownSlice_nil

end proof
