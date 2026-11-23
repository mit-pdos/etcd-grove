/-
`Model()` (kit.go) meets the register's porcupine model spec `casS` (notes/dsv-gryff.md): the
state's helpers `apply`, `isWrite`, `without`, `with`, `sameCfg`, `hasCfg`, `reach`, `step`,
`equal` over read-only slices, and the pure `stepG_pSeq` (`ModelSet.lean`).
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.ModelSet
public import Dsverify.Proof.gryff.examples.gryffnet.Base
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace gryff.examples.gryffnet

open EtcdGrove EtcdGrove.linkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : gryff.examples.gryffnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.gryff.examples.gryffnet

set_option goose.wp.extras true

/-- `wp_alloc` does not take `#(zero_val w64)` at `go.int64` (the zero value `GoZeroVal go.int64`
steps to): rewritten to `W64 0` inside `wp_auto` (its extra simp set). -/
@[local goose_wp_simp_extra] theorem zero_val_w64 : (zero_val w64 : w64) = W64 0 := rfl

attribute [local goose_wp_simp_extra] OpRead OpWrite OpCAS

@[local goose_wp_simp_extra] theorem zero_val_bool : (zero_val Bool : Bool) = false := rfl

/-- `Out{}`. -/
@[local goose_wp_simp_extra] theorem zero_val_Out : (zero_val Out : Out) = outDone := rfl

theorem wp_isWrite (i : In) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! gryff.examples.gryffnet.isWrite)) (Val #i))
    {{ RET #(isWriteG i); True }} := by
  wp_start as #Hk
  wp_auto
  unfold isWriteG
  by_cases h1 : i.Op' = W64 1
  · simp only [h1, _root_.decide_true, Bool.true_or]
    wp_auto
    iapply HΦ; itrivial
  · simp only [h1, _root_.decide_false, Bool.false_or]
    wp_auto
    iapply HΦ; itrivial

theorem wp_apply (v : w64) (i : In) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (App (Val (@! gryff.examples.gryffnet.apply)) (Val #v)) (Val #i))
    {{ RET (PairV #(applyG v i).1 #(applyG v i).2); True }} := by
  wp_start as #Hk
  wp_auto
  unfold applyG
  by_cases h1 : i.Op' = W64 1
  · simp only [h1, _root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial
  · simp only [h1, _root_.decide_false, ↓reduceIte]
    wp_auto
    by_cases h2 : i.Op' = W64 2
    · simp only [h2, _root_.decide_true, ↓reduceIte]
      wp_auto
      by_cases h3 : v = i.A'
      · simp only [h3, _root_.decide_true, ↓reduceIte]
        wp_auto
        iapply HΦ; itrivial
      · simp only [h3, _root_.decide_false, ↓reduceIte]
        wp_auto
        iapply HΦ; itrivial
    · simp only [h2, _root_.decide_false, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial

theorem wp_sameCfg (a b : Cfg) (A B : List In) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ a.Pend' ↦*□ A ∗ b.Pend' ↦*□ B }}
      (App (App (Val (@! gryff.examples.gryffnet.sameCfg)) (Val #a)) (Val #b))
    {{ RET #(decide (a.V' = b.V' ∧ A = B)); True }} := by
  wp_start as ⟨#Ha, #Hb⟩
  ihave %HA := ownSlice_len _ _ _ $$ Ha
  ihave %HB := ownSlice_len _ _ _ $$ Hb
  wp_auto
  by_cases h1 : ¬ a.V' = b.V'
  · simp only [h1, _root_.decide_false, Bool.not_false]
    wp_auto
    simp only [false_and, _root_.decide_false]
    iapply HΦ; itrivial
  have h1 := Classical.not_not.mp h1
  simp only [h1, _root_.decide_true, Bool.not_true]
  wp_auto
  by_cases h3 : ¬ a.Pend'.len = b.Pend'.len
  · simp only [h3, _root_.decide_false, Bool.not_false]
    wp_auto
    have : ¬ A = B := fun e => h3 (by
      have := HA.1; have := HB.1; subst e; word)
    simp only [true_and, decide_eq_false this]
    iapply HΦ; itrivial
  have h3 := Classical.not_not.mp h3
  simp only [h3, _root_.decide_true, Bool.not_true]
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
    have hne : x ≠ y → ¬ A = B := fun hxy e => hxy (by
      subst e; rw [Hx_lookup] at Hy_lookup; exact Option.some.inj Hy_lookup)
    by_cases hxy : x = y
    · subst hxy
      simp only [_root_.decide_true]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      refine ⟨by word, by word, ?_⟩
      rw [hs, List.take_add_one, List.take_add_one, Ht, Hx_lookup, Hy_lookup]
    · have hAB' := hne hxy
      by_cases e1 : x.Op' = y.Op'
      · simp only [e1, _root_.decide_true]
        wp_auto
        by_cases e2 : x.A' = y.A'
        · simp only [e2, _root_.decide_true]
          wp_auto
          have e3 : ¬ x.B' = y.B' := fun e3 => hxy (by
            cases x; cases y; simp only at e1 e2 e3; subst e1 e2 e3; rfl)
          simp only [e3, _root_.decide_false]
          wp_auto
          wp_for_post
          simp only [true_and, decide_eq_false hAB']
          iapply HΦ; itrivial
        · simp only [e2, _root_.decide_false]
          wp_auto
          wp_for_post
          simp only [true_and, decide_eq_false hAB']
          iapply HΦ; itrivial
      · simp only [e1, _root_.decide_false]
        wp_auto
        wp_for_post
        simp only [true_and, decide_eq_false hAB']
        iapply HΦ; itrivial
  · have heq : sint.Z i = sint.Z a.Pend'.len := by omega
    have hn : sint.nat i = A.length := by
      rw [HA.1]; show (sint.Z i).toNat = _; rw [heq]
    have e : A = B := by
      rw [hn, List.take_length, hAB, List.take_length] at Ht
      exact Ht
    simp only [true_and, decide_eq_true e]
    iapply HΦ; itrivial

theorem eraseIdx_take_succ {α : Type} (P : List α) (n k : Nat) (x : α) (hx : P[n]? = some x) :
    (P.take (n + 1)).eraseIdx k =
      if n = k then (P.take n).eraseIdx k else (P.take n).eraseIdx k ++ [x] := by
  have hn : n < P.length := (List.getElem?_eq_some_iff.1 hx).1
  have hl : (P.take n).length = n := by simp; omega
  rw [List.take_add_one, hx, Option.toList_some]
  split
  · subst k
    rw [List.eraseIdx_append_of_length_le (by omega), hl, Nat.sub_self]
    simp only [List.eraseIdx_cons_zero, List.append_nil]
    exact (List.eraseIdx_of_length_le (by omega)).symm
  · rename_i hne
    by_cases hk : k < n
    · rw [List.eraseIdx_append_of_lt_length (by omega)]
    · rw [List.eraseIdx_of_length_le (by simp; omega), List.eraseIdx_of_length_le (by omega)]

theorem wp_without (p : GoSlice) (P : List In) (i : w64) (hi : 0 ≤ sint.Z i) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! gryff.examples.gryffnet.without)) (Val #p)) (Val #i))
    {{ (q : GoSlice), RET #q; q ↦* P.eraseIdx (sint.nat i) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply (wp_slice_make3 (V := In) (W64 0) p.len (by word)) as %q0 ⟨Hq, Hcap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (j : w64) (q : GoSlice), "j" ∷ j_ptr ↦ j ∗ "q" ∷ q_ptr ↦ q ∗
      "Hq" ∷ q ↦* (P.take (sint.nat j)).eraseIdx (sint.nat i) ∗
      "Hcap" ∷ ownSliceCap In q (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z p.len⌝ : IProp GF) $$ [j q Hq Hcap]
  · iexists W64 0, q0
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0]
    simp only [List.take_zero, List.eraseIdx_nil]
    iframe
    ipureintro
    refine ⟨by word, by word⟩
  wp_for HI
  obtain ⟨Hj0, Hjl⟩ := Hj
  wp_if_destruct
  · have hlt : sint.Z j < sint.Z p.len := Hif
    list_elem P (sint.nat j) as x
    have e := eraseIdx_take_succ P (sint.nat j) (sint.nat i) x Hx_lookup
    have hs : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    by_cases hji : j = i
    · subst hji
      simp only [_root_.decide_true]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, q
      rw [hs, e, ite_eq_left rfl]
      iframe
      ipureintro
      refine ⟨by word, by word⟩
    · have hji' : sint.nat j ≠ sint.nat i := fun h => hji (by word)
      simp only [hji, _root_.decide_false]
      wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z p.len from ⟨Hj0, hlt⟩)]
      wp_apply wp_load_slice_index p (sint.Z j) P _ x Hj0 $$ [Hp] as -
      · iframe Hp; ipureintro; exact Hx_lookup
      wp_apply wp_slice_literal (V := In) [x]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append (V := In) $$ [$Hq $Hcap $Hsl] as %q' ⟨Hq', Hcap', -⟩
      wp_for_post
      iframe
      iexists j + W64 1, q'
      rw [hs, e, if_neg hji']
      iframe
      ipureintro
      refine ⟨by word, by word⟩
  · have heq : sint.Z j = sint.Z p.len := by omega
    have hn : sint.nat j = P.length := by
      rw [Hl.1]; show (sint.Z j).toNat = _; rw [heq]
    rw [hn, List.take_length]
    iapply HΦ
    iexact Hq

theorem wp_with (p : GoSlice) (P : List In) (x : In) (hP : P.length < 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ p ↦*□ P }}
      (App (App (Val (@! gryff.examples.gryffnet.«with»)) (Val #p)) (Val #x))
    {{ (q : GoSlice), RET #q; q ↦* (P ++ [x]) }} := by
  wp_start as #Hp
  ihave %Hl := ownSlice_len _ _ _ $$ Hp
  wp_auto
  wp_apply wp_slice_make2 (V := In) $$ [] as %q ⟨Hq, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [$Hq $Hp] as %n ⟨-, Hq, -⟩
  have hn : sint.nat (p.len + W64 1) = P.length + 1 := by rw [Hl.1]; word
  rw [hn, List.take_of_length_le (by simp), List.drop_replicate,
    show P.length + 1 - P.length = 1 by omega, List.replicate_one]
  ihave %Hql := ownSlice_len _ _ _ $$ Hq
  have hb : 0 ≤ sint.Z p.len ∧ sint.Z p.len < sint.Z q.len := by
    have := Hql.1; simp only [List.length_append, List.length_singleton] at this; word
  rw [ite_eq_left hb]
  wp_apply wp_store_slice_index q (sint.Z p.len) _ x $$ [Hq] as Hq
  · iframe Hq; ipureintro; simp only [List.length_append, List.length_singleton]; word
  rw [show (sint.Z p.len).toNat = P.length by rw [Hl.1],
    List.set_append_right _ _ (by omega), Nat.sub_self, List.set_cons_zero]
  wp_auto
  iapply HΦ
  iexact Hq

/-! ## The model's configurations in Go -/

theorem gcfg_eq (x y : GCfg) : x = y ↔ x.st = y.st ∧ x.pend = y.pend := by
  cases x; cases y; simp

instance GCfg.decEq : DecidableEq GCfg := fun a b =>
  decidable_of_iff (a.st = b.st ∧ a.pend = b.pend) (gcfg_eq a b).symm


/-- A Go `Cfg` stands for the configuration `g`: its value, and its pending slice, read-only,
holding `g.pend`. -/
def cfgOk (c : Cfg) (g : GCfg) : IProp GF := iprop(⌜c.V' = g.st⌝ ∗ c.Pend' ↦*□ g.pend)

instance cfgOk_pers (c : Cfg) (g : GCfg) : Persistent (cfgOk (GF := GF) c g) := by
  unfold cfgOk; infer_instance

/-- A list of Go `Cfg`s stands for the list of configurations `L`, element by element. -/
def cfgsOk (cs : List Cfg) (L : List GCfg) : IProp GF :=
  iprop(⌜cs.length = L.length⌝ ∗
    □ ∀ (j : Nat) (c : Cfg) (g : GCfg), ⌜cs[j]? = some c⌝ -∗ ⌜L[j]? = some g⌝ -∗ cfgOk c g)

instance cfgsOk_pers (cs : List Cfg) (L : List GCfg) : Persistent (cfgsOk (GF := GF) cs L) := by
  unfold cfgsOk; infer_instance

theorem cfgsOk_nil : ⊢ cfgsOk (GF := GF) [] [] := by
  unfold cfgsOk
  isplitr
  · ipureintro; rfl
  iintro !> %j %c %g %h
  simp at h

theorem cfgsOk_snoc (cs : List Cfg) (L : List GCfg) (c : Cfg) (g : GCfg) :
    cfgsOk (GF := GF) cs L ∗ cfgOk c g ⊢ cfgsOk (cs ++ [c]) (L ++ [g]) := by
  unfold cfgsOk
  iintro ⟨⟨%hl, #H⟩, #Hc⟩
  isplitr
  · ipureintro; simp [hl]
  iintro !> %j %c' %g' %h1 %h2
  by_cases hj : j < cs.length
  · rw [List.getElem?_append_left hj] at h1
    rw [List.getElem?_append_left (hl ▸ hj)] at h2
    iapply H $$ %j %c' %g' %h1 %h2
  · rw [List.getElem?_append_right (by omega)] at h1
    rw [List.getElem?_append_right (by omega)] at h2
    have hj1 : j - cs.length < 1 := by
      have := (List.getElem?_eq_some_iff.1 h1).1; simpa using this
    rw [show j - cs.length = 0 by omega] at h1
    rw [show j - L.length = 0 by omega] at h2
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    iexact Hc

theorem cfgsOk_get (cs : List Cfg) (L : List GCfg) (j : Nat) (c : Cfg) (hc : cs[j]? = some c) :
    cfgsOk (GF := GF) cs L ⊢ ∃ g, ⌜L[j]? = some g⌝ ∗ cfgOk c g := by
  unfold cfgsOk
  iintro ⟨%hl, #H⟩
  have hj : j < L.length := hl ▸ (List.getElem?_eq_some_iff.1 hc).1
  iexists L[j]
  isplitr
  · ipureintro; simp
  iapply H $$ %j %c %L[j] %hc %(by simp)


theorem wp_hasCfg (sl : GoSlice) (dq : DFrac) (cs : List Cfg) (L : List GCfg) (c : Cfg) (g : GCfg) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*{dq} cs ∗ cfgsOk cs L ∗ cfgOk c g }}
      (App (App (Val (@! gryff.examples.gryffnet.hasCfg)) (Val #sl)) (Val #c))
    {{ RET #(decide (g ∈ L)); sl ↦*{dq} cs }} := by
  wp_start as ⟨Hsl, #Hcs, #Hc⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  ihave %HcsL : ⌜cs.length = L.length⌝ $$ []
  · unfold cfgsOk; icases Hcs with ⟨%h, -⟩; ipureintro; exact h
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "Hsl" ∷ sl ↦*{dq} cs ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len ∧ g ∉ L.take (sint.nat i)⌝ : IProp GF)
      $$ [i Hsl]
  · iexists W64 0
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by word, by rw [h0]; simp⟩
  wp_for HI
  obtain ⟨Hi0, Hil, Hni⟩ := Hi
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z sl.len := Hif
    obtain ⟨x, Hx_lookup⟩ : ∃ x, cs[sint.nat i]? = some x :=
      ⟨cs[sint.nat i]'(by rw [Hl.1]; word), List.getElem?_eq_getElem _⟩
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len from ⟨Hi0, hlt⟩)]
    wp_apply wp_load_slice_index sl (sint.Z i) cs _ x Hi0 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact Hx_lookup
    ihave ⟨%g', %Hg', #Hx⟩ := cfgsOk_get cs L (sint.nat i) x Hx_lookup $$ Hcs
    iclear %Hx_lookup
    unfold cfgOk
    icases Hx with ⟨%HxV, #HxP⟩
    icases Hc with ⟨%HcV, #HcP⟩
    wp_apply wp_sameCfg x c g'.pend g.pend $$ [$HxP $HcP]
    have hdec : decide (x.V' = c.V' ∧ g'.pend = g.pend) = decide (g' = g) := by
      rw [HxV, HcV]; exact decide_eq_decide.2 (gcfg_eq g' g).symm
    rw [hdec]
    by_cases hgg : g' = g
    · subst hgg
      simp only [_root_.decide_true]
      wp_auto
      wp_for_post
      have : g' ∈ L := List.mem_of_getElem? Hg'
      rw [decide_eq_true this]
      iapply HΦ
      iexact Hsl
    · simp only [hgg, _root_.decide_false]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      have hs : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      refine ⟨by word, by word, ?_⟩
      rw [hs, List.take_add_one, Hg']
      simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
      exact ⟨Hni, Ne.symm hgg⟩
  · have heq : sint.Z i = sint.Z sl.len := by omega
    have hn : sint.nat i = L.length := by
      rw [← HcsL, Hl.1]; show (sint.Z i).toNat = _; rw [heq]
    rw [hn, List.take_length] at Hni
    rw [decide_eq_false Hni]
    iapply HΦ
    iexact Hsl

end proof

end gryff.examples.gryffnet
end Perennial
