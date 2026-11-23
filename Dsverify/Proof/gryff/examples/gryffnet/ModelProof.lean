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

/-- One step of `reach`: pending operation `k` of `x` takes effect. -/
def succG (x : GCfg) (k : Nat) (hk : k < x.pend.length) : GCfg :=
  ⟨(applyG x.st x.pend[k]).1, x.pend.eraseIdx k⟩

theorem areach_trans {a b c : GCfg} (h1 : AReach a b) (h2 : AReach b c) : AReach a c := by
  induction h1 with
  | refl => exact h2
  | step k hk _ ih => exact .step k hk (ih h2)

theorem areach_succ {g x : GCfg} (h : AReach g x) (k : Nat) (hk : k < x.pend.length) :
    AReach g (succG x k hk) :=
  areach_trans h (.step k hk (.refl _))

theorem areach_closed {R : List GCfg}
    (hc : ∀ x ∈ R, ∀ k (hk : k < x.pend.length), succG x k hk ∈ R) {x y : GCfg} (hx : x ∈ R)
    (h : AReach x y) : y ∈ R := by
  induction h with
  | refl => exact hx
  | step k hk _ ih => exact ih (hc _ hx k hk)

theorem wp_reach (c : Cfg) (g : GCfg) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ cfgOk c g }}
      (App (Val (@! gryff.examples.gryffnet.reach)) (Val #c))
    {{ (sl : GoSlice), RET #sl; ∃ (cs : List Cfg) (R : List GCfg),
        sl ↦* cs ∗ cfgsOk cs R ∗ ⌜∀ y, y ∈ R ↔ AReach g y⌝ }} := by
  wp_start as #Hc
  wp_auto
  wp_apply wp_slice_literal (V := Cfg) [c]
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, Hcap0⟩
  wp_auto
  ihave #Hcs0 := cfgsOk_snoc [] [] c g $$ [$Hc]
  · iapply cfgsOk_nil
  simp only [List.nil_append] at *
  ihave HI : (∃ (k : w64) (sl : GoSlice) (cs : List Cfg) (R : List GCfg),
      "k" ∷ k_ptr ↦ k ∗ "out" ∷ out_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* cs ∗
      "Hcap" ∷ ownSliceCap Cfg sl (DFrac.own 1) ∗ "#Hcs" ∷ cfgsOk cs R ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ R.length ∧ g ∈ R ∧ (∀ y ∈ R, AReach g y) ∧
        ∀ j x, j < sint.nat k → R[j]? = some x → ∀ i (hi : i < x.pend.length), succG x i hi ∈ R⌝ :
      IProp GF) $$ [k out Hsl0 Hcap0]
  · iexists W64 0, _, [c], [g]
    iframe
    iframe #
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    refine ⟨by word, by rw [h0]; simp, by simp, ?_, fun j x hj => by rw [h0] at hj; omega⟩
    intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact .refl _
  wp_for HI
  obtain ⟨Hk0, HkR, HgR, HRr, HRc⟩ := Hk
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  ihave %HcsR : ⌜cs.length = R.length⌝ $$ []
  · unfold cfgsOk; icases Hcs with ⟨%h, -⟩; ipureintro; exact h
  wp_if_destruct
  · have hlt : sint.Z k < sint.Z sl.len := Hif
    obtain ⟨xc, Hx_lookup⟩ : ∃ x, cs[sint.nat k]? = some x :=
      ⟨cs[sint.nat k]'(by rw [Hl.1]; word), List.getElem?_eq_getElem _⟩
    rw [ite_eq_left (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len from ⟨Hk0, hlt⟩)]
    wp_apply wp_load_slice_index sl (sint.Z k) cs _ xc Hk0 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact Hx_lookup
    ihave ⟨%xg, %Hxg, #Hx⟩ := cfgsOk_get cs R (sint.nat k) xc Hx_lookup $$ Hcs
    unfold cfgOk
    icases Hx with ⟨%HxV, #HxP⟩
    ihave %HxL := ownSlice_len _ _ _ $$ HxP
    ihave HJ : (∃ (iv : w64) (sl' : GoSlice) (cs' : List Cfg) (R' : List GCfg),
        "i" ∷ i_ptr ↦ iv ∗ "out" ∷ out_ptr ↦ sl' ∗ "Hsl" ∷ sl' ↦* cs' ∗
        "Hcap" ∷ ownSliceCap Cfg sl' (DFrac.own 1) ∗ "#Hcs" ∷ cfgsOk cs' R' ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv ≤ xg.pend.length ∧ R <+: R' ∧
          (∀ y ∈ R', AReach g y) ∧
          ∀ i' (hi' : i' < xg.pend.length), i' < sint.nat iv → succG xg i' hi' ∈ R'⌝ :
        IProp GF) $$ [i out Hsl Hcap]
    · iexists W64 0, sl, cs, R
      iframe
      iframe #
      ipureintro
      have h0 : sint.nat (W64 0) = 0 := rfl
      refine ⟨by word, by rw [h0]; omega, List.prefix_refl _, HRr, fun i' _ h => by rw [h0] at h; omega⟩
    wp_for HJ
    obtain ⟨Hi0, HiL, HRR', HR'r, HR'c⟩ := Hi
    ihave %Hl' := ownSlice_len _ _ _ $$ Hsl
    ihave %HcsR' : ⌜cs'.length = R'.length⌝ $$ []
    · unfold cfgsOk; icases Hcs with ⟨%h, -⟩; ipureintro; exact h
    wp_if_destruct
    · have hlt : sint.Z iv < sint.Z xc.Pend'.len := Hif
      have hiv : sint.nat iv < xg.pend.length := by rw [HxL.1]; word
      have Hp : xg.pend[sint.nat iv]? = some xg.pend[sint.nat iv] := List.getElem?_eq_getElem hiv
      rw [ite_eq_left (show 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z xc.Pend'.len from ⟨Hi0, hlt⟩)]
      wp_apply wp_load_slice_index xc.Pend' (sint.Z iv) xg.pend _ _ Hi0 $$ [HxP] as -
      · iframe HxP; ipureintro; exact Hp
      wp_apply wp_apply
      wp_apply +noauto wp_without xc.Pend' xg.pend iv Hi0 $$ [$HxP] as %q Hq
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hq with #Hq
      imodintro
      wp_auto
      ihave #Hy : cfgOk (Cfg.mk (applyG xc.V' xg.pend[sint.nat iv]).1 q) (succG xg (sint.nat iv) hiv) $$ []
      · unfold cfgOk succG
        isplitr
        · ipureintro; simp [HxV]
        iexact Hq
      wp_apply wp_hasCfg sl' _ cs' R' _ (succG xg (sint.nat iv) hiv) $$ [$Hsl $Hcs $Hy] as Hsl
      have hs : sint.nat (iv + W64 1) = sint.nat iv + 1 := by word
      by_cases hin : succG xg (sint.nat iv) hiv ∈ R'
      · simp only [hin, _root_.decide_true, Bool.not_true]
        wp_auto
        wp_for_post
        iframe
        iexists iv + W64 1, sl', cs', R'
        iframe
        iframe #
        ipureintro
        refine ⟨by word, by rw [hs]; omega, HRR', HR'r, fun i' hi' h => ?_⟩
        rw [hs] at h
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
        · exact HR'c i' hi' h
        · subst h; exact hin
      · simp only [hin, _root_.decide_false, Bool.not_false]
        wp_auto
        wp_apply wp_slice_literal (V := Cfg) [_]
        isplitr
        · ipureintro; rfl
        iintro %sl1 ⟨Hsl1, -⟩
        wp_auto
        wp_apply wp_slice_append (V := Cfg) $$ [$Hsl $Hcap $Hsl1] as %q' ⟨Hq', Hcap', -⟩
        wp_for_post
        iframe
        ihave #Hcs2 := cfgsOk_snoc cs' R' _ _ $$ [$Hcs $Hy]
        iexists iv + W64 1, q', _, R' ++ [succG xg (sint.nat iv) hiv]
        iframe
        iframe #
        ipureintro
        refine ⟨by word, by rw [hs]; omega, HRR'.trans (List.prefix_append _ _), ?_, fun i' hi' h => ?_⟩
        · intro y hy
          rcases List.mem_append.1 hy with hy | hy
          · exact HR'r y hy
          · simp only [List.mem_singleton] at hy; subst hy
            exact areach_succ (HRr xg (List.mem_of_getElem? Hxg)) _ hiv
        · rw [hs] at h
          rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
          · exact List.mem_append_left _ (HR'c i' hi' h)
          · subst h; exact List.mem_append_right _ (List.mem_singleton_self _)
    · have hend : sint.nat iv = xg.pend.length := by
        have h1 := HiL; rw [HxL.1] at h1 ⊢; word
      have hkR : sint.nat k < R.length := by rw [← HcsR, Hl.1]; word
      have hks : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      obtain ⟨t, rfl⟩ := HRR'
      wp_for_post
      iframe
      iexists k + W64 1, sl', cs', R ++ t
      iframe
      iframe #
      ipureintro
      refine ⟨by word, by rw [hks]; simp; omega, List.mem_append_left _ HgR, HR'r, ?_⟩
      intro j x hj hx i' hi'
      rw [hks] at hj
      have hjR : j < R.length := by omega
      rw [List.getElem?_append_left hjR] at hx
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact List.mem_append_left _ (HRc j x hj hx i' hi')
      · subst hj
        rw [Hxg] at hx
        cases hx
        exact HR'c i' hi' (by omega)
  · have hkR : sint.nat k = R.length := by
      have h1 := HkR; rw [← HcsR, Hl.1] at h1 ⊢; word
    iapply HΦ
    iexists cs, R
    iframe Hsl
    iframe #
    ipureintro
    intro y
    constructor
    · exact HRr y
    · intro h
      refine areach_closed (fun x hx i hi => ?_) HgR h
      obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
      exact HRc j x (by omega) (by rw [← hjx]; exact List.getElem?_eq_getElem hj) i hi

theorem areach_len {x y : GCfg} (h : AReach x y) : y.pend.length ≤ x.pend.length := by
  induction h with
  | refl => exact Nat.le_refl _
  | step k hk _ ih => simp [List.length_eraseIdx, hk] at ih; omega

theorem pseq_unknown (cs : List GCfg) (hne : cs ≠ []) (i : In) :
    (pSeq casB).step (cfgSet cs) (i, .err) =
      some (cfgSet (if isWriteG i then cs.map (fun x => ⟨x.st, x.pend ++ [i]⟩) else cs)) := by
  cases hw : isWriteG i
  · simp only [Bool.false_eq_true, ↓reduceIte, pSeq]
    rw [post_errR cs i hw, if_pos (cfgSet_nonempty.2 hne)]
  · simp only [↓reduceIte, pSeq]
    rw [post_errW cs i hw, if_pos (cfgSet_nonempty.2 (by simpa using hne))]

/-- `step`'s result: the verdict and the next list (`stepG_pSeq`). -/
def stepRes (L : List GCfg) (i : In) (o : Out) (ok : Bool) (L' : List GCfg) : Prop :=
  (pSeq casB).step (cfgSet L) (i, if o.Unknown' then .err else .ok o) =
    (if ok then some (cfgSet L') else none)

theorem wp_stepGo (sl : GoSlice) (cs : List Cfg) (L : List GCfg) (hne : L ≠ []) (k : Nat)
    (hk : k < 2 ^ 60) (hL : ∀ x ∈ L, x.pend.length ≤ k) (i : In) (o : Out) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ sl ↦*□ cs ∗ cfgsOk cs L }}
      (App (App (App (Val (@! gryff.examples.gryffnet.step)) (Val #(State.mk sl))) (Val #i))
        (Val #o))
    {{ (ok : Bool) (s' : State), RET (PairV #ok #s'); ∃ (sl' : GoSlice) (cs' : List Cfg)
        (L' : List GCfg), ⌜s' = State.mk sl' ∧ stepRes L i o ok L' ∧
          (ok = true → L' ≠ [] ∧ ∀ x ∈ L', x.pend.length ≤ k + 1)⌝ ∗
        sl' ↦*□ cs' ∗ cfgsOk cs' L' }} := by
  wp_start as ⟨#Hsl, #Hcs⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  ihave %HcsL : ⌜cs.length = L.length⌝ $$ []
  · unfold cfgsOk; icases Hcs with ⟨%h, -⟩; ipureintro; exact h
  wp_auto
  cases hu : o.Unknown'
  · sorry
  · have H := pseq_unknown L hne i
    wp_auto
    wp_apply wp_isWrite
    cases hw : isWriteG i
    · simp only [Bool.not_false]
      wp_auto
      iapply HΦ
      iexists sl, cs, L
      iframe #
      ipureintro
      refine ⟨rfl, ?_, fun _ => ⟨hne, fun x hx => by have := hL x hx; omega⟩⟩
      unfold stepRes
      simp only [hu, ↓reduceIte, H, hw, Bool.false_eq_true]
    · simp only [Bool.not_true]
      wp_auto
      sorry

end proof

end gryff.examples.gryffnet
end Perennial
