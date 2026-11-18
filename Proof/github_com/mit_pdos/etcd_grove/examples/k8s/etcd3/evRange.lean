module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.evRange

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- The Go loop's `(lo, hi)` after some events: the model's range, `(2^64 - 1, 0)` before any. -/
def evRangeG (evs : List WEv) : Nat × Nat := (evRangeL evs).getD (2 ^ 64 - 1, 0)

theorem evRangeL_snoc (l : List WEv) (e : WEv) :
    evRangeL (l ++ [e]) = evRStep (evRangeL l) e := by
  simp [evRangeL, List.foldl_append]

theorem evRangeG_snoc (l : List WEv) (e : WEv) (h : evLo e ≤ 2 ^ 64 - 1) :
    evRangeG (l ++ [e]) = (min (evRangeG l).1 (evLo e), max (evRangeG l).2 (evHi e)) := by
  unfold evRangeG
  rw [evRangeL_snoc]
  cases hl : evRangeL l with
  | none => simp only [evRStep, Option.getD_some, Option.getD_none]; ext <;> simp; omega
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only [evRStep, Option.getD_some, Nat.min_comm, Nat.max_comm]

theorem evRStep_foldl_some (l : List WEv) (p : Nat × Nat) :
    ∃ q, l.foldl evRStep (some p) = some q := by
  induction l generalizing p with
  | nil => exact ⟨p, rfl⟩
  | cons e l ih =>
    obtain ⟨a, b⟩ := p
    exact ih _

theorem evRangeL_some (l : List WEv) (h : l ≠ []) : evRangeL l = some (evRangeG l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons e l =>
    obtain ⟨q, hq⟩ := evRStep_foldl_some l (evLo e, evHi e)
    have : evRangeL (e :: l) = some q := hq
    rw [evRangeG, this]; rfl

theorem evRange.wp_proof : evRange.spec (GF := GF) (hG := hG) := by
  intro s evs Hevs
  have hmin : (#(functions go.min [go.uint64, go.uint64]) : val) = min.impl go.uint64 2 :=
    FuncUnfold.func_unfold (f := go.min) (type_args := List.replicate 2 go.uint64)
  have hmax : (#(functions go.max [go.uint64, go.uint64]) : val) = max.impl go.uint64 2 :=
    FuncUnfold.func_unfold (f := go.max) (type_args := List.replicate 2 go.uint64)
  wp_start as #Hs
  unfold wevsOwn
  icases Hs with ⟨%ws, #Hk, %He⟩
  subst He
  ihave %Hl := ownSlice_len $$ Hk
  wp_auto
  ihave HI : (∃ (j : w64) (evv : WEvent) (lo hi : w64),
      "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ evv ∗ "lo" ∷ lo_ptr ↦ lo ∗ "hi" ∷ hi_ptr ↦ hi ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len ∧
        (uint.nat lo, uint.nat hi) = evRangeG ((ws.map wevOf).take (sint.nat j))⌝ : IProp GF)
      $$ [i ev lo hi]
  · iexists W64 0, _, _, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    rfl
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, Hif⟩
    list_elem ws (sint.nat j) as w
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z j) ws _ w Hj.1 $$ [Hk] as -
    · isplit
      · iexact Hk
      · ipureintro; exact Hw_lookup
    have hw : uint.Z w.Obj'.ResourceVersion' < 2 ^ 63 :=
      Hevs (wevOf w) (List.mem_map_of_mem (List.mem_of_getElem? Hw_lookup))
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htake : (ws.map wevOf).take (sint.nat j + 1) = (ws.map wevOf).take (sint.nat j) ++ [wevOf w] := by
      rw [List.take_add_one]; simp [Hw_lookup]
    have hstep := evRangeG_snoc ((ws.map wevOf).take (sint.nat j)) (wevOf w)
      (by unfold evLo wevOf; split <;> word)
    rw [← Hj.2.2] at hstep
    have h3 : uint.nat w.Type' = 3 ↔ w.Type' = W64 3 := by
      constructor
      · intro h; word
      · intro h; rw [h]; rfl
    (try wp_auto)
    wp_if_destruct
    · have hT := Hif; clear Hif
      have hlo : evLo (wevOf w) = uint.nat w.Obj'.ResourceVersion' + 1 := by
        simp [evLo, wevOf, h3, hT]
      have hhi : evHi (wevOf w) = uint.nat w.Obj'.ResourceVersion' := by
        simp [evHi, wevOf, h3, hT]
      iterate 4
        all_goals (try simp only [hmin, hmax])
        all_goals (try wp_auto)
        all_goals (try wp_if_destruct)
      all_goals
        wp_for_post
        iframe
        iexists j + W64 1, w, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hj1, htake, hstep, hlo, hhi]
        simp only [Prod.mk.injEq]
        constructor <;> word
    · have hT := Hif; clear Hif
      have hlo : evLo (wevOf w) = uint.nat w.Obj'.ResourceVersion' := by
        simp [evLo, wevOf, h3]; exact hT
      have hhi : evHi (wevOf w) = uint.nat w.Obj'.ResourceVersion' + 1 := by
        simp [evHi, wevOf, h3]; exact hT
      iterate 4
        all_goals (try simp only [hmin, hmax])
        all_goals (try wp_auto)
        all_goals (try wp_if_destruct)
      all_goals
        wp_for_post
        iframe
        iexists j + W64 1, w, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hj1, htake, hstep, hlo, hhi]
        simp only [Prod.mk.injEq]
        constructor <;> word
  · have hfull : (ws.map wevOf).take (sint.nat j) = ws.map wevOf :=
      List.take_of_length_le (by simp; word)
    rw [hfull] at Hj
    (try wp_auto)
    iapply HΦ
    ipureintro
    intro hne
    rw [evRangeL_some _ hne, ← Hj.2.2]

end proof