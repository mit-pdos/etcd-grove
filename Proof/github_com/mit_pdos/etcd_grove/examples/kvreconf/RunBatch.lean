/-
Lean-first (no Rocq counterpart).

# Freezing a `Ready`'s committed entries (2026-10-30, kvreconf's `run`)

The `Ready`'s committed entries `ce` follow the delivered log `D`. The first `m0` of them are frozen
already (`ceFrozen`). The rest are the batch's first entries (`readyRest_ceInBatch`, the batch
consecutive by `kvr_readyRest_indices`), so `batch_tail` shows they are the same Go entries. After
`Append`, the applier freezes that prefix of the batch (`batch_freeze`). This gives `frozenTo c (D ++ ce)`
and the receipt `Advance` takes (`appendReceipt` of the frozen prefix, at the memLog level).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunFrozen

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- An entry handed out at its own index, read back. -/
theorem toEntryM_ofEntryM [GooseExts] (y : EntryM) (k : Nat) (hk : uint.nat y.Index' = k) :
    (LogEntry.ofEntryM y).toEntryM (W64 (k : Int)) = y := by
  cases y
  simp only [LogEntry.ofEntryM, LogEntry.toEntryM] at hk ⊢
  congr 1
  subst hk; word

/-- The committed entries not yet frozen are the batch's first ones. -/
theorem batch_tail [GooseExts] (D ce : List LogEntry) (es : List EntryM) (m0 : Nat) (e0 : EntryM)
    (hhead : es.head? = some e0) (hm : D.length + 1 + m0 = uint.nat e0.Index')
    (Hin : ∀ (j : Nat) (e : LogEntry), ce[j]? = some e → uint.nat e0.Index' ≤ D.length + 1 + j →
      Option.map LogEntry.ofEntryM es[D.length + 1 + j - uint.nat e0.Index']? = some e)
    (Hidx : ∀ j e, es[j]? = some e → uint.nat e.Index' = uint.nat e0.Index' + j) :
    (LogEntry.toEntries ce D.length).drop m0 = es.take (ce.length - m0) ∧
      ce.length - m0 ≤ es.length := by
  constructor
  · apply List.ext_getElem?
    intro i
    rw [List.getElem?_drop, List.getElem?_take]
    by_cases hi : i < ce.length - m0
    · rw [if_pos hi]
      have hci : m0 + i < ce.length := by omega
      obtain ⟨x, hx⟩ : ∃ x, ce[m0 + i]? = some x := ⟨_, List.getElem?_eq_getElem hci⟩
      rw [kvr_toEntries_get ce D.length (m0 + i) x hx]
      have h1 := Hin (m0 + i) x hx (by omega)
      rw [show D.length + 1 + (m0 + i) - uint.nat e0.Index' = i by omega] at h1
      cases hy : es[i]? with
      | none => rw [hy] at h1; cases h1
      | some y =>
        rw [hy] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        subst h1
        have := Hidx i y hy
        have h2 : (W64 ((D.length : Int) + ((m0 + i : Nat) : Int) + 1)) = y.Index' := by word
        rw [h2]; cases y; rfl
    · rw [if_neg hi]
      have : ce.length ≤ m0 + i := by omega
      unfold LogEntry.toEntries
      rw [List.getElem?_mapIdx, List.getElem?_eq_none this]; rfl
  · apply Nat.le_of_not_lt; intro hc
    have hj : m0 + es.length < ce.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, ce[m0 + es.length]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    have h1 := Hin (m0 + es.length) x hx (by omega)
    rw [show D.length + 1 + (m0 + es.length) - uint.nat e0.Index' = es.length by omega,
      List.getElem?_eq_none (Nat.le_refl _)] at h1
    cases h1

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- A range from its two parts. -/
theorem memLog_take_drop (γs : MemStorNames) (k : Nat) (dq : DFrac) (l : List EntryM) (m : Nat)
    (hm : m ≤ l.length) :
    memLog (GF := GF) γs k dq (l.take m) ∗ memLog γs (k + m) dq (l.drop m) ⊢ memLog γs k dq l := by
  have h := memLog_app (GF := GF) γs k dq (l.take m) (l.drop m)
  rw [List.take_append_drop, List.length_take_of_le hm] at h
  exact h.2

/-- Freezing past the delivered log. -/
theorem frozenTo_app (γs : MemStorNames) (c : Nat) (D ce : List LogEntry) (Hc : c ≤ D.length) :
    frozenTo (GF := GF) γs c D ∗ memLog γs (D.length + 1) DFrac.discard
      (LogEntry.toEntries ce D.length) ⊢ frozenTo γs c (D ++ ce) := by
  unfold frozenTo
  rw [kvr_toEntries_append, Nat.zero_add,
    List.drop_append_of_le_length (by rw [kvr_toEntries_length]; exact Hc)]
  iintro ⟨H1, H2⟩
  iapply (memLog_app γs (c + 1) DFrac.discard _ _).2
  iframe H1
  rw [List.length_drop, kvr_toEntries_length, show c + 1 + (D.length - c) = D.length + 1 by omega]
  iexact H2

/-- **Freezing a `Ready`'s committed entries** (see the file header): from the frozen delivered log,
the frozen first `m0` committed entries (`ceFrozen`) and the batch appended at `k`. -/
theorem batch_freeze (γs : MemStorNames) (c : Nat) (D ce : List LogEntry) (es : List EntryM)
    (m0 k : Nat) (Hc : c ≤ D.length)
    (Hm : m0 = ce.length ∨ ∃ e0, es.head? = some e0 ∧ D.length + 1 + m0 = uint.nat e0.Index')
    (Hin : ∀ e0, es.head? = some e0 → ∀ (j : Nat) (e : LogEntry), ce[j]? = some e →
      uint.nat e0.Index' ≤ D.length + 1 + j →
      Option.map LogEntry.ofEntryM es[D.length + 1 + j - uint.nat e0.Index']? = some e)
    (Hidx : ∀ e0, es.head? = some e0 → ∀ j e, es[j]? = some e →
      uint.nat e.Index' = uint.nat e0.Index' + j)
    (Hk : ∀ e0, es.head? = some e0 → k = uint.nat e0.Index') :
    ⊢ frozenTo (GF := GF) γs c D -∗
      memLog γs (D.length + 1) DFrac.discard ((LogEntry.toEntries ce D.length).take m0) -∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) ==∗
      frozenTo γs c (D ++ ce) ∗ ∃ a : List EntryM,
        ⌜(a ≠ [] → k - 1 + a.length ≤ (D ++ ce).length) ∧ a <+: es⌝ ∗
        (if es = [] then emp else memLog γs k DFrac.discard a ∗
          memLog γs (k + a.length) (DFrac.own 1) (es.drop a.length) ∗ memEnd γs (k + es.length)) := by
  iintro #Hf #Hm0 Hb
  by_cases hall : ce.length ≤ m0
  · rw [List.take_of_length_le (by rw [kvr_toEntries_length]; exact hall)]
    imodintro
    isplitl []
    · iapply frozenTo_app γs c D ce Hc; iframe Hf Hm0
    iexists []
    isplitr
    · ipureintro; exact ⟨fun h => absurd rfl h, List.nil_prefix⟩
    by_cases he : es = []
    · subst he; simp only [if_true]; iexact Hb
    · simp only [if_neg he, List.length_nil, Nat.add_zero, List.drop_zero]
      icases Hb with ⟨Hl, He⟩
      iframe Hl He
      iapply memLog_nil
  · have hlt : m0 < ce.length := Nat.lt_of_not_le hall
    obtain ⟨e0, hh, hm⟩ : ∃ e0, es.head? = some e0 ∧ D.length + 1 + m0 = uint.nat e0.Index' := by
      rcases Hm with h | h
      · omega
      · exact h
    have hne : es ≠ [] := by intro h; subst h; cases hh
    obtain ⟨Htail, Hle⟩ := batch_tail D ce es m0 e0 hh hm (Hin e0 hh) (Hidx e0 hh)
    have hk := Hk e0 hh
    simp only [if_neg hne]
    icases Hb with ⟨Hl, He⟩
    have hsplit : es = es.take (ce.length - m0) ++ es.drop (ce.length - m0) :=
      (List.take_append_drop _ _).symm
    have hlen : (es.take (ce.length - m0)).length = ce.length - m0 := List.length_take_of_le Hle
    rw [hsplit]
    icases (memLog_app γs k (DFrac.own 1) _ _).1 $$ Hl with ⟨Ha, Hrest⟩
    rw [← hsplit]
    imod memLog_persist γs k (DFrac.own 1) _ $$ Ha with #Ha
    imodintro
    isplitl []
    · iapply frozenTo_app γs c D ce Hc
      iframe Hf
      iapply memLog_take_drop γs _ DFrac.discard _ m0
        (by rw [kvr_toEntries_length]; exact Nat.le_of_lt hlt)
      iframe Hm0
      rw [Htail, show D.length + 1 + m0 = k by omega]
      iexact Ha
    iexists es.take (ce.length - m0)
    isplitr
    · ipureintro
      refine ⟨fun _ => ?_, List.take_prefix _ _⟩
      rw [hlen, List.length_append]; omega
    rw [hlen]
    iframe Ha Hrest He

end ghost

end kvreconf
end EtcdGrove
end Perennial
