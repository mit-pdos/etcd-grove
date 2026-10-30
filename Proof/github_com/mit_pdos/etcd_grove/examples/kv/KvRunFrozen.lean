/-
Lean-first (no Rocq counterpart).

# `run`'s frozen entries and appends (2026-10-30, stage P of the client repair: kvreconf's
`RunFrozen`/`RunBatch`/`RunAppend`, at kv's storage)

`frozenTo γs c D` holds the delivered log `D`'s entries above `c` read-only in the storage; a
snapshot or a compaction at `i` in `(c, |D|]` takes the entry there (`frozenTo_at`). A `Ready`'s
committed entries not yet frozen are its batch's first ones (`batch_tail`); after `Append` the
applier freezes them (`batch_freeze`), which gives `frozenTo` past them and `Advance`'s receipt
(`append_none_pre`/`append_none_post`, at the wrapper's interface).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3


/-- The Go entry at position `k` of the log entries `ce` handed out after `base`. -/
theorem kv_toEntries_get [GooseExts] (ce : List LogEntry) (base k : Nat) (en : LogEntry)
    (h : ce[k]? = some en) :
    (LogEntry.toEntries ce base)[k]? = some (en.toEntryM (W64 (base + k + 1))) := by
  unfold LogEntry.toEntries; rw [List.getElem?_mapIdx, h]; rfl

theorem kv_toEntries_length [GooseExts] (ce : List LogEntry) (base : Nat) :
    (LogEntry.toEntries ce base).length = ce.length := by
  unfold LogEntry.toEntries; simp

theorem kv_toEntries_append [GooseExts] (a b : List LogEntry) (base : Nat) :
    LogEntry.toEntries (a ++ b) base =
      LogEntry.toEntries a base ++ LogEntry.toEntries b (base + a.length) := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a.length
  · rw [List.getElem?_append_left (by rw [kv_toEntries_length]; exact hk)]
    obtain ⟨x, hx⟩ : ∃ x, a[k]? = some x := ⟨a[k], List.getElem?_eq_getElem hk⟩
    rw [kv_toEntries_get a base k x hx,
      kv_toEntries_get (a ++ b) base k x (by rw [List.getElem?_append_left hk]; exact hx)]
  · have hk' : a.length ≤ k := Nat.le_of_not_lt hk
    rw [List.getElem?_append_right (by rw [kv_toEntries_length]; exact hk'),
      kv_toEntries_length]
    cases hb : b[k - a.length]? with
    | none =>
      have h1 : (a ++ b)[k]? = none := by rw [List.getElem?_append_right hk']; exact hb
      have h2 : (LogEntry.toEntries (a ++ b) base)[k]? = none := by
        unfold LogEntry.toEntries; rw [List.getElem?_mapIdx, h1]; rfl
      have h3 : (LogEntry.toEntries b (base + a.length))[k - a.length]? = none := by
        unfold LogEntry.toEntries; rw [List.getElem?_mapIdx, hb]; rfl
      rw [h2, h3]
    | some x =>
      rw [kv_toEntries_get (a ++ b) base k x (by rw [List.getElem?_append_right hk']; exact hb),
        kv_toEntries_get b (base + a.length) (k - a.length) x hb]
      congr 3
      omega

section frozen
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- One entry of a range. -/
theorem memLog_elem (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) (j : Nat)
    (e : EntryM) (h : es[j]? = some e) :
    memLog (GF := GF) γs k dq es ⊢ memLog γs (k + j) dq [e] := by
  have hj : j < es.length := by
    rcases Nat.lt_or_ge j es.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have he : es[j] = e := by
    rw [List.getElem?_eq_getElem hj] at h; cases h; rfl
  have hes : es = es.take j ++ ([e] ++ es.drop (j + 1)) := by
    refine (List.take_append_drop j es).symm.trans ?_
    rw [List.drop_eq_getElem_cons hj, he]; rfl
  have hl : (es.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  rw [hes]
  iintro H
  icases (memLog_app γs k dq _ _).1 $$ H with ⟨-, H⟩
  icases (memLog_app γs _ dq _ _).1 $$ H with ⟨H, -⟩
  rw [hl]
  iexact H

/-- **The frozen entry at `i`** in `(c, |D|]`, with `D`'s term there. -/
theorem frozenTo_at (γs : MemStorNames) (c : Nat) (D : List LogEntry) (i : Nat)
    (h1 : c < i) (h2 : i ≤ D.length) :
    frozenTo (GF := GF) γs c D ⊢ ∃ e : EntryM, memLog γs i DFrac.discard [e] ∗
      ⌜∀ x, D[i - 1]? = some x → e = x.toEntryM (W64 i)⌝ := by
  unfold frozenTo
  have hx : i - 1 < D.length := by omega
  have hD : D[i - 1]? = some D[i - 1] := List.getElem?_eq_getElem hx
  have hg := kv_toEntries_get D 0 (i - 1) D[i - 1] hD
  have hg0 : ((LogEntry.toEntries D 0).drop c)[i - 1 - c]? = (LogEntry.toEntries D 0)[i - 1]? := by
    rw [List.getElem?_drop, show c + (i - 1 - c) = i - 1 by omega]
  have hg' : ((LogEntry.toEntries D 0).drop c)[i - 1 - c]? = some (D[i - 1].toEntryM (W64 i)) := by
    rw [hg0, hg]; congr 3; push_cast; omega
  iintro #H
  ihave H' := memLog_elem γs (c + 1) DFrac.discard _ (i - 1 - c) _ hg' $$ H
  rw [show c + 1 + (i - 1 - c) = i by omega]
  iexists D[i - 1].toEntryM (W64 i)
  iframe H'
  ipureintro
  intro x hxx
  rw [hD] at hxx; cases hxx; rfl

end frozen



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
      rw [kv_toEntries_get ce D.length (m0 + i) x hx]
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

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
  rw [kv_toEntries_append, Nat.zero_add,
    List.drop_append_of_le_length (by rw [kv_toEntries_length]; exact Hc)]
  iintro ⟨H1, H2⟩
  iapply (memLog_app γs (c + 1) DFrac.discard _ _).2
  iframe H1
  rw [List.length_drop, kv_toEntries_length, show c + 1 + (D.length - c) = D.length + 1 by omega]
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
  · rw [List.take_of_length_le (by rw [kv_toEntries_length]; exact hall)]
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
        (by rw [kv_toEntries_length]; exact Nat.le_of_lt hlt)
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



section append
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]


theorem append_none_pre (st ms : Loc) (γs : MemStorNames) (es : List EntryM) :
    ⊢ kvStorRec (GF := GF) st ms γs -∗ appendRight (kvStorIface st) es -∗
      ∃ (k : Nat) (old : List EntryM),
        ⌜(∀ e0, es.head? = some e0 → k = uint.nat e0.Index') ∧ (es = [] → k = 0)⌝ ∗
        (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)) := by
  iintro #Hrec Happ
  iunfold appendRight at Happ
  icases Happ with (%He | ⟨%e0, %old, %Hh, Hl, He⟩)
  · subst He
    iexists 0, []
    simp only [if_true]
    isplitr
    · ipureintro; simp
    itrivial
  · iexists uint.nat e0.Index', old
    have hne : es ≠ [] := by intro h; subst h; cases Hh
    simp only [if_neg hne]
    isplitr
    · ipureintro; exact ⟨fun e h => by rw [Hh] at h; cases h; rfl, fun h => absurd h hne⟩
    ihave Hl := kvStorLog_to st ms γs _ _ _ $$ Hrec Hl
    ihave He := kvStorEnd_to st ms γs _ $$ Hrec He
    iframe Hl He

theorem append_none_post (st ms : Loc) (γs : MemStorNames) (c : Nat) (D ce : List LogEntry)
    (es : List EntryM) (k : Nat) (Hc : c ≤ D.length)
    (Hin : ∀ e0, es.head? = some e0 → ∀ (j : Nat) (e : LogEntry), ce[j]? = some e →
      uint.nat e0.Index' ≤ D.length + 1 + j →
      Option.map LogEntry.ofEntryM es[D.length + 1 + j - uint.nat e0.Index']? = some e)
    (Hidx : ∀ e0, es.head? = some e0 → ∀ j e, es[j]? = some e →
      uint.nat e.Index' = uint.nat e0.Index' + j)
    (Hk : ∀ e0, es.head? = some e0 → k = uint.nat e0.Index') :
    ⊢ kvStorRec (GF := GF) st ms γs -∗ frozenTo γs c D -∗
      ceFrozen (kvStorIface st) D.length (LogEntry.toEntries ce D.length) es -∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) ==∗
      frozenTo γs c (D ++ ce) ∗ advReceipt (kvStorIface st) (D ++ ce).length es none := by
  iintro #Hrec #Hf #Hcf Hb
  iunfold ceFrozen at Hcf
  icases Hcf with ⟨%m0, #Hm0, %Hm⟩
  ihave #Hm0 := kvStorLog_to st ms γs _ _ _ $$ Hrec Hm0
  have Hm' : m0 = ce.length ∨ ∃ e0, es.head? = some e0 ∧ D.length + 1 + m0 = uint.nat e0.Index' := by
    rw [kv_toEntries_length] at Hm; exact Hm
  imod batch_freeze γs c D ce es m0 k Hc Hm' Hin Hidx Hk $$ Hf Hm0 Hb with ⟨#Hf', %a, %Ha, Hr⟩
  imodintro
  iframe Hf'
  unfold advReceipt
  iexists a
  isplitl
  · unfold appendReceipt
    by_cases he : es = []
    · ileft; ipureintro; exact he
    · iright
      simp only [if_neg he]
      icases Hr with ⟨#Ha', Hb', He'⟩
      obtain ⟨e0, he0⟩ : ∃ e0, es.head? = some e0 := by
        cases es with
        | nil => exact absurd rfl he
        | cons x xs => exact ⟨x, rfl⟩
      iexists e0, es.drop a.length
      isplitr
      · ipureintro
        obtain ⟨t, rfl⟩ := Ha.2
        refine ⟨he0, ?_⟩
        simp
      rw [← Hk e0 he0]
      ihave Ha' := kvStorLog_of st ms γs _ _ _ $$ Hrec Ha'
      ihave Hb' := kvStorLog_of st ms γs _ _ _ $$ Hrec Hb'
      ihave He' := kvStorEnd_of st ms γs _ $$ Hrec He'
      iframe Ha' Hb' He'
  · ipureintro
    intro hne e0 he0
    have := Ha.1 hne
    rw [Hk e0 he0] at this
    exact this

end append

end kv
end EtcdGrove
end Perennial
