/-
Lean-first (no Rocq counterpart).

# Freezing a `Ready`'s committed entries in the raft loop (2026-10-30, the repair; stage P, S-C)

The server's version of kvreconf's `batch_freeze` (`examples/kvreconf/RunBatch.lean`). A `Ready`'s
committed entries `ce` follow the delivered log of length `n`. The node API freezes the first `m0`
of them (`ceFrozen`). The rest are the batch's first entries (`srv_batch_tail`), which the loop
freezes after `Append`, before `Advance` (`srv_batch_freeze`). This gives the batch's frozen range
(`srvFrozenRange`, `raftAdvancedC`'s payload) and the receipt `Advance` takes (`advReceipt none` with
the frozen prefix): `rn_freeze_receipt`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

theorem srv_toEntries_get [GooseExts] (ce : List LogEntry) (base k : Nat) (en : LogEntry)
    (h : ce[k]? = some en) :
    (LogEntry.toEntries ce base)[k]? = some (en.toEntryM (W64 (base + k + 1))) := by
  unfold LogEntry.toEntries; rw [List.getElem?_mapIdx, h]; rfl

theorem srv_toEntries_length [GooseExts] (ce : List LogEntry) (base : Nat) :
    (LogEntry.toEntries ce base).length = ce.length := by
  unfold LogEntry.toEntries; simp

/-- The committed entries not yet frozen are the batch's first ones. -/
theorem srv_batch_tail [GooseExts] (n : Nat) (ce : List LogEntry) (es : List EntryM) (m0 : Nat)
    (e0 : EntryM) (_hhead : es.head? = some e0) (hm : n + 1 + m0 = uint.nat e0.Index')
    (Hin : ∀ (j : Nat) (e : LogEntry), ce[j]? = some e → uint.nat e0.Index' ≤ n + 1 + j →
      Option.map LogEntry.ofEntryM es[n + 1 + j - uint.nat e0.Index']? = some e)
    (Hidx : ∀ j e, es[j]? = some e → uint.nat e.Index' = uint.nat e0.Index' + j) :
    (LogEntry.toEntries ce n).drop m0 = es.take (ce.length - m0) ∧
      ce.length - m0 ≤ es.length := by
  constructor
  · apply List.ext_getElem?
    intro i
    rw [List.getElem?_drop, List.getElem?_take]
    by_cases hi : i < ce.length - m0
    · rw [ite_eq_left hi]
      have hci : m0 + i < ce.length := by omega
      obtain ⟨x, hx⟩ : ∃ x, ce[m0 + i]? = some x := ⟨_, List.getElem?_eq_getElem hci⟩
      rw [srv_toEntries_get ce n (m0 + i) x hx]
      have h1 := Hin (m0 + i) x hx (by omega)
      rw [show n + 1 + (m0 + i) - uint.nat e0.Index' = i by omega] at h1
      cases hy : es[i]? with
      | none => rw [hy] at h1; cases h1
      | some y =>
        rw [hy] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        subst h1
        have := Hidx i y hy
        have h2 : (W64 ((n : Int) + ((m0 + i : Nat) : Int) + 1)) = y.Index' := by word
        rw [h2]; cases y; rfl
    · rw [ite_eq_right hi]
      have : ce.length ≤ m0 + i := by omega
      unfold LogEntry.toEntries
      rw [List.getElem?_mapIdx, List.getElem?_eq_none this]; rfl
  · apply Nat.le_of_not_lt; intro hc
    have hj : m0 + es.length < ce.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, ce[m0 + es.length]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    have h1 := Hin (m0 + es.length) x hx (by omega)
    rw [show n + 1 + (m0 + es.length) - uint.nat e0.Index' = es.length by omega,
      List.getElem?_eq_none (Nat.le_refl _)] at h1
    cases h1

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

instance srvFrozenAt_persistent (γs : MemStorNames) (i : Nat) :
    Persistent (srvFrozenAt (GF := GF) γs i) := by
  unfold srvFrozenAt; infer_instance

instance srvFrozenRange_persistent (γs : MemStorNames) (lo hi : Nat) :
    Persistent (srvFrozenRange (GF := GF) γs lo hi) := by
  unfold srvFrozenRange; infer_instance

/-- A range from its two parts. -/
theorem srv_memLog_take_drop (γs : MemStorNames) (k : Nat) (dq : DFrac) (l : List EntryM)
    (m : Nat) (hm : m ≤ l.length) :
    memLog (GF := GF) γs k dq (l.take m) ∗ memLog γs (k + m) dq (l.drop m) ⊢ memLog γs k dq l := by
  have h := memLog_app (GF := GF) γs k dq (l.take m) (l.drop m)
  rw [List.take_append_drop, List.length_take_of_le hm] at h
  exact h.2

/-- A frozen range, entry by entry. -/
theorem srvFrozenRange_of_memLog (γs : MemStorNames) :
    ∀ (l : List EntryM) (k : Nat),
      memLog (GF := GF) γs k DFrac.discard l ⊢ srvFrozenRange γs k (k + l.length)
  | [], k => by
    unfold srvFrozenRange
    simp only [List.length_nil, Nat.add_zero, Nat.sub_self, List.range'_zero]
    iintro -
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | x :: xs, k => by
    have h := memLog_app (GF := GF) γs k DFrac.discard [x] xs
    rw [show [x] ++ xs = x :: xs from rfl] at h
    iintro #H
    icases h.1 $$ H with ⟨#H1, #H2⟩
    ihave Hr : [∗list] j ∈ List.range' (k + 1) xs.length, srvFrozenAt (GF := GF) γs j $$ [H2]
    · have hr := srvFrozenRange_of_memLog γs xs (k + 1)
      unfold srvFrozenRange at hr
      rw [show k + 1 + xs.length - (k + 1) = xs.length by omega] at hr
      iapply hr
      iexact H2
    unfold srvFrozenRange
    rw [show k + (x :: xs).length - k = xs.length + 1 by simp, List.range'_succ]
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitr
    rotate_left
    · iexact Hr
    · unfold srvFrozenAt
      iright
      iexists x
      iexact H1

/-- **Freezing a `Ready`'s committed entries** (kvreconf's `batch_freeze`, at the `memLog` level):
from the first `m0` committed entries frozen (`ceFrozen`) and the batch appended at `k`, all of them
frozen, and the batch's frozen prefix `a`. -/
theorem srv_batch_freeze (γs : MemStorNames) (n : Nat) (ce : List LogEntry) (es : List EntryM)
    (m0 k : Nat)
    (Hm : m0 = ce.length ∨ ∃ e0, es.head? = some e0 ∧ n + 1 + m0 = uint.nat e0.Index')
    (Hin : ∀ e0, es.head? = some e0 → ∀ (j : Nat) (e : LogEntry), ce[j]? = some e →
      uint.nat e0.Index' ≤ n + 1 + j →
      Option.map LogEntry.ofEntryM es[n + 1 + j - uint.nat e0.Index']? = some e)
    (Hidx : ∀ e0, es.head? = some e0 → ∀ j e, es[j]? = some e →
      uint.nat e.Index' = uint.nat e0.Index' + j)
    (Hk : ∀ e0, es.head? = some e0 → k = uint.nat e0.Index') :
    ⊢ memLog (GF := GF) γs (n + 1) DFrac.discard ((LogEntry.toEntries ce n).take m0) -∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) ==∗
      memLog γs (n + 1) DFrac.discard (LogEntry.toEntries ce n) ∗ ∃ a : List EntryM,
        ⌜(a ≠ [] → k - 1 + a.length ≤ n + ce.length) ∧ a <+: es⌝ ∗
        (if es = [] then emp else memLog γs k DFrac.discard a ∗
          memLog γs (k + a.length) (DFrac.own 1) (es.drop a.length) ∗ memEnd γs (k + es.length)) := by
  iintro #Hm0 Hb
  by_cases hall : ce.length ≤ m0
  · rw [List.take_of_length_le (by rw [srv_toEntries_length]; exact hall)] at *
    imodintro
    iframe Hm0
    iexists []
    isplitr
    · ipureintro; exact ⟨fun h => absurd rfl h, List.nil_prefix⟩
    by_cases he : es = []
    · subst he; simp only [ite_true]; iexact Hb
    · simp only [ite_eq_right he, List.length_nil, Nat.add_zero, List.drop_zero]
      icases Hb with ⟨Hl, He⟩
      iframe Hl He
      iapply memLog_nil
  · have hlt : m0 < ce.length := Nat.lt_of_not_le hall
    obtain ⟨e0, hh, hm⟩ : ∃ e0, es.head? = some e0 ∧ n + 1 + m0 = uint.nat e0.Index' := by
      rcases Hm with h | h
      · omega
      · exact h
    have hne : es ≠ [] := by intro h; subst h; cases hh
    obtain ⟨Htail, Hle⟩ := srv_batch_tail n ce es m0 e0 hh hm (Hin e0 hh) (Hidx e0 hh)
    have hk := Hk e0 hh
    simp only [ite_eq_right hne]
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
    · iapply srv_memLog_take_drop γs _ DFrac.discard _ m0
        (by rw [srv_toEntries_length]; exact Nat.le_of_lt hlt)
      iframe Hm0
      rw [Htail, show n + 1 + m0 = k by omega]
      iexact Ha
    iexists es.take (ce.length - m0)
    isplitr
    · ipureintro
      refine ⟨fun _ => ?_, List.take_prefix _ _⟩
      rw [hlen]; omega
    rw [hlen]
    iframe Ha Hrest He

/-- **The loop's freeze before `Advance`** (at the server's storage model): the `Ready`'s
`ceFrozen` and the append's receipt (nothing frozen, `rnAppendReceipt`'s) give the committed
entries' frozen range, `n + 1 .. n + |ce|` (`raftAdvancedC`'s payload), and `Advance`'s receipt
past the committed log `n + |ce|` long (`advReceipt none`, with the batch's frozen prefix). -/
theorem rn_freeze_receipt [MemStorReg GF] (ms : Loc) (γs : MemStorNames) (n : Nat)
    (ce : List LogEntry) (es : List EntryM)
    (Hin : ∀ e0, es.head? = some e0 → ∀ (j : Nat) (e : LogEntry), ce[j]? = some e →
      uint.nat e0.Index' ≤ n + 1 + j →
      Option.map LogEntry.ofEntryM es[n + 1 + j - uint.nat e0.Index']? = some e)
    (Hidx : ∀ e0, es.head? = some e0 → ∀ j e, es[j]? = some e →
      uint.nat e.Index' = uint.nat e0.Index' + j) :
    ⊢ memStorReg (GF := GF) ms γs -∗
      ceFrozen (memStorIface ms) n (LogEntry.toEntries ce n) es -∗
      appendReceipt (memStorIface ms) es [] ==∗
      srvFrozenRange γs (n + 1) (n + 1 + ce.length) ∗
      advReceipt (memStorIface ms) (n + ce.length) es none := by
  iintro #Hreg #Hcf Hrc
  iunfold ceFrozen at Hcf
  icases Hcf with ⟨%m0, #Hm0, %Hm⟩
  ihave #Hm0 := memStorLog_to ms γs _ _ _ $$ Hreg Hm0
  have Hm' : m0 = ce.length ∨ ∃ e0, es.head? = some e0 ∧ n + 1 + m0 = uint.nat e0.Index' := by
    rw [srv_toEntries_length] at Hm; exact Hm
  -- the batch appended at its first index (`k`), or nothing
  obtain ⟨k, Hk⟩ : ∃ k : Nat, ∀ e0, es.head? = some e0 → k = uint.nat e0.Index' := by
    cases es with
    | nil => exact ⟨0, fun _ h => by cases h⟩
    | cons x xs => exact ⟨uint.nat x.Index', fun e0 h => by cases h; rfl⟩
  ihave Hb : (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length))
    $$ [Hrc]
  · iunfold appendReceipt at Hrc
    by_cases he : es = []
    · simp only [ite_eq_left he]; iempintro
    simp only [ite_eq_right he]
    icases Hrc with (%He | ⟨%e0, %b, %Hh, -, Hb, Hend⟩)
    · exact absurd He he
    obtain ⟨hh, hb⟩ := Hh
    simp only [List.nil_append] at hb
    subst hb
    rw [Hk e0 hh]
    ihave Hb := memStorLog_to ms γs _ _ _ $$ Hreg Hb
    ihave Hend := memStorEnd_to ms γs _ $$ Hreg Hend
    simp only [List.length_nil, Nat.add_zero]
    iframe Hb Hend
  imod srv_batch_freeze γs n ce es m0 k Hm' Hin Hidx Hk $$ Hm0 Hb with ⟨#Hall, %a, %Ha, Hr⟩
  imodintro
  isplitr
  · ihave #H := srvFrozenRange_of_memLog γs _ (n + 1) $$ Hall
    rw [show n + 1 + ce.length = n + 1 + (LogEntry.toEntries ce n).length by
      rw [srv_toEntries_length]]
    iexact H
  unfold advReceipt
  iexists a
  isplitl
  · unfold appendReceipt
    by_cases he : es = []
    · ileft; ipureintro; exact he
    · iright
      simp only [ite_eq_right he]
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
      ihave Ha' := memStorLog_of ms γs _ _ _ $$ Hreg Ha'
      ihave Hb' := memStorLog_of ms γs _ _ _ $$ Hreg Hb'
      ihave He' := memStorEnd_of ms γs _ $$ Hreg He'
      iframe Ha' Hb' He'
  · ipureintro
    intro hne e0 he0
    have := Ha.1 hne
    rw [Hk e0 he0] at this
    exact this

/-- The node's running token from its two halves (the loop's and the apply side's, which
`stopped` brings back: `raftNode.onStop` takes the whole). -/
theorem rnRun_join [StorageModel GF] (n : Loc) (γ : Cluster) (N : Namespace) :
    nodeRunning (GF := GF) n γ N (1 : Qp).half ∗ nodeRunning n γ N (1 : Qp).half ⊢
      nodeRunning n γ N 1 := by
  iintro ⟨H1, H2⟩
  have h := ((nodeRunning_fractional (GF := GF) n γ N).fractional (1 : Qp).half (1 : Qp).half).2
  rw [Qp.half_add_half] at h
  iapply h
  iframe H1 H2

end ghost

end EtcdGrove
end Perennial
