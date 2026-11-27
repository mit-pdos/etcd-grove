/-
Lean-first (no Rocq counterpart).

# Freezing a `Ready`'s committed entries in the raft loop (2026-10-30, the repair; stage P, S-C)

The server's version of kvreconf's `batch_freeze` (`examples/raft/kvreconf/RunBatch.lean`). A `Ready`'s
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

/-- An entry of a frozen range, alone. -/
theorem srv_memLog_get (γs : MemStorNames) (k : Nat) (l : List EntryM) (i : Nat) (x : EntryM)
    (h : l[i]? = some x) :
    memLog (GF := GF) γs k DFrac.discard l ⊢ memLog γs (k + i) DFrac.discard [x] := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 h).1
  have hx : l[i] = x := by
    have := List.getElem?_eq_getElem hi; rw [this] at h; exact Option.some.inj h
  have hl : l = l.take i ++ ([x] ++ l.drop (i + 1)) := by
    have h3 := List.take_append_drop i l
    rw [List.drop_eq_getElem_cons hi, hx] at h3
    exact h3.symm
  have h1 := (memLog_app (GF := GF) γs k DFrac.discard (l.take i) ([x] ++ l.drop (i + 1))).1
  have h2 := (memLog_app (GF := GF) γs (k + (l.take i).length) DFrac.discard [x]
    (l.drop (i + 1))).1
  rw [List.length_take_of_le (Nat.le_of_lt hi)] at h2
  rw [← hl, List.length_take_of_le (Nat.le_of_lt hi)] at h1
  exact h1.trans (sep_elim_right.trans (h2.trans sep_elim_left))

/-- (#11's S3) The committed entries frozen at `k` give their terms entry by entry. -/
theorem srvFrozenTerms_of_memLog (γs : MemStorNames) (k n : Nat) (ce : List EntryModel) :
    memLog (GF := GF) γs k DFrac.discard (LogEntry.toEntries (ce.map EntryModel.toLE) n) ⊢
      srvFrozenTerms γs k ce := by
  have h : □ memLog (GF := GF) γs k DFrac.discard (LogEntry.toEntries (ce.map EntryModel.toLE) n)
      ⊢ srvFrozenTerms γs k ce := by
    unfold srvFrozenTerms
    refine BigSepL.bigSepL_intro fun i m hm => ?_
    have hg := srv_toEntries_get (ce.map EntryModel.toLE) n i m.toLE (by
      rw [List.getElem?_map, hm]; rfl)
    iintro #H
    ileft
    iexists (m.toLE.toEntryM (W64 (n + i + 1)))
    isplitl
    · iapply srv_memLog_get γs k _ i _ hg $$ H
    ipureintro; rfl
  iintro #H
  iapply h
  iexact H

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
      memLog γs (n + 1) DFrac.discard (LogEntry.toEntries ce n) ∗
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
  isplitr
  · iexact Hall
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
theorem rnRun_join [StorageModel GF] (n : NodeH) (γ : Cluster) (N : Namespace) :
    nodeRunning (GF := GF) n γ N (1 : Qp).half ∗ nodeRunning n γ N (1 : Qp).half ⊢
      nodeRunning n γ N 1 := by
  iintro ⟨H1, H2⟩
  have h := ((nodeRunning_fractional (GF := GF) n γ N).fractional (1 : Qp).half (1 : Qp).half).2
  rw [Qp.half_add_half] at h
  iapply h
  iframe H1 H2

/-! ### A snapshot `Ready` (2026-10-31, #3)

The server's copies of kv's `snapAppend_pre`/`snapAppend_post`/`kv_snapReceipt`
(`examples/raft/kv/KvRunSnap.lean`; kvreconf has copies of the first two), at the `MemoryStorage`'s
interface. -/

/-- Before `Append` after a snapshot: the range lent to it (empty, after the dummy), and what is
kept. -/
theorem srv_snapAppend_pre (γs : MemStorNames) (j : Nat) (es : List EntryM) :
    memEnd (GF := GF) γs j ⊢
      (if es = [] then emp else memLog γs j (DFrac.own 1) [] ∗ memEnd γs (j + ([] : List EntryM).length)) ∗
      (if es = [] then memEnd γs j else emp) := by
  iintro He
  by_cases h : es = []
  · simp only [h, ↓reduceIte]
    iframe He
  · simp only [h, ↓reduceIte, List.length_nil, Nat.add_zero]
    iframe He
    iapply memLog_nil

/-- After `Append` after a snapshot: the batch's range, owned, and the storage's end after it. -/
theorem srv_snapAppend_post (γs : MemStorNames) (j : Nat) (es : List EntryM) :
    (if es = [] then emp else memLog (GF := GF) γs j (DFrac.own 1) es ∗ memEnd γs (j + es.length)) ∗
      (if es = [] then memEnd γs j else emp) ⊢
      memLog γs j (DFrac.own 1) es ∗ memEnd γs (j + es.length) := by
  by_cases h : es = []
  · subst h
    simp only [↓reduceIte, List.length_nil, Nat.add_zero]
    iintro ⟨-, He⟩
    iframe He
    iapply memLog_nil
  · simp only [h, ↓reduceIte]
    iintro ⟨⟨Hl, He⟩, -⟩
    iframe Hl He

/-- **`Advance`'s receipt for a snapshot loan** (`snapReceipt`), from `ApplySnapshot`'s and
`Append`'s posts. -/
theorem rn_snapReceipt [MemStorReg GF] (ms : Loc) (γs : MemStorNames) (l : SnapLoan)
    (es : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ ownSnapM l.ptr (DFrac.own (Qp.half 1)) l.snap -∗
      memCompacted γs (uint.nat l.snap.Metadata'.Index') -∗
      memLog γs (uint.nat l.snap.Metadata'.Index') DFrac.discard [memDummy l.snap] -∗
      memLog γs (uint.nat l.snap.Metadata'.Index' + 1) (DFrac.own 1) es -∗
      memEnd γs (uint.nat l.snap.Metadata'.Index' + 1 + es.length) -∗
      snapReceipt (memStorIface ms) l es := by
  iintro #Hrec Hs #Hc #Hd Hl He
  unfold snapReceipt
  iframe Hs
  isplitl []
  · iapply memStorCompacted_of ms γs _ $$ Hrec Hc
  isplitl []
  · iexists memDummy l.snap
    isplitr
    · ipureintro; rfl
    iapply memStorLog_of ms γs _ _ _ $$ Hrec Hd
  ihave Hl := memStorLog_of ms γs _ _ _ $$ Hrec Hl
  ihave He := memStorEnd_of ms γs _ $$ Hrec He
  iframe Hl He

/-- After `ApplySnapshot` at `s`: the snapshot's dummy entry frozen and everything below it
compacted (`raftAdvancedC`'s payload for a snapshot batch, `rnApSnap`). -/
theorem srv_snap_frozen (γs : MemStorNames) (s : Nat) (sv : SnapshotM) :
    memCompacted (GF := GF) γs s ∗ memLog γs s DFrac.discard [memDummy sv] ⊢
      srvFrozenAt γs s ∗ srvFrozenBelow γs s := by
  have hB : □ memCompacted (GF := GF) γs s ⊢ srvFrozenBelow γs s := by
    unfold srvFrozenBelow
    refine BigSepL.bigSepL_intro fun k j hk => ?_
    have hk' : k < s := by
      have := (List.getElem?_eq_some_iff.1 hk).1; simpa using this
    rw [List.getElem?_range hk', Option.some.injEq] at hk
    subst hk
    iintro #Hc
    iright
    iapply memCompacted_mono γs s k (by omega) $$ Hc
  iintro ⟨#Hc, #Hd⟩
  isplitl []
  · unfold srvFrozenAt; iright; iexists memDummy sv; iexact Hd
  iapply hB
  imodintro
  iexact Hc

/-- (2026-10-31, #3) **The frozen terms after a snapshot `Ready`**: the log `A` the snapshot jumps
to, from `lo`, ending at the snapshot's index, its last entry of the snapshot's term:
`ApplySnapshot` compacted everything below the index and froze the dummy entry there, of the
snapshot's term. -/
theorem srvFrozenTerms_snap (γs : MemStorNames) (lo : Nat) (A : List EntryModel) (sv : SnapshotM)
    (hlen : lo + A.length = uint.nat sv.Metadata'.Index' + 1)
    (hlast : Option.map EntryModel.term A.getLast? = some sv.Metadata'.Term') :
    memCompacted (GF := GF) γs (uint.nat sv.Metadata'.Index') ∗
      memLog γs (uint.nat sv.Metadata'.Index') DFrac.discard [memDummy sv] ⊢
      srvFrozenTerms γs lo A := by
  have h : □ (memCompacted (GF := GF) γs (uint.nat sv.Metadata'.Index') ∗
      memLog γs (uint.nat sv.Metadata'.Index') DFrac.discard [memDummy sv]) ⊢
      srvFrozenTerms γs lo A := by
    unfold srvFrozenTerms
    refine BigSepL.bigSepL_intro fun k m hm => ?_
    have hk : k < A.length := (List.getElem?_eq_some_iff.1 hm).1
    iintro #H
    icases H with ⟨#Hc, #Hd⟩
    by_cases hl : k + 1 < A.length
    · iright
      isplitr
      · ipureintro; exact hl
      iapply memCompacted_mono γs _ _ (by omega) $$ Hc
    · ileft
      iexists memDummy sv
      have hk' : lo + k = uint.nat sv.Metadata'.Index' := by omega
      rw [hk']
      iframe Hd
      ipureintro
      have hA : A.getLast? = some m := by
        rw [List.getLast?_eq_getElem?, show A.length - 1 = k by omega, hm]
      rw [hA] at hlast
      simp only [Option.map_some, Option.some.injEq] at hlast
      simp only [memDummy]
      exact hlast.symm
  iintro ⟨#Hc, #Hd⟩
  iapply h
  imodintro
  iframe Hc Hd

/-- (2026-10-31, #3) A snapshot with every pointer set (`ownSnapS`, a `Ready`'s) has what the WAL's
`SaveSnap` takes: its metadata with the pointer fields set (`smPtsV`). -/
theorem srv_ownSnapS_meta (p : Loc) (dq : DFrac) (s : SnapshotM) :
    ownSnapS (GF := GF) p dq s ⊢
      ∃ pm : Loc, p.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} pm ∗
        smPtsV pm dq s.Metadata' := by
  iintro H
  iNamed H
  iexists pm
  iframe HM
  iclear Hpb
  iNamed Hm
  ihave Hc := csSet_A _ _ _ $$ Hc
  iunfold smPtsV
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HC HI HT cI cT Hpb Hc

/-- (wal-link L3, 2026-11-19) A conf state with its `AutoLeave` set, frozen (`csPts … true` at `discard`), is the
canonical wire content of its model: every list, `AutoLeave` set, no unknown fields. -/
theorem srv_csPts_csRoC_set (p : Loc) (c : ConfStateM) :
    csPts (GF := GF) p DFrac.discard c true ⊢
      csRoC p ⟨c.Voters', c.Learners', c.VotersOutgoing', c.LearnersNext', some c.AutoLeave', []⟩ := by
  iunfold csPts
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hnn, #HV, #Hv, #HL, #Hl, #HO, #Ho, #HN, #Hn, #HA, #cA, %Hal, #Hpb⟩
  unfold csRoC
  iexists sv, sl, so, sn, pa
  iframe HV Hv HL Hl HO Ho HN Hn HA Hpb
  isplitr
  · ipureintro; exact Hnn
  iunfold cellRO at cA
  icases cA with (%H | #H)
  · exact absurd H.1 (Hal rfl)
  · simp only [optCell]; iexact H

/-- (wal-link Hm1 route (B), 2026-11-19) **A conf state frozen at `discard`, `AutoLeave` set or not**: its
canonical content at the presence bit `al` of its `AutoLeave` pointer (`walAlC`; a nil pointer reads `false`). -/
theorem srv_csPts_csRoC (p : Loc) (c : ConfStateM) (b : Bool) :
    csPts (GF := GF) p DFrac.discard c b ⊢
      ∃ al : Bool, csRoC p ⟨c.Voters', c.Learners', c.VotersOutgoing', c.LearnersNext', walAlC al c.AutoLeave', []⟩ := by
  iunfold csPts
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hnn, #HV, #Hv, #HL, #Hl, #HO, #Ho, #HN, #Hn, #HA, #cA, %Hal, #Hpb⟩
  iunfold cellRO at cA
  icases cA with (%H | #H)
  · iexists false
    unfold csRoC
    iexists sv, sl, so, sn, pa
    iframe HV Hv HL Hl HO Ho HN Hn HA Hpb
    isplitr
    · ipureintro; exact Hnn
    obtain ⟨hpa, hv⟩ := H
    have hn : walAlC false c.AutoLeave' = none := by rw [hv]; rfl
    rw [hn]
    simp only [optCell]
    ipureintro; exact hpa
  · iexists true
    unfold csRoC
    iexists sv, sl, so, sn, pa
    iframe HV Hv HL Hl HO Ho HN Hn HA Hpb
    isplitr
    · ipureintro; exact Hnn
    simp only [walAlC, Bool.true_or, ite_true, optCell]
    iexact H

/-- (wal-link L3, 2026-11-19; the presence bit `al`, Hm1 route (B)) **The canonical wire content of a snapshot
metadata `md`** with the unknown fields `uf`: every pointer set but the conf state's `AutoLeave`, set as the bit
`al` says (`walAlC`), the conf state canonical (`srv_csPts_csRoC`). -/
def srvSnapMetaC (md : SnapshotMetadataM) (al : Bool) (uf : List w8) : SnapMetaC :=
  ⟨some ⟨md.ConfState'.Voters', md.ConfState'.Learners', md.ConfState'.VotersOutgoing',
    md.ConfState'.LearnersNext', walAlC al md.ConfState'.AutoLeave', []⟩, some md.Index', some md.Term', uf⟩

theorem srvSnapMetaC_model (md : SnapshotMetadataM) (al : Bool) (uf : List w8) :
    (srvSnapMetaC md al uf).model = md := by
  obtain ⟨⟨a, b, c, d, e⟩, i, t⟩ := md
  simp only [srvSnapMetaC, SnapMetaC.model, CSC.model, Option.map_some, Option.getD_some]
  congr 2
  exact walAlC_getD al e

/-- Its record bytes are the canonical ones (`walSnapCanon`) when the conf state is not the zero one. -/
theorem srvSnapMetaC_canon (md : SnapshotMetadataM) (al : Bool) (uf : List w8) (hz : md.ConfState' ≠ walCsZero) :
    storage.metaWalC (srvSnapMetaC md al uf) = walSnapCanon md al := by
  unfold storage.metaWalC walSnapCanon srvSnapMetaC
  simp only [Option.map_some, if_neg hz]
  rfl

/-- (wal-link Hm1 route (B), 2026-11-19) **A metadata `MemoryStorage.CreateSnapshot` made, as the WAL's `SaveSnap`
takes it**: frozen (`metaRoC`) at its canonical content at some presence bit (`smPtsV`'s conf state is set). -/
theorem srv_smPtsV_metaC (pm : Loc) (md : SnapshotMetadataM) :
    smPtsV (GF := GF) pm DFrac.discard md ⊢
      ∃ (al : Bool) (uf : List w8), metaRoC pm (srvSnapMetaC md al uf) := by
  iintro H
  iNamed H
  iunfold csOptA at Hc
  icases Hc with (%Hz | Hc | Hc)
  · exact absurd Hz.1 Hnn.2.1
  all_goals
    ihave ⟨%al, #Hcs⟩ := srv_csPts_csRoC pc _ _ $$ Hc
    iexists al, uf
    unfold metaRoC srvSnapMetaC
    iexists pc, pi, pt
    iframe HC HI HT Hpb
    isplitr
    · ipureintro; exact Hnn.1
    isplitl [Hcs]
    · simp only [csOptC]; iexact Hcs
    isplitr
    · iunfold cellRO at cI
      icases cI with (%H | #H)
      · exact absurd H.1 Hnn.2.2.1
      · simp only [optCell]; iexact H
    · iunfold cellRO at cT
      icases cT with (%H | #H)
      · exact absurd H.1 Hnn.2.2.2
      · simp only [optCell]; iexact H

/-- (wal-link L3, 2026-11-19) **A `Ready`'s snapshot's metadata as the WAL's `SaveSnap` takes it** (F2): frozen
(`metaRoC`) at its canonical content (`srvSnapMetaC`). -/
theorem srv_ownSnapS_metaC (p : Loc) (s : SnapshotM) :
    ownSnapS (GF := GF) p DFrac.discard s ⊢
      ∃ (pm : Loc) (uf : List w8), p.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{DFrac.discard} pm ∗
        metaRoC pm (srvSnapMetaC s.Metadata' true uf) := by
  iintro H
  iNamed H
  iclear Hpb
  iNamed Hm
  iexists pm, uf
  iframe HM
  unfold metaRoC srvSnapMetaC
  iexists pc, pi, pt
  iframe HC HI HT Hpb
  isplitr
  · ipureintro; exact Hnn.1
  isplitl [Hc]
  · simp only [csOptC, walAlC, Bool.true_or, ↓reduceIte]
    iunfold csSet at Hc
    icases Hc with (#Hc | #Hc) <;> iapply srv_csPts_csRoC_set $$ Hc
  isplitr
  · iunfold cellRO at cI
    icases cI with (%H | #H)
    · exact absurd H.1 Hnn.2.2.1
    · simp only [optCell]; iexact H
  · iunfold cellRO at cT
    icases cT with (%H | #H)
    · exact absurd H.1 Hnn.2.2.2
    · simp only [optCell]; iexact H

/-- (wal-link L3, 2026-11-19) **`SaveSnap` of a canonical metadata** (`walSaveSnap_spec` at `srvSnapMetaC md uf`):
the conf state not the zero one, the index below the largest, the record below layer 1's bound. -/
theorem walSaveSnapC_spec [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] (st : GoInterface) (h : WalH GF) (ss : Loc) (si : GoInterfaceOk)
    (hst : st = GoInterface.ok si) (q : Qp) (sn mp : Loc) (dq : DFrac) (md : SnapshotMetadataM) (al : Bool) (uf : List w8)
    (Q : IProp GF) (sized : Bool) (hz : md.ConfState' ≠ walCsZero) (hidx : uint.nat md.Index' < 2 ^ 64 - 1)
    (henc : (walSrvMr.encSnap md al).length < 2 ^ 40) :
    isWalStorage st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ metaRoC mp (srvSnapMetaC md al uf) ∗
          AU <{ ∃∃ (σ : StorContents), walRecs h σ sized ∗
                ⌜uint.nat md.Index' = σ.b → md.Term' = σ.base.term'⌝ }>
            @ WalFs.walAuMask, ∅ <{ walRecs h (walSaveSnap σ md) sized, COMM Q }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ Q ∗
          ∃ i : Nat, walSnapRec h i md }} := by
  have HS := walSaveSnap_spec st h ss si hst q sn mp dq (srvSnapMetaC md al uf) al Q sized
  simp only [srvSnapMetaC_model] at HS
  iintro #Hw
  ihave #HS := HS $$ Hw
  iintro !> %Φ ⟨Ho, Hr, Hsn, #Hm, HAU⟩ HΦ
  iapply HS $$ [Ho Hr Hsn HAU] HΦ
  iframe Ho Hr Hsn Hm HAU
  ipureintro
  refine ⟨⟨rfl, rfl, srvSnapMetaC_canon md al uf hz⟩, Or.inr rfl, hidx, henc⟩

/-- (P5, 2026-11-25) **`SaveSnap` of a canonical metadata, over the history** (`walSaveSnapC_spec` from
`walSaveSnapHist_spec`; P5 (b), 2026-11-26: until then over the records with their history, `walRecsH`):
the snapshot record appended at the history `Hs` the update committed at, synced, its witness at `|Hs|`. -/
theorem walSaveSnapCH_spec [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] (st : GoInterface) (h : WalH GF)
    (ss : Loc) (si : GoInterfaceOk)
    (hst : st = GoInterface.ok si) (q : Qp) (sn mp : Loc) (dq : DFrac) (md : SnapshotMetadataM) (al : Bool) (uf : List w8)
    (Q : WalHist → IProp GF) (sized : Bool) (hz : md.ConfState' ≠ walCsZero) (hidx : uint.nat md.Index' < 2 ^ 64 - 1)
    (henc : (walSrvMr.encSnap md al).length < 2 ^ 40) :
    isWalStorage st h ss ⊢
      {{ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ metaRoC mp (srvSnapMetaC md al uf) ∗
          AU <{ ∃∃ Hs : WalHist, walHistH h Hs sized }>
            @ WalFs.walAuMask, ∅
            <{ walHistH h (Hs ++ [WalOpG.snap md al]) sized, COMM Q Hs }> }}
        (App (Val #(methods si.ty go!"SaveSnap" si.v)) (Val #sn))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗ walStorRd st h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          ∃ Hs : WalHist, Q Hs ∗ (letI := h.W; WalFs.walSyncedLb h.dir h.γ.inc (Hs.length + 1)) ∗
            walSnapRec h Hs.length md }} := by
  have HS := walSaveSnapHist_spec st h ss si hst q sn mp dq (srvSnapMetaC md al uf) al Q sized
  simp only [srvSnapMetaC_model] at HS
  iintro #Hw
  ihave #HS := HS $$ Hw
  iintro !> %Φ ⟨Ho, Hr, Hsn, #Hm, HAU⟩ HΦ
  iapply HS $$ [Ho Hr Hsn HAU] HΦ
  iframe Ho Hr Hsn Hm HAU
  ipureintro
  refine ⟨⟨rfl, rfl, srvSnapMetaC_canon md al uf hz⟩, Or.inr rfl, hidx, henc⟩

/-! ## F2 (wal-link L3, 2026-11-19): a snapshot's conf state at the server's static membership -/

/-- **The voters' conf state, as the WAL's `SaveSnap` takes it**: a conf state of the voters' simple
membership, of a non-empty set of fewer than `2^16` voters, is not the zero one, and a metadata at it encodes
below layer 1's record bound (`walSnapCanon_enc_len`). -/
theorem srv_csF2 (cs : ConfStateM) (vs : GSet w64) (h : confStateIs cs (Membership.simple vs))
    (hne : vs ≠ ∅) (hsz : GMap.size vs < 2 ^ 16) (md : SnapshotMetadataM) (hmd : md.ConfState' = cs) :
    md.ConfState' ≠ walCsZero ∧ ∀ al, (walSrvMr.encSnap md al).length < 2 ^ 40 := by
  subst hmd
  obtain ⟨hv, hvo, hl, hln, -⟩ := h
  have e1 := hv.length_eq
  have e2 := hvo.length_eq
  have e3 := hl.length_eq
  have e4 := hln.length_eq
  simp only [GMap.length_elements, Membership.simple, GMap.size_empty] at e1 e2 e3 e4
  have hpos : 0 < GMap.size vs := by
    rcases Nat.eq_zero_or_pos (GMap.size vs) with h0 | h0
    · exact absurd ((GMap.size_empty_iff vs).1 h0) hne
    · exact h0
  refine ⟨?_, ?_⟩
  · intro hz
    rw [hz] at e1
    simp only [walCsZero, List.length_nil] at e1
    omega
  · intro al
    show (WalEnc.snapEnc (walSnapCanon md al)).length < 2 ^ 40
    exact walSnapCanon_enc_len md al (by omega)

/-- **The server's cluster: a non-empty set of fewer than `2^16` voters** (`srvRaftLogInv`'s). -/
theorem srvRaftLogInv_cfg (γ : ServerRaftNames) :
    srvRaftLogInv (GF := GF) γ ⊢ ⌜γ.raft.cfg ≠ ∅ ∧ GMap.size γ.raft.cfg < 2 ^ 16⌝ := by
  iintro #H
  iunfold srvRaftLogInv at H
  icases H with ⟨-, -, -, -, -, -, %Hv⟩
  obtain ⟨hne, hnd, -, hlen⟩ := Hv
  ipureintro
  unfold SrvRaft.cfg
  refine ⟨?_, by rw [GMap.size_list_to_set _ hnd]; exact hlen⟩
  intro h
  obtain ⟨p, ps', hp⟩ := List.exists_cons_of_ne_nil hne
  have : p ∈ GMap.listToSet γ.raft.vs :=
    (GMap.elem_of_list_to_set p _).2 (by rw [hp]; exact List.mem_cons_self ..)
  rw [h] at this
  exact (GMap.not_elem_of_empty p) this

/-- **A valid snapshot's metadata, as the WAL's `SaveSnap` takes it** (F2): at the server's cluster its conf
state is the voters' (`srv_confAt_simple`): not the zero one, its record below layer 1's bound. -/
theorem srv_snapshotValid_F2 (γ : ServerRaftNames) (cl : Cluster) (hcl : γ.raft.cl = cl) (sv : SnapshotM) :
    letI := srvStor (GF := GF) γ.raft
    srvRaftLogInv (GF := GF) γ ∗ snapshotValid cl sv ⊢
      |={⊤}=> ⌜sv.Metadata'.ConfState' ≠ walCsZero ∧ ∀ al, (walSrvMr.encSnap sv.Metadata' al).length < 2 ^ 40⌝ := by
  letI := srvStor (GF := GF) γ.raft
  subst hcl
  iintro ⟨#Hinv, #Hv⟩
  ihave %Hcfg := srvRaftLogInv_cfg γ $$ Hinv
  iunfold snapshotValid at Hv
  icases Hv with ⟨%l, %m, #Hlb, #Hm, -, %Hf⟩
  imod srv_confAt_simple γ l l.length (Nat.le_refl _) ⊤ (fun _ _ => CoPset.mem_full)
    (fun _ _ => CoPset.mem_full) $$ [Hinv Hlb] with #Hs
  · iframe Hinv Hlb
  ihave %Heq := confAt_agree γ.raft.cl l.length m (Membership.simple γ.raft.cfg) $$ [Hm Hs]
  · iframe Hm Hs
  subst Heq
  imodintro; ipureintro
  exact srv_csF2 _ _ Hf.2.2.2.1 Hcfg.1 Hcfg.2 sv.Metadata' rfl

end ghost

end EtcdGrove
end Perennial
