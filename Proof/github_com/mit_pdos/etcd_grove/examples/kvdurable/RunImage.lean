/-
Lean-first (no Rocq counterpart).

# A `Ready`'s storage changes on the image (2026-11-01, stage II (j))

`run`'s `dmu` section changes the image as it changes the `MemoryStorage`: the snapshot (if any),
the hard state, the entries. Pure: the image after the changes keeps `openStorage`'s checks
(`KdFileOk`) and holds the batch's durable state (`StorageHolds (readyDurable …)`), from the same
of the image before and facts of the `Ready` (raft's: the hard state's commit at most the log's end
after the batch, the entries starting within the durable log and above the commit, consecutive and
decodable).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.ImageLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `imgAppend` of a non-empty batch starting past the log's start: the log's entries up to the
batch, then the batch. -/
theorem imgAppend_past (I : StorFile) (k : Nat) (es : List EntryM) (hne : es ≠ [])
    (hk : uint.nat I.prev < k) :
    imgAppend I k es = ⟨I.hs, I.snap, I.prev, I.prevTerm,
      I.ents.take (k - (uint.nat I.prev + 1)) ++ es⟩ := by
  unfold imgAppend
  have hl : 0 < es.length := List.length_pos_iff.mpr hne
  rw [if_neg (by intro h; rcases h with h | h; exact hne h; omega)]
  rw [show uint.nat I.prev + 1 - k = 0 by omega, List.drop_zero]

/-- The durable log after a batch without a snapshot whose entries start past the base. -/
theorem next_ents_past (S : RaftState) (t v c : w64) (es : List EntryM) (k : Nat)
    (hne : es ≠ []) (Hidx : ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j)
    (hk : uint.nat S.base.index' < k) :
    (S.next t v c none es).ents = S.ents.take (k - uint.nat S.base.index' - 1) ++ es := by
  obtain ⟨e0, rest, rfl⟩ : ∃ e0 rest, es = e0 :: rest := by
    cases es with
    | nil => exact absurd rfl hne
    | cons a b => exact ⟨a, b, rfl⟩
  have h0 := Hidx 0 e0 rfl
  simp only [RaftState.next, appendEnts]
  have hd : (uint.Z S.base.index' + 1 - uint.Z e0.Index').toNat = 0 := by
    have : uint.Z S.base.index' + 1 ≤ uint.Z e0.Index' := by word
    omega
  rw [hd, List.drop_zero]
  simp only [plogTruncateAppend]
  congr 2
  word

set_option hygiene false in
/-- `word`, with the hypotheses it should not rewrite with cleared. -/
local macro "wd" : tactic => `(tactic| ((try clear H2) <;> (try clear H3) <;> (try clear H8) <;>
  (try clear Hidxm) <;> (try clear Hidx) <;> (try clear Hn) <;> (try clear Hew) <;> (try clear Hwf) <;>
  word))

/-- **The image after a `Ready` without a snapshot** (its hard state set to the `Ready`'s, or the
driver's previous one, `hd'`, and its entries appended) keeps its shape and holds the batch's
durable state. -/
theorem img_ready_ok (M : StorFile) (S : RaftState) (hd' : HardStateM) (es : List EntryM) (k : Nat)
    (Hh : StorageHolds S (kdContents (some M))) (Hok : KdFileOk M)
    (Hc : uint.nat M.hs.Commit' ≤ uint.nat hd'.Commit')
    (Hidx : ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j)
    (Hwf : ∀ e ∈ es, EntWf e)
    (Hfit : es ≠ [] → k + es.length ≤ 2 ^ 61)
    (G8 : uint.nat hd'.Commit' ≤ (readyDurable S hd' none es).last)
    (G9 : es ≠ [] → k ≤ S.last + 1)
    (G17 : es ≠ [] → uint.nat M.hs.Commit' < k) :
    KdFileOk (imgAppend (imgSetHardState M hd') k es) ∧
      StorageHolds (readyDurable S hd' none es)
        (kdContents (some (imgAppend (imgSetHardState M hd') k es))) := by
  obtain ⟨⟨Hsw, Hew, Hel⟩, Hp61, Hlen, Hidxm, Hps, Hsl, Hpc, Hcl, Htie⟩ := Hok
  obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9⟩ := Hh
  simp only [kdContents, StorContents.b, StorContents.commit] at H1 H2 H3 H4 H5 H6 H7 H8 H9
  have Hsc : uint.nat M.snap.Metadata'.Index' ≤ uint.nat M.hs.Commit' := by
    by_cases h0 : M.snap.Metadata'.Index' = W64 0
    · rw [h0]; exact Nat.zero_le _
    · exact (H8 M.snap (by simp only [h0, ↓reduceIte])).2
  -- the image's log ends where `S`'s does
  have HbZ : uint.Z S.base.index' ≤ uint.Z M.prev := H1
  have Hpl : uint.nat M.prev ≤ S.last := by
    unfold plogTermAt at H2
    unfold RaftState.last
    by_cases hlt : uint.Z M.prev < uint.Z S.base.index'
    · wd
    rw [if_neg hlt] at H2
    by_cases heq : uint.Z M.prev = uint.Z S.base.index'
    · wd
    rw [if_neg heq] at H2
    have : (uint.Z M.prev - uint.Z S.base.index' - 1).toNat < S.ents.length := by
      rcases Nat.lt_or_ge (uint.Z M.prev - uint.Z S.base.index' - 1).toNat S.ents.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at H2; cases H2
    wd
  have HMl : M.ents.length = S.last - uint.nat M.prev := by
    rw [H3]; unfold RaftState.entsFrom RaftState.last; simp only [List.length_drop]; wd
  unfold readyDurable at G8 ⊢
  rw [show Option.map (fun x : SnapLoan => x.snap) none = none from rfl] at G8 ⊢
  by_cases hne : es = []
  · -- no entries: only the hard state
    subst hne
    have Hap : imgAppend (imgSetHardState M hd') k [] = imgSetHardState M hd' := by
      unfold imgAppend; rw [if_pos (Or.inl rfl)]
    rw [Hap]
    have Hn : (S.next hd'.Term' hd'.Vote' hd'.Commit' none []).ents = S.ents := by
      simp only [RaftState.next, appendEnts]
    have HnL : (S.next hd'.Term' hd'.Vote' hd'.Commit' none []).last = S.last := by
      unfold RaftState.last; rw [Hn]; rfl
    rw [HnL] at G8
    refine ⟨⟨⟨Hsw, Hew, Hel⟩, Hp61, Hlen, Hidxm, Hps, Hsl, ?_, ?_, Htie⟩, ?_⟩
    · simp only [imgSetHardState]; wd
    · simp only [imgSetHardState]; wd
    · simp only [imgSetHardState]
      simp only [StorageHolds, kdContents, StorContents.b, StorContents.commit]
      refine ⟨H1, ?_, ?_, rfl, rfl, ?_, Nat.le_refl _, ?_, H9⟩
      · rw [Hn]; exact H2
      · unfold RaftState.entsFrom at H3 ⊢; rw [Hn]; exact H3
      · wd
      · intro sv hsv
        obtain ⟨a, b⟩ := H8 sv hsv
        exact ⟨a, by wd⟩
  · -- entries past the log's start
    have hk := G17 hne
    have hkp : uint.nat M.prev < k := by wd
    have hkb : uint.nat S.base.index' < k := by wd
    rw [imgAppend_past _ k es hne (by simp only [imgSetHardState]; exact hkp)]
    have Hn := next_ents_past S hd'.Term' hd'.Vote' hd'.Commit' es k hne Hidx hkb
    have Hk9 := G9 hne
    have Hf := Hfit hne
    have HSl : S.last = uint.nat S.base.index' + S.ents.length := rfl
    have HnL : (S.next hd'.Term' hd'.Vote' hd'.Commit' none es).last = k - 1 + es.length := by
      unfold RaftState.last; rw [Hn]
      have : (S.next hd'.Term' hd'.Vote' hd'.Commit' none es).base = S.base := rfl
      rw [this, List.length_append, List.length_take]; wd
    rw [HnL] at G8
    have Htl : (M.ents.take (k - (uint.nat M.prev + 1))).length = k - (uint.nat M.prev + 1) := by
      rw [List.length_take]; wd
    simp only [imgSetHardState]
    refine ⟨⟨⟨Hsw, ?_, ?_⟩, Hp61, ?_, ?_, Hps, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro e he
      rcases List.mem_append.1 he with h | h
      · exact Hew e (List.mem_of_mem_take h)
      · exact Hwf e h
    · rw [List.length_append, Htl]; wd
    · rw [List.length_append, Htl]; wd
    · intro j e he
      by_cases hj : j < k - (uint.nat M.prev + 1)
      · rw [List.getElem?_append_left (by rw [Htl]; exact hj), List.getElem?_take_of_lt hj] at he
        exact Hidxm j e he
      · rw [List.getElem?_append_right (by rw [Htl]; wd), Htl] at he
        have := Hidx _ e he
        wd
    · rw [List.length_append, Htl]; wd
    · wd
    · rw [List.length_append, Htl]; wd
    · -- the snapshot's entry, at most the commit index, is below the batch
      refine ⟨Htie.1, ?_⟩
      rw [← Htie.2]
      unfold imgTermAt
      by_cases hsp : uint.nat M.snap.Metadata'.Index' ≤ uint.nat M.prev
      · rw [if_pos hsp, if_pos hsp]
      · rw [if_neg hsp, if_neg hsp,
          List.getElem?_append_left (by rw [Htl]; wd), List.getElem?_take_of_lt (by wd)]
    · simp only [StorageHolds, kdContents, StorContents.b, StorContents.commit]
      refine ⟨H1, ?_, ?_, rfl, rfl, ?_, Nat.le_refl _, ?_, H9⟩
      · -- the term at the image's start: `S`'s, below the batch
        rw [Hn]
        unfold plogTermAt at H2 ⊢
        have hb : (S.next hd'.Term' hd'.Vote' hd'.Commit' none es).base = S.base := rfl
        rw [hb]
        by_cases hlt : uint.Z M.prev < uint.Z S.base.index'
        · rw [if_pos hlt] at H2; cases H2
        rw [if_neg hlt] at H2 ⊢
        by_cases heq : uint.Z M.prev = uint.Z S.base.index'
        · rw [if_pos heq] at H2 ⊢; exact H2
        rw [if_neg heq] at H2 ⊢
        rw [List.getElem?_append_left (by rw [List.length_take]; wd),
          List.getElem?_take_of_lt (by wd)]
        exact H2
      · unfold RaftState.entsFrom at H3 ⊢
        have hb : (S.next hd'.Term' hd'.Vote' hd'.Commit' none es).base = S.base := rfl
        rw [hb, Hn, H3]
        have hd : (uint.Z M.prev - uint.Z S.base.index').toNat ≤ k - uint.nat S.base.index' - 1 := by
          wd
        rw [List.drop_append_of_le_length (by rw [List.length_take]; wd), List.drop_take]
        congr 2
        wd
      · wd
      · intro sv hsv
        obtain ⟨a, b⟩ := H8 sv hsv
        exact ⟨a, by wd⟩

/-- A snapshot past the image's commit index is not refused by the image. (2026-11-02, stage II (s):
until then past the durable commit index `S.commit`, kvdurable's first G7; raft's `readyRest_snap`
bounds it by the hard state's, the image's.) -/
theorem img_snap_fresh (M : StorFile) (S : RaftState) (sv : SnapshotM)
    (Hh : StorageHolds S (kdContents (some M)))
    (G7 : uint.nat M.hs.Commit' < uint.nat sv.Metadata'.Index') : ¬ imgSnapStale M sv := by
  intro ⟨h0, hle⟩
  have := holds_snap_commit S M Hh h0
  word

/-- **The image after a `Ready` with a snapshot** (the snapshot applied, the hard state set, the
entries after it appended) keeps its shape and holds the batch's durable state. -/
theorem img_ready_snap_ok (M : StorFile) (S : RaftState) (hd' : HardStateM) (sv : SnapshotM)
    (L : SnapLoan) (es : List EntryM) (HL : L.snap = sv)
    (Hsw : SnapWf sv) (Hpos : 0 < uint.Z sv.Metadata'.Index') (H61 : uint.Z sv.Metadata'.Index' < 2 ^ 61)
    (Hidx : ∀ (j : Nat) (e : EntryM), es[j]? = some e →
      uint.nat e.Index' = uint.nat sv.Metadata'.Index' + 1 + j)
    (Hwf : ∀ e ∈ es, EntWf e)
    (Hfit : uint.nat sv.Metadata'.Index' + 1 + es.length ≤ 2 ^ 61)
    (G7 : uint.nat sv.Metadata'.Index' ≤ uint.nat hd'.Commit')
    (G8 : uint.nat hd'.Commit' ≤ (readyDurable S hd' (some L) es).last) :
    KdFileOk (imgAppend (imgSetHardState (imgApplySnapshot M sv) hd')
        (uint.nat sv.Metadata'.Index' + 1) es) ∧
      StorageHolds (readyDurable S hd' (some L) es)
        (kdContents (some (imgAppend (imgSetHardState (imgApplySnapshot M sv) hd')
          (uint.nat sv.Metadata'.Index' + 1) es))) := by
  subst HL
  have Hi0 : L.snap.Metadata'.Index' ≠ W64 0 := by intro h; rw [h] at Hpos; word
  have Hap : imgAppend (imgSetHardState (imgApplySnapshot M L.snap) hd')
      (uint.nat L.snap.Metadata'.Index' + 1) es =
      ⟨hd', L.snap, L.snap.Metadata'.Index', L.snap.Metadata'.Term', es⟩ := by
    unfold imgAppend
    by_cases hne : es = []
    · subst hne; rw [if_pos (Or.inl rfl)]; rfl
    · have hl : 0 < es.length := List.length_pos_iff.mpr hne
      rw [if_neg (by intro h; rcases h with h | h; exact hne h; simp only [imgSetHardState,
        imgApplySnapshot] at h; omega)]
      simp only [imgSetHardState, imgApplySnapshot, List.take_nil, List.nil_append]
      rw [show uint.nat L.snap.Metadata'.Index' + 1 - (uint.nat L.snap.Metadata'.Index' + 1) = 0 by omega,
        List.drop_zero]
  have Hn : (readyDurable S hd' (some L) es).ents = es ∧
      (readyDurable S hd' (some L) es).base =
        entryID.mk L.snap.Metadata'.Term' L.snap.Metadata'.Index' := by
    unfold readyDurable
    simp only [Option.map_some, RaftState.next, appendEnts]
    refine ⟨?_, trivial⟩
    cases hes : es with
    | nil => rfl
    | cons e0 rest =>
      have h0 := Hidx 0 e0 (by rw [hes]; rfl)
      simp only [plogTruncateAppend]
      rw [show (uint.Z L.snap.Metadata'.Index' + 1 - uint.Z e0.Index').toNat = 0 by word,
        List.drop_zero]
      simp
  obtain ⟨HnE, HnB⟩ := Hn
  have HnL : (readyDurable S hd' (some L) es).last = uint.nat L.snap.Metadata'.Index' + es.length := by
    unfold RaftState.last; rw [HnE, HnB]
  rw [HnL] at G8
  rw [Hap]
  refine ⟨⟨⟨Hsw, Hwf, by word⟩, H61, by word, ?_, by word, by simp only; omega, by word, by simp only; omega,
    ⟨fun h => by simp only at h; rw [h] at Hpos; word,
      by unfold imgTermAt; simp only; rw [if_pos (Nat.le_refl _)]⟩⟩, ?_⟩
  · intro j e he; simp only at he ⊢; exact Hidx j e he
  · simp only [StorageHolds, kdContents, StorContents.b, StorContents.commit, Hi0, ↓reduceIte, HnB, HnE]
    refine ⟨by word, ?_, ?_, ?_, ?_, G7, Nat.le_refl _, ?_, ?_⟩
    · unfold plogTermAt; rw [if_neg (by word), if_pos rfl]
    · unfold RaftState.entsFrom; rw [HnE, HnB]; simp
    · unfold readyDurable; simp only [RaftState.next]
    · unfold readyDurable; simp only [RaftState.next]
    · intro sv' hsv'; cases hsv'; exact ⟨Nat.le_refl _, G7⟩
    · intro h; exact absurd rfl h

/-- The image's log ends where the durable state's does. -/
theorem holds_last (S : RaftState) (M : StorFile) (Hh : StorageHolds S (kdContents (some M))) :
    uint.nat M.prev + M.ents.length = S.last := by
  obtain ⟨H1, H2, H3, -⟩ := Hh
  simp only [kdContents, StorContents.b] at H1 H2 H3
  have HbZ : uint.Z S.base.index' ≤ uint.Z M.prev := H1
  have Hpl : uint.nat M.prev ≤ S.last := by
    unfold plogTermAt at H2
    unfold RaftState.last
    by_cases hlt : uint.Z M.prev < uint.Z S.base.index'
    · word
    rw [if_neg hlt] at H2
    by_cases heq : uint.Z M.prev = uint.Z S.base.index'
    · word
    rw [if_neg heq] at H2
    have : (uint.Z M.prev - uint.Z S.base.index' - 1).toNat < S.ents.length := by
      rcases Nat.lt_or_ge (uint.Z M.prev - uint.Z S.base.index' - 1).toNat S.ents.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at H2; cases H2
    word
  rw [H3]; unfold RaftState.entsFrom RaftState.last at *; simp only [List.length_drop]
  clear H2 H3
  word

@[simp] theorem imgAppend_prev (I : StorFile) (k : Nat) (es : List EntryM) :
    (imgAppend I k es).prev = I.prev := by unfold imgAppend; split <;> rfl
@[simp] theorem imgAppend_hs (I : StorFile) (k : Nat) (es : List EntryM) :
    (imgAppend I k es).hs = I.hs := by unfold imgAppend; split <;> rfl
@[simp] theorem imgAppend_snap (I : StorFile) (k : Nat) (es : List EntryM) :
    (imgAppend I k es).snap = I.snap := by unfold imgAppend; split <;> rfl

/-- The batch's base, without a snapshot, is the durable state's. -/
theorem readyDurable_base_none (S : RaftState) (h : HardStateM) (es : List EntryM) :
    (readyDurable S h none es).base = S.base := rfl

/-- The appended image's entries up to `fz0`, past the batch's start, are the old image's. -/
theorem imgAppend_take (I : StorFile) (k : Nat) (es : List EntryM) (n : Nat)
    (Hn : es ≠ [] → uint.nat I.prev + n < k) (Hn2 : n ≤ I.ents.length) :
    (imgAppend I k es).ents.take n = I.ents.take n := by
  by_cases hne : es = []
  · subst hne; unfold imgAppend; rw [if_pos (Or.inl rfl)]
  · have hk := Hn hne
    rw [imgAppend_past I k es hne (by omega)]
    simp only
    rw [List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take]
    congr 1; omega

/-- **The image's entries past the old frozen bound are the delivered log's** (the image holds the
batch's durable state, whose entries there are the delivered ones). -/
theorem img_frozen_facts (M3 : StorFile) (S' : RaftState) (D' : List LogEntry) (p Dlen fz0 : Nat)
    (Hh3 : StorageHolds S' (kdContents (some M3))) (Hprev : uint.nat M3.prev = p)
    (Hfz0 : Dlen ≤ fz0) (Hpf : p ≤ fz0)
    (HD' : ∀ i, Dlen < i → i ≤ D'.length → ∃ x, D'[i - 1]? = some x ∧
      S'.ents[i - 1 - uint.nat S'.base.index']? = some (x.toEntryM (W64 i))) :
    ∀ i, fz0 < i → i ≤ D'.length → ∃ x, D'[i - 1]? = some x ∧
      M3.ents[i - p - 1]? = some (x.toEntryM (W64 i)) := by
  intro i h1 h2
  obtain ⟨x, hx, hs⟩ := HD' i (by omega) h2
  refine ⟨x, hx, ?_⟩
  obtain ⟨H1, -, H3, -⟩ := Hh3
  simp only [kdContents] at H1 H3
  rw [H3]
  unfold RaftState.entsFrom
  simp only
  rw [List.getElem?_drop, ← hs]
  congr 1
  word

end pure

end kvdurable
end EtcdGrove
end Perennial
