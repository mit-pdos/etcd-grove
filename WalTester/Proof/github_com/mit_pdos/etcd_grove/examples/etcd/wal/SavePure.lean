/- Lean-first (no Rocq counterpart).

**`member.save`'s pure vocabulary** (W4c U5): the operation the tester appends (`tSaveOp`), the oracle
after the append (`tSaveO1`) and after the whole call (`tSaveO`, Go's `save` transliterated), and the
member's knowledge of the WAL's last hard state (`tMemHs`: `m.o.lastHS` is the WAL history's
`walLastHS`, which `MustSync` reads on the WAL side; a fact of its own, beside `tMemOk`, so that
`sync`/`close` are unchanged). The facts `save`'s proof needs: the oracle with the operation appended
still accounts for the WAL before the call (`tCandOk_save1`) and for the WAL after it
(`tMemOk_save1`); the tester's `walMustSync` is the WAL's (`tMustSync_iff`); the entries' bounds.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Member
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.toRaft

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI go_etcd_io.raft.v3 WalEnc WalFs

section pure
variable [GooseExts]

/-- `walOp{hs: h, ents: es}`. -/
def tSaveOp (h : THs) (es : List TEnt) : TOp := ⟨false, h, es, W64 0, W64 0⟩

/-- The oracle with the save appended to `since` (what `save` stores first). -/
def tSaveO1 (o : TOracle) (h : THs) (es : List TEnt) : TOracle :=
  { o with since := o.since ++ [tSaveOp h es] }

/-- **The oracle after `save(h, es)`** (wal.go): nothing for an empty save; else the append, the mark
moved if the save syncs, and `lastHS` advanced. -/
def tSaveO (o : TOracle) (h : THs) (es : List TEnt) : TOracle :=
  if tHsEmpty h && es.isEmpty then o else
  { (if tMustSync o.lastHS h es.length then tSynced (tSaveO1 o h es) else tSaveO1 o h es) with
    lastHS := tPhsNext o.lastHS h }

/-- **`m.o.lastHS` is the WAL's last hard state.** -/
def tMemHs (o : TOracle) (d : WalDur) : Prop := absHs o.lastHS = walLastHS (d.H.map WalOpG.toM)

/-- The WAL state after the save's update. -/
def tSaveD (d : WalDur) (h : THs) (es : List TEnt) : WalDur :=
  { d with H := d.H ++ [(WalOpG.save (absHs h) (es.map absEnt)).toRaw] }

theorem absOp_saveOp (h : THs) (es : List TEnt) :
    absOp (tSaveOp h es) = WalOpG.save (absHs h) (es.map absEnt) := rfl

theorem tSaveD_hist (d : WalDur) (h : THs) (es : List TEnt) :
    (tSaveD d h es).H.map WalOpG.toM = d.H.map WalOpG.toM ++ [absOp (tSaveOp h es)] := by
  unfold tSaveD
  rw [List.map_append, List.map_singleton, WalOpG.toM_toRaw, absOp_saveOp]

theorem tSaveOp_wf (h : THs) (es : List TEnt) (hes : ∀ x ∈ es, tEntWf x) (ht : uint.nat h.term' < 2 ^ 63) :
    tOpWf (tSaveOp h es) := by
  unfold tOpWf tSaveOp
  exact ⟨fun hs => absurd hs Bool.false_ne_true, fun _ => hes, fun _ => ht⟩

theorem tSaveO1_hist (o : TOracle) (c : TCand) (h : THs) (es : List TEnt) :
    tCandHist (tSaveO1 o h es) c = tCandHist o c ++ [tSaveOp h es] := by
  unfold tCandHist tSaveO1; simp

theorem tHistWf_snoc {H : List TOp} {op : TOp} (h1 : tHistWf H) (h2 : tOpWf op) : tHistWf (H ++ [op]) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h1 x hx
  · simp at hx; subst hx; exact h2

/-- **The appended oracle accounts for the WAL before the call** (the first store's relation). -/
theorem tCandOk_save1 {o : TOracle} {c : TCand} {d : WalDur} (hok : tMemOk o c d) (h : THs)
    (es : List TEnt) (hes : ∀ x ∈ es, tEntWf x) (ht : uint.nat h.term' < 2 ^ 63)
    (hs : tSim ((tCandHist (tSaveO1 o h es) c).map absOp) (tCandMark o c)) :
    tCandOk (tSaveO1 o h es) c d := by
  obtain ⟨-, -, -, h4, h5, h6, h7, h8, h9, h10, -⟩ := hok
  refine ⟨?_, h5, h6, Nat.le_trans h7 (Nat.le_max_left _ _), h8, ?_, hs⟩
  · rw [tSaveO1_hist, h4]
    refine ⟨(tCandHist o c).length, ?_, ?_, Or.inl ?_⟩
    · unfold tCandMark tCandHist tSaveO1
      simp only [List.length_append]; omega
    · simp
    · rw [List.map_append, List.take_append_of_le_length (by simp)]
      exact (List.take_of_length_le (by simp)).symm
  · rw [tSaveO1_hist]; exact tHistWf_snoc h9 (tSaveOp_wf h es hes ht)

/-- **The appended oracle's candidate is the WAL after the save's update.** -/
theorem tMemOk_save1 {o : TOracle} {c : TCand} {d : WalDur} (hok : tMemOk o c d) (h : THs)
    (es : List TEnt) (hes : ∀ x ∈ es, tEntWf x) (ht : uint.nat h.term' < 2 ^ 63)
    (hs : tSim ((tCandHist (tSaveO1 o h es) c).map absOp) (tCandMark o c)) :
    tMemOk (tSaveO1 o h es) c (tSaveD d h es) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hok
  refine ⟨h1, h2, h3, ?_, h5, h6, h7, h8, ?_, ?_, hs⟩
  · rw [tSaveD_hist, h4, tSaveO1_hist, List.map_append, List.map_singleton]
  · rw [tSaveO1_hist]; exact tHistWf_snoc h9 (tSaveOp_wf h es hes ht)
  · show uint.nat o.synced ≤ (o.since ++ [tSaveOp h es]).length
    simp only [List.length_append, List.length_singleton]; omega

theorem walLastHS_snoc (H : List WalOp) (h : HardStateM) (es : List EntryM) :
    walLastHS (H ++ [WalOpG.save h es]) = phsNext (walLastHS H) h := by
  unfold walLastHS; rw [List.foldl_append]; rfl

/-- **The member's last hard state after the save.** -/
theorem tMemHs_save {o : TOracle} {d : WalDur} (hhs : tMemHs o d) (h : THs) (es : List TEnt)
    (o2 : TOracle) : tMemHs { o2 with lastHS := tPhsNext o.lastHS h } (tSaveD d h es) := by
  unfold tMemHs at *
  rw [tSaveD_hist, absOp_saveOp, walLastHS_snoc, ← hhs, absHs_phsNext]

/-- **The tester's `walMustSync` is the WAL's** (on the member's last hard state). -/
theorem tMustSync_iff {o : TOracle} {d : WalDur} (hhs : tMemHs o d) (h : THs) (es : List TEnt) :
    tMustSync o.lastHS h es.length = true ↔
      walMustSync (d.H.map WalOpG.toM) (absHs h) (es.map absEnt) := by
  unfold tMemHs at hhs
  unfold tMustSync walMustSync hsEmptyP
  rw [← hhs]
  unfold tHsEmpty absHs
  cases es
  · simp only [List.length_nil, List.map_nil]
    by_cases h1 : h.term' = 0#64 <;> by_cases h2 : h.vote' = 0#64 <;> by_cases h3 : h.commit' = 0#64 <;>
      simp [h1, h2, h3]
  · simp

/-- The size of a tester entry's canonical content. -/
theorem absEnt_entrySize_le (e : TEnt) (h0 : 0 < uint.nat e.size') (h : uint.nat e.size' < 2 ^ 40) :
    entrySize (walEntCanon (absEnt e)) ≤ 44 + uint.nat e.size' := by
  unfold walEntCanon entrySize
  have hne := tEntData_ne_nil e h0
  have hl := tEntData_length e
  simp only [absEnt, hne, ↓reduceIte, Option.map_some]
  have h1 := optVarintSize_w64 (uint.Z (W64 (sint.Z (W32 0)))).toNat (by word)
  have h2 := optVarintSize_w64 (uint.Z e.term').toNat (by word)
  have h3 := optVarintSize_w64 (uint.Z e.index').toNat (by word)
  have h4 := varintEnc_length_w64 (tEntData e).length (by omega)
  unfold varintSize
  simp only [List.length_nil]
  omega

/-- **The tester's entries meet `Save`'s bounds**: indices below `2^64 - 1`, encodings below `2^40`. -/
theorem tEnts_saveOk (es : List TEnt) (hes : ∀ x ∈ es, tEntWf x) :
    (∀ e ∈ es.map absEnt, uint.nat e.Index' < 2 ^ 64 - 1) ∧
    (∀ e ∈ es.map absEnt, (walRaftMr.encEntry e).length < 2 ^ 40) := by
  constructor
  · intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    have := (hes x hx).2.2.1
    show uint.nat x.index' < 2 ^ 64 - 1
    omega
  · intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    obtain ⟨h8, h14, -, -⟩ := hes x hx
    have h0 : 0 < uint.nat x.size' := by omega
    have hs : uint.nat x.size' < 2 ^ 40 := by omega
    have hsm := absEnt_small x h0 hs
    have hle := absEnt_entrySize_le x h0 hs
    show (walEncEnt (absEnt x)).length < 2 ^ 40
    rw [(walEncEnt_small hsm).2.2]
    omega

end pure

end etcd_wal
end EtcdGrove
end Perennial
