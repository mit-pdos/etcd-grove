/- Lean-first (no Rocq counterpart).

# The layout after a cut (`notes/wal-fsext-plan.md`, W2)

Pure. What the invariant holds of a WAL right after a cut's rename (S/wal.go:936):

* `segRecs_snoc`: an extra cut at `|H|` leaves the records of every earlier segment as they were
  (the new segment holds no operation: only its headers).
* `cutLay_abs`: the static relation of the new layout (`cutLay lay |H| g wr`), from the old one with
  its last segment synced and truncated at its stream, the new segment's name above the old ones
  and its bytes (the headers' frames, then zeros) durable.
* `crashOkA_cut`: `crashOkA_rename` with its `hkept` discharged by `crashTo_synced` over the new
  layout: the crash condition the invariant holds from the rename to the directory's fsync.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSynced
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutName

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section cutlay
variable [GooseExts]

/-- An extra cut at the end adds an empty segment. -/
theorem segsOf_snoc_end (H : WalHist) (cuts : List Nat) :
    segsOf H (cuts ++ [H.length]) = segsOf H cuts ++ [[]] := by
  unfold segsOf
  rw [show (0 :: (cuts ++ [H.length])) = (0 :: cuts) ++ [H.length] by simp,
    List.zip_append (by simp)]
  simp

theorem length_segsOf (H : WalHist) (cuts : List Nat) : (segsOf H cuts).length = cuts.length + 1 := by
  simp [segsOf]

theorem chainSegs_append_ex (C : WalCodec) :
    ∀ (c : w32) (A B : List (List (w64 × List w8))), ∃ X, chainSegs C c (A ++ B) = chainSegs C c A ++ X
  | c, [], B => ⟨chainSegs C c B, by simp [chainSegs]⟩
  | c, D :: A, B => by
    obtain ⟨X, hX⟩ := chainSegs_append_ex C (crcAfter C c D) A B
    exact ⟨X, by simp [chainSegs, hX]⟩

/-- **An extra cut at the history's end leaves the earlier segments' records.** -/
theorem segRecs_snoc (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) (k : Nat)
    (hk : k ≤ cuts.length) :
    (segRecs C Mr d (cuts ++ [d.H.length])).getD k [] = (segRecs C Mr d cuts).getD k [] := by
  have hN : d.H.length = (histM d).length := by simp [histM]
  rw [segRecs, segRecs, hN, segsOf_snoc_end, segsDs_append]
  obtain ⟨X, hX⟩ := chainSegs_append_ex C 0#32 (segsDs Mr d.metadata true [] (segsOf (histM d) cuts))
    (segsDs Mr d.metadata _ _ [[]])
  rw [hX, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left]
  rw [length_chainSegs, length_segsDs, length_segsOf]
  omega

theorem segStart_snoc {cuts : List Nat} {N k : Nat} (hk : k ≤ cuts.length) :
    segStart (cuts ++ [N]) k = segStart cuts k := by
  unfold segStart
  rw [show (0 :: (cuts ++ [N])) = (0 :: cuts) ++ [N] by simp, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; omega), ← List.getD_eq_getElem?_getD]

theorem segStart_snoc_last (cuts : List Nat) (N : Nat) :
    segStart (cuts ++ [N]) (cuts.length + 1) = N := by
  unfold segStart
  rw [show (0 :: (cuts ++ [N])) = (0 :: cuts) ++ [N] by simp, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp)]
  simp

theorem segStream_snoc (C : WalCodec) (Mr : WalMarshal) (d : WalDur) {cuts : List Nat} {k : Nat}
    (hk : k ≤ cuts.length) :
    segStream C Mr d (cuts ++ [d.H.length]) k = segStream C Mr d cuts k := by
  unfold segStream; rw [segRecs_snoc C Mr d cuts k hk]

/-- **The static relation after a cut's rename** (see the file header). The old layout: its last
segment `g0` synced and truncated at its stream (`hlast0`), the history synced (`hm`), its end a cut
position past the last cut (`hcut`). The new segment `g`: named `walFileName sq ix` above every old
name and above every index before `|H|`, its bytes the stream `wr` bytes long (its headers' frames)
then zeros, all durable, its `OsMeta` sized to them; the directory's entries `ents'` the old ones
with `g`'s name. -/
theorem cutLay_abs (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (ents ents' : Ents)
    (g : SegG) (wr : Nat) (sq ix : Nat)
    (habs : WalAbsD C Mr d lay ents) (hex : TailExact lay) (hm : d.m = d.H.length)
    (hlast0 : ∀ g0, lay.segs.getLast? = some g0 →
      g0.bs = (segStream C Mr d lay.cuts lay.cuts.length).map durB)
    (hcut : walCutPos (histM d) d.H.length ∧ ∀ b ∈ lay.cuts, b < d.H.length)
    (hname : g.name = walFileName sq ix ∧ walLastIdx (histM d) + 1 ≤ ix ∧
      ∀ g0 ∈ lay.segs, go.GoStringLt g0.name g.name)
    (hsq : ∀ g0, lay.segs.getLast? = some g0 → ∃ sq0 ix0, g0.name = walFileName sq0 ix0 ∧ sq = sq0 + 1)
    (hwr : wr = (segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)).length)
    (hbs : g.bs = ((segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)) ++
      List.replicate (g.bs.length - wr) 0).map durB ∧ wr ≤ g.bs.length)
    (hmeta : g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo = g.bs.length ∧
      g.om.hi = g.bs.length)
    (hfit : RecsFit C (recsOfSegs C Mr d.metadata (segsOf (histM d) (lay.cuts ++ [d.H.length]))))
    (hents : walInos ents' = walInos ents ++ [g.ino])
    (hz : g.bs.length - wr = 0 ∨ 8 ≤ g.bs.length - wr) (hix : ix < 2 ^ 64) (hpos : 0 < d.H.length) :
    WalAbsD C Mr d (cutLay lay d.H.length g wr) ents' := by
  have hlen := habs.cuts.2.2
  have hne := habs.nonempty
  have hfirst : lay.first ≤ lay.cuts.length := by
    have : 0 < lay.segs.length := List.length_pos_iff.2 hne
    omega
  have hd : WalDur.mk d.H d.m d.unl d.pur d.cut d.metadata d.named d.sized = d := rfl
  -- the new segment's bytes
  have hgb : ∀ b (h : b < g.bs.length), g.bs[b] = durB ((segStream C Mr d (lay.cuts ++ [d.H.length])
      (lay.cuts.length + 1)).getD b 0) := by
    intro b h
    obtain ⟨hbs1, hbs2⟩ := hbs
    generalize hS : segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1) = S at hwr hbs1 ⊢
    have hl := congrArg List.length hbs1
    simp only [List.length_map, List.length_append, List.length_replicate] at hl
    rw [List.getElem_of_eq hbs1 h, List.getElem_map]
    by_cases hb : b < S.length
    · rw [List.getElem_append_left hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
      rfl
    · rw [List.getElem_append_right (by omega), List.getElem_replicate,
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  refine
    { names := ?_, cuts := ?_, nameBound := ?_, cut := ?_, metas := ?_, intact := ?_,
      last := ?_, synced := ?_, lastSynced := ?_, fit := ?_, tailStop := ?_, nonempty := ?_,
      cutPos := ?_, seqName := ?_ }
  · simp only [cutLay, List.map_append, List.map_cons, List.map_nil]
    refine ⟨by rw [hents, habs.names.1], List.pairwise_append.2 ⟨habs.names.2, by simp, ?_⟩⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb; subst hb
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 ha
    exact hname.2.2 g0 hg0
  · simp only [cutLay, List.mem_append, List.mem_singleton, List.length_append, List.length_singleton]
    refine ⟨fun b hb => ?_, List.pairwise_append.2 ⟨habs.cuts.2.1, by simp, fun a ha b hb => ?_⟩,
      by omega⟩
    · rcases hb with hb | rfl
      · exact habs.cuts.1 b hb
      · simpa [histM] using hcut.1
    · simp only [List.mem_singleton] at hb; subst hb; exact hcut.2 a ha
  · intro k g' hk
    simp only [cutLay] at hk ⊢
    by_cases hkl : k < lay.segs.length
    · rw [List.getElem?_append_left hkl] at hk
      obtain ⟨sq', ix', h1, hix', h2⟩ := habs.nameBound k g' hk
      exact ⟨sq', ix', h1, hix', by rw [segStart_snoc (by omega)]; exact h2⟩
    · rw [List.getElem?_append_right (by omega)] at hk
      have hk0 : k = lay.segs.length := by
        rcases Nat.lt_or_ge (k - lay.segs.length) 1 with h1 | h1
        · omega
        · rw [List.getElem?_eq_none (by simp; omega)] at hk; cases hk
      subst hk0
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      refine ⟨sq, ix, hname.1, hix, fun _ => ?_⟩
      rw [show lay.first + lay.segs.length = lay.cuts.length + 1 by omega, segStart_snoc_last,
        List.take_of_length_le (by simp [histM])]
      exact hname.2.1
  · simp only [cutLay]
    exact ⟨by rw [segStart_snoc hfirst]; exact habs.cut.1, habs.cut.2⟩
  · intro g' hg'
    simp only [cutLay, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := habs.metasEx hex g' hg'
      exact ⟨h1, h2, Nat.le_of_eq h3, Nat.le_of_eq h4.symm, Or.inr ⟨h3, h4⟩⟩
    · exact ⟨hmeta.1, hmeta.2.1, (Nat.le_of_eq hmeta.2.2.1), (Nat.le_of_eq hmeta.2.2.2.symm), Or.inr hmeta.2.2⟩
  · intro k g' hk hg'
    simp only [cutLay, List.length_append, List.length_singleton] at hk hg' ⊢
    have hkl : k < lay.segs.length := by omega
    rw [List.getElem?_append_left hkl] at hg'
    rw [segStream_snoc C Mr d (by omega)]
    by_cases hk1 : k + 1 < lay.segs.length
    · exact habs.intact k g' hk1 hg'
    · have hk' : k = lay.segs.length - 1 := by omega
      have hl : lay.segs.getLast? = some g' := by
        rw [List.getLast?_eq_getElem?, ← hk']; exact hg'
      rw [hlast0 g' hl, show lay.first + k = lay.cuts.length by omega]
  · intro g' hg'
    simp only [cutLay, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq] at hg'
    subst hg'
    refine ⟨fun _ => ?_, fun hne => absurd hmeta.2.2 hne⟩
    simp only [TailLast, cutLay, List.length_append, List.length_singleton, List.length_replicate]
    refine ⟨Nat.le_refl _, by omega, by simp, hbs.2, fun b x hx => ?_, Nat.zero_le _, by simp,
      fun _ b _ hb => by simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hb]⟩
    have hb : b < g.bs.length := (List.getElem?_eq_some_iff.1 hx).1
    have hxe : x = g.bs[b] := ((List.getElem?_eq_some_iff.1 hx).2).symm
    rw [hxe, hgb b hb]
    unfold ByteOk
    by_cases hbw : b < wr
    · simp [hbw]
    · simp only [hbw, decide_false, Bool.false_eq_true, if_false]
      have : (segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)).getD b 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [this]
      refine ⟨[], ?_, by simp, fun _ => rfl, ?_⟩ <;>
        simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hb]
  · simp only [cutLay, List.length_append, List.length_singleton]
    refine ⟨by omega, ?_⟩
    rw [List.take_of_length_le (by omega), hd]
    unfold segStream at hwr
    exact Nat.le_of_eq hwr.symm
  · simp only [cutLay, List.length_append, List.length_singleton]
    rw [segStart_snoc_last]; omega
  · exact hfit
  · intro hz0 r len c'
    simp only [cutLay, List.length_append, List.length_singleton] at hz0 ⊢
    rw [decStep_zeros C true (z := g.bs.length) (by rw [← Nat.sub_zero g.bs.length]; rw [hwr, ← hz0] at hz; simpa using hz) (by simp)]
    simp
  · simp [cutLay]
  · intro b hb
    simp only [cutLay, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact habs.cutPos b hb
    · exact hpos
  · -- the sequence names: the new segment's is the old tail's plus one, `|cuts| + 1`
    intro k g' hk
    simp only [cutLay] at hk ⊢
    by_cases hkl : k < lay.segs.length
    · rw [List.getElem?_append_left hkl] at hk
      exact habs.seqName k g' hk
    · rw [List.getElem?_append_right (by omega)] at hk
      have hk0 : k = lay.segs.length := by
        rcases Nat.lt_or_ge (k - lay.segs.length) 1 with h1 | h1
        · omega
        · rw [List.getElem?_eq_none (by simp; omega)] at hk; cases hk
      subst hk0
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      obtain ⟨g0, hg0⟩ : ∃ g0, lay.segs.getLast? = some g0 := by
        cases h : lay.segs.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
        | some g0 => exact ⟨g0, rfl⟩
      obtain ⟨⟨ix1, hix1⟩, -⟩ := habs.tailSeq g0 hg0
      obtain ⟨sq0, ix0, hn0, rfl⟩ := hsq g0 hg0
      refine ⟨ix, ?_⟩
      rw [hname.1, show lay.first + lay.segs.length = lay.cuts.length + 1 by omega]
      exact walFileName_succ_eq ix (hn0.symm.trans hix1)

/-- **The crash condition from a cut's rename on**: `crashOkA_rename` for the new layout `cutLay`,
whose crashes keeping the rename are those of a synced WAL (`crashTo_synced`). -/
theorem crashOkA_cut (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay)
    (ents : Ents) (cl : List Claim) (n : Nat) (X : List GoString) (h : NamesH) (x : Nat)
    (e : LogEntry) (c : Ents) (bt : GoString) (g : SegG) (wr : Nat)
    (hok : CrashOk C Mr d lay cl n) (habs : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (habs' : WalAbsD C Mr d (cutLay lay d.H.length g wr) c) (hexg : SegExact g) (hm : d.m = d.H.length)
    (hdur : ∀ g ∈ lay.segs, ∀ y ∈ g.bs, y = durB y.1) (hdurg : ∀ y ∈ g.bs, y = durB y.1)
    (hwr : wr = (segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)).length)
    (hz : g.bs.length - wr = 0 ∨ 8 ≤ g.bs.length - wr)
    (hX : ∀ b ∈ X, walNameP b = false)
    (hcl : (lay.j, NameSet.except X, h) ∈ cl) (hcoh : ClaimCoh h lay.j (.except X))
    (hcoh' : ClaimCoh (h.log x e c) lay.j (.except X)) (hs : h.next ≤ e.start)
    (hbt : ∀ b, (NameSet.except X).Mem b → e.op.Writes lay.j b → b = bt) (hcur : h.cur !! bt = none)
    (hothers : ∀ c' ∈ cl, c' ≠ (lay.j, NameSet.except X, h) → c'.1 = lay.j →
      ¬ c'.2.1.Mem bt)
    (hjr : lay.jr ≠ lay.j ∨ lay.nm ≠ bt) :
    CrashOkA C Mr d (cutLay lay d.H.length g wr) (some lay)
      (replClaim (lay.j, NameSet.except X, h) (lay.j, NameSet.except X, h.log x e c) cl) n := by
  refine crashOkA_rename C Mr d lay (cutLay lay d.H.length g wr) ents cl n X h x e c bt hok habs hex
    hdur hcl hcoh hcoh' hs hbt hcur hothers hjr ⟨[g], rfl⟩ rfl
    (fun m' fo hf hn hnames hdir => ?_)
  refine crashTo_synced C Mr d _ c m' fo habs'
    (fun g' hg' => by
      simp only [cutLay, List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.some.injEq] at hg'
      exact hg' ▸ hexg) hm (fun g' hg' => ?_)
    (by simp only [cutLay, List.length_append, List.length_singleton]; exact hwr) ?_ ?_ ?_ hdir hf hn
  · simp only [cutLay, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hdur g' hg'
    · exact hdurg
  · intro b _ hb
    simp only [cutLay, List.length_replicate] at hb ⊢
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hb]
  · simpa [cutLay] using hz
  · show walInos (entsOf m' lay.j) = walInos c
    refine walInos_congr (fun b hb => ?_)
    rw [entsOf_lookup]
    refine hnames b (fun hbX => ?_)
    have := hX b hbX
    rw [hb] at this; cases this

/-- **The layout before the cut is an alternative to the layout after it** (`AltOk`): the same WAL
directory, its segments a strict prefix. -/
theorem altOk_cut (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (ents : Ents)
    (b : Nat) (g : SegG) (wr : Nat) (habs : WalAbsD C Mr d lay ents) :
    AltOk C Mr d (cutLay lay b g wr) lay :=
  ⟨⟨ents, habs⟩, rfl, rfl, rfl, ⟨[g], rfl⟩, by simp [cutLay]⟩

end cutlay

end WalFs
end EtcdGrove
end Perennial

end
