/- Lean-first (no Rocq counterpart).

# The layout after a cut (`notes/wal-fsext-plan.md`, W2)

Pure. What the invariant holds of a WAL right after a cut's rename (S/wal.go:936):

* `segRecs_snoc`: an extra cut at `|H|` leaves the records of every earlier segment as they were
  (the new segment holds no operation: only its headers).
* `cutLay_abs`: the static relation of the new layout (`cutLay lay |H| g wr`), from the old one with
  its last segment synced and truncated at its stream, the new segment's name above the old ones
  and its bytes (the headers' frames, then zeros) durable. **`sorry`** (next unit).
* `crashOkA_cut`: `crashOkA_rename` with its `hkept` discharged by `crashTo_synced` over the new
  layout: the crash condition the invariant holds from the rename to the directory's fsync.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSynced

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

/-- **The static relation after a cut's rename** (see the file header). The old layout: its last
segment `g0` synced and truncated at its stream (`hlast0`), the history synced (`hm`), its end a cut
position past the last cut (`hcut`). The new segment `g`: named `walFileName sq ix` above every old
name and above every index before `|H|`, its bytes the stream `wr` bytes long (its headers' frames)
then zeros, all durable, its `OsMeta` sized to them; the directory's entries `ents'` the old ones
with `g`'s name. -/
theorem cutLay_abs (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay) (ents ents' : Ents)
    (g : SegG) (wr : Nat) (sq ix : Nat)
    (habs : WalAbsD C Mr d lay ents) (hm : d.m = d.H.length)
    (hlast0 : ∀ g0, lay.segs.getLast? = some g0 →
      g0.bs = (segStream C Mr d lay.cuts lay.cuts.length).map durB)
    (hcut : walCutPos (histM d) d.H.length ∧ ∀ b ∈ lay.cuts, b < d.H.length)
    (hname : g.name = walFileName sq ix ∧ walLastIdx (histM d) + 1 ≤ ix ∧
      ∀ g0 ∈ lay.segs, go.GoStringLt g0.name g.name)
    (hwr : wr = (segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)).length)
    (hbs : g.bs = ((segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)) ++
      List.replicate (g.bs.length - wr) 0).map durB ∧ wr ≤ g.bs.length)
    (hmeta : g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo = g.bs.length ∧
      g.om.hi = g.bs.length)
    (hfit : RecsFit C (recsOfSegs C Mr d.metadata (segsOf (histM d) (lay.cuts ++ [d.H.length]))))
    (hents : walInos ents' = walInos ents ++ [g.ino]) :
    WalAbsD C Mr d (cutLay lay d.H.length g wr) ents' := by
  sorry

/-- **The crash condition from a cut's rename on**: `crashOkA_rename` for the new layout `cutLay`,
whose crashes keeping the rename are those of a synced WAL (`crashTo_synced`). -/
theorem crashOkA_cut (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (lay : WalLay)
    (ents : Ents) (cl : List Claim) (n : Nat) (X : List GoString) (h : NamesH) (x : Nat)
    (e : LogEntry) (c : Ents) (bt : GoString) (g : SegG) (wr : Nat)
    (hok : CrashOk C Mr d lay cl n) (habs : WalAbsD C Mr d lay ents)
    (habs' : WalAbsD C Mr d (cutLay lay d.H.length g wr) c) (hm : d.m = d.H.length)
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
  refine crashOkA_rename C Mr d lay (cutLay lay d.H.length g wr) ents cl n X h x e c bt hok habs
    hdur hcl hcoh hcoh' hs hbt hcur hothers hjr ⟨[g], rfl⟩ rfl
    (fun m' fo hf hn hnames hdir => ?_)
  refine crashTo_synced C Mr d _ c m' fo habs' hm (fun g' hg' => ?_)
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

end cutlay

end WalFs
end EtcdGrove
end Perennial

end
