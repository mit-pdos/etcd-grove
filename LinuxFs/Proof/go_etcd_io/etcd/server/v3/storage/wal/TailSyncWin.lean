/- Lean-first (no Rocq counterpart).

# The fdatasync of a tail in a resize window (I3b; W6 log, nineteenth session; pure)

`sync`'s fdatasync may find the tail in a window (`¬ SegExact`): after `Save`'s writes past the
preallocated size, or after `ReadAll`'s `ZeroToEnd`. The fdatasync makes every byte durable at its
value and the size exact (`syncTail`); below the write position the bytes are the stream's
(`TailWin`'s `ByteOk`), past it zero (`WinZero`, finding 2). So the synced layout is exact once `old`
is those zeros past `wr` (`syncLayW`): for an exact tail `syncLay` keeps `old`, whose bytes past `wr`
the fdatasync made durable unchanged.

* `syncLayW`, `walAbsD_syncW`: the static relation after the window's fdatasync;
* `tailZeros_syncW`, `tailBound_syncW`: F-Z and the record boundary after it.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section syncw
variable [GooseExts]

/-- **The layout after the fdatasync of a tail `g` in a window**: `syncLay`, and `old` zeros past
the write position (the synced bytes there, `WinZero`). -/
def syncLayW (lay : WalLay) (pre : List SegG) (g : SegG) : WalLay :=
  { syncLay lay pre g with old := lay.old.take lay.wr ++ List.replicate (g.bs.length - lay.wr) 0 }

theorem syncOld_length (old : List w8) (wr k : Nat) (hwr : wr ≤ old.length) :
    (old.take wr ++ List.replicate k (0 : w8)).length = wr + k := by
  simp; omega

theorem syncOld_getD_lt (old : List w8) (wr k b : Nat) (hwr : wr ≤ old.length) (hb : b < wr) :
    (old.take wr ++ List.replicate k (0 : w8)).getD b 0 = old.getD b 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; omega), List.getElem?_take, if_pos hb]

theorem syncOld_getD_ge (old : List w8) (wr k b : Nat) (hwr : wr ≤ old.length) (hb : wr ≤ b) :
    (old.take wr ++ List.replicate k (0 : w8)).getD b 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
  simp only [List.getElem?_replicate]
  split <;> rfl

/-- **The fdatasync of a tail in a window keeps the static relation** (the history synced, every
record flushed: `wr` the stream's end), the layout `syncLayW`. -/
theorem walAbsD_syncW {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} (h : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (hx : ¬ SegExact g0) (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) :
    WalAbsD C Mr { d with m := d.H.length } (syncLayW lay pre g0) ents := by
  have hc : ∀ b ∈ lay.cuts, b ≤ d.H.length := fun b hb => by
    have := walCutPos_le (h.cuts.1 b hb); simpa [histM] using this
  have hmapI : (syncLayW lay pre g0).segs.map (·.ino) = lay.segs.map (·.ino) := by
    simp [syncLayW, syncLay, hs, syncTail]
  have hmapN : (syncLayW lay pre g0).segs.map (·.name) = lay.segs.map (·.name) := by
    simp [syncLayW, syncLay, hs, syncTail]
  have hlen : (syncLayW lay pre g0).segs.length = lay.segs.length := by simp [syncLayW, syncLay, hs]
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  have hlast' : (syncLayW lay pre g0).segs.getLast? = some (syncTail g0) := by
    simp [syncLayW, syncLay]
  have hget : ∀ k, (syncLayW lay pre g0).segs[k]? =
      (lay.segs[k]?).map (fun g => if k = pre.length then syncTail g else g) :=
    syncLay_getElem? hs
  have hSm : ∀ k, segStream C Mr { d with m := d.H.length } lay.cuts k =
      segStream C Mr d lay.cuts k := fun _ => rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := h.lastWin g0 hg0
  have hwz := h.winZero g0 hg0 hx
  have hwo : lay.wr ≤ lay.old.length := by omega
  refine { names := ?_, cuts := ?_, nameBound := ?_, cut := h.cut, metas := ?_, intact := ?_,
           last := ?_, synced := ?_, lastSynced := ?_, fit := h.fit, tailStop := ?_,
           nonempty := ?_, cutPos := h.cutPos }
  · rw [hmapI, hmapN]; exact h.names
  · exact ⟨h.cuts.1, h.cuts.2.1, by rw [hlen]; exact h.cuts.2.2⟩
  · intro k g hk
    rw [hget] at hk
    obtain ⟨g1, hg1, rfl⟩ := Option.map_eq_some_iff.1 hk
    obtain ⟨sq, ix, hn, hb⟩ := h.nameBound k g1 hg1
    refine ⟨sq, ix, ?_, hb⟩
    split <;> simp [syncTail, hn]
  · intro g hg
    simp only [syncLayW, syncLay, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · obtain ⟨k1, k2, k3, k4, k5⟩ := h.metas g (by rw [hs]; simp [hg])
      refine ⟨k1, k2, k3, k4, Or.inr ?_⟩
      rcases k5 with k5 | k5
      · obtain rfl := Option.some.inj (hg0.symm.trans k5)
        exfalso
        have hn := h.names.2
        rw [hs, List.map_append, List.pairwise_append] at hn
        exact go.goStringLt_irrefl _ (hn.2.2 _ (List.mem_map_of_mem hg) _ (by simp))
      · exact k5
    · have := h.metas g0 (by rw [hs]; simp)
      refine ⟨?_, ?_, ?_, ?_, Or.inl hlast'⟩ <;>
        simp [syncTail, OsMeta.synced, this.1, this.2.1]
  · intro k g hk hg
    rw [hget] at hg
    obtain ⟨g1, hg1, rfl⟩ := Option.map_eq_some_iff.1 hg
    have hk' : k + 1 < lay.segs.length := hlen ▸ hk
    have hkp : k ≠ pre.length := by rw [hs] at hk'; simp at hk'; omega
    simp only [if_neg hkp]
    exact h.intact k g1 hk' hg1
  · intro g hg
    rw [hlast'] at hg; cases hg
    have hxs : SegExact (syncTail g0) := by
      simp [SegExact, syncTail, OsMeta.synced, (h.metas g0 (by rw [hs]; simp)).1]
    refine ⟨fun _ => ?_, fun hx' => absurd hxs hx'⟩
    unfold TailLast
    simp only [syncLayW, syncLay, hSm] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    refine ⟨Nat.le_refl _, h2, ?_, by rw [syncOld_length _ _ _ hwo]; omega, fun b x hb => ?_, h6,
      ?_, fun hz b hb1 hb2 => ?_⟩
    · rw [syncOld_length _ _ _ hwo]; simp [syncTail]; omega
    · simp only [syncTail, List.getElem?_map] at hb
      cases hb0 : g0.bs[b]? with
      | none => rw [hb0] at hb; cases hb
      | some y =>
        rw [hb0] at hb; simp only [Option.map_some, Option.some.injEq] at hb; subst hb
        by_cases hbw : b < lay.wr
        · rw [syncOld_getD_lt _ _ _ _ hwo hbw]
          exact byteOk_sync (h5 b y hb0 hbw) (fun _ => decide_eq_true hbw)
        · rw [syncOld_getD_ge _ _ _ _ hwo (by omega), hwz b y (by omega) hb0]
          exact byteOk_durB (decide_eq_false hbw) (decide_eq_false hbw)
    · rw [List.take_append_of_le_length (by simp; omega), List.take_take,
        Nat.min_eq_left h6]
      exact h7
    · by_cases hbw : b < lay.wr
      · rw [syncOld_getD_lt _ _ _ _ hwo hbw]; exact h8 hz b hb1 (by omega)
      · exact syncOld_getD_ge _ _ _ _ hwo (by omega)
  · refine ⟨Nat.le_refl _, ?_⟩
    simp only [syncLayW, syncLay, List.take_length]
    rw [htail]; exact Nat.le_refl _
  · exact segStart_le hc _
  · intro hz r len c'
    simp only [syncLayW, syncLay, hSm] at hz ⊢
    have hz0 : lay.z0 = lay.wr := by omega
    apply decStep_zeros_any C true (z := g0.bs.length - lay.wr)
    rw [hz0, List.drop_append_of_le_length (by simp; omega), List.drop_eq_nil_of_le (by simp; omega),
      List.nil_append]
    rfl
  · simp [syncLayW, syncLay]

/-- **F-Z after the window's fdatasync.** -/
theorem tailZeros_syncW {lay : WalLay} {pre : List SegG} {g0 : SegG} (hZ : TailZeros lay)
    (hwo : lay.wr ≤ lay.old.length) : TailZeros (syncLayW lay pre g0) := by
  intro b hb1 hb2
  simp only [syncLayW, syncLay] at hb1 hb2 ⊢
  by_cases hbw : b < lay.wr
  · rw [syncOld_getD_lt _ _ _ _ hwo hbw]; exact hZ b hb1 (by omega)
  · exact syncOld_getD_ge _ _ _ _ hwo (by omega)

/-- **The record boundary after the window's fdatasync** (`tailBound_sync`: it does not read `old`). -/
theorem tailBound_syncW {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) :
    TailBound C Mr { d with m := d.H.length } (syncLayW lay pre g0) :=
  by have := tailBound_sync (pre := pre) habs hs htail; exact this

end syncw

end WalFs
end EtcdGrove
end Perennial

end
