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
* `crashOk_syncW`: the crash condition after it (`crashOk_sync`'s window form: the tail imaged as of
  the last sync, past `wr` a stamp-0 candidate or, past `lo`, zero; W6 log, twentieth session);
* `walsOk_syncW`, `dirKeysOk_syncW`: the invariant's pure conjuncts after it.
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
the write position (the synced bytes there, `WinZero`); below it `old`'s bytes, zero past `old`'s end (a
write past the size makes the tail longer than `old`: W6 log, twenty-fourth session). -/
def syncLayW (lay : WalLay) (pre : List SegG) (g : SegG) : WalLay :=
  { syncLay lay pre g with
    old := (lay.old ++ List.replicate lay.wr 0).take lay.wr ++ List.replicate (g.bs.length - lay.wr) 0 }

theorem syncOld_length (old : List w8) (wr k : Nat) :
    ((old ++ List.replicate wr 0).take wr ++ List.replicate k (0 : w8)).length = wr + k := by
  simp <;> omega

theorem syncOld_getD_lt (old : List w8) (wr k b : Nat) (hb : b < wr) :
    ((old ++ List.replicate wr 0).take wr ++ List.replicate k (0 : w8)).getD b 0 = old.getD b 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; omega), List.getElem?_take, if_pos hb]
  by_cases hbo : b < old.length
  · rw [List.getElem?_append_left hbo]
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, if_pos (by omega),
      List.getElem?_eq_none (show old.length ≤ b by omega)]
    rfl

theorem syncOld_getD_ge (old : List w8) (wr k b : Nat) (hb : wr ≤ b) :
    ((old ++ List.replicate wr 0).take wr ++ List.replicate k (0 : w8)).getD b 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
  simp only [List.getElem?_replicate]
  split <;> rfl

/-- **The fdatasync of a tail in a window keeps the static relation** (the history synced, every
record flushed: `wr` the stream's end), the layout `syncLayW`, the tail's bytes from `wr` on zero
(`WinZero`: given F-Z by `WalAbsD.winZero`; after `ZeroToEnd` from a pending tail, by the handle's
bytes; `wal-tc17`, finding A). -/
theorem walAbsD_syncW {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} (h : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (hx : ¬ SegExact g0) (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length)
    (hwz : WinZero lay g0) :
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
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, -⟩ := h.lastWin g0 hg0
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
    simp only [syncLayW, syncLay, hSm] at h1 h2 h3 h4 h6 h7 h8 ⊢
    refine ⟨Nat.le_refl _, h2, ?_, by rw [syncOld_length _ _ _]; omega, fun b x hb => ?_, h6,
      ?_, fun hz b hb1 hb2 => ?_⟩
    · rw [syncOld_length _ _ _]; simp [syncTail]; omega
    · simp only [syncTail, List.getElem?_map] at hb
      cases hb0 : g0.bs[b]? with
      | none => rw [hb0] at hb; cases hb
      | some y =>
        rw [hb0] at hb; simp only [Option.map_some, Option.some.injEq] at hb; subst hb
        by_cases hbw : b < lay.wr
        · rw [syncOld_getD_lt _ _ _ _ hbw]
          rcases h.low g0 hg0 b y hb0 hbw with ⟨-, hB⟩ | ⟨-, -, hW⟩
          · exact byteOk_sync hB (fun _ => decide_eq_true hbw)
          · simp [ByteOk, hbw, hW.1]
        · rw [syncOld_getD_ge _ _ _ _ (by omega), hwz b y (by omega) hb0]
          exact byteOk_durB (decide_eq_false hbw) (decide_eq_false hbw)
    · rw [List.take_append_of_le_length (by simp; omega), List.take_take,
        Nat.min_eq_left h6, List.take_append_of_le_length h3]
      exact h7
    · by_cases hbw : b < lay.wr
      · rw [syncOld_getD_lt _ _ _ _ hbw]
        by_cases hbo : b < lay.old.length
        · exact h8 hz b hb1 hbo
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      · exact syncOld_getD_ge _ _ _ _ (by omega)
  · refine ⟨Nat.le_refl _, ?_⟩
    simp only [syncLayW, syncLay, List.take_length]
    rw [htail]; exact Nat.le_refl _
  · exact segStart_le hc _
  · intro hz r len c'
    simp only [syncLayW, syncLay, hSm] at hz ⊢
    have hz0 : lay.z0 = lay.wr := by omega
    apply decStep_zeros_any C true (z := g0.bs.length - lay.wr)
    rw [hz0, List.drop_append_of_le_length (by simp <;> omega),
      List.drop_eq_nil_of_le (by simp <;> omega),
      List.nil_append]
    rfl
  · simp [syncLayW, syncLay]

/-- **F-Z after the window's fdatasync.** -/
theorem tailZeros_syncW {lay : WalLay} {pre : List SegG} {g0 : SegG} (hZ : TailZeros lay) :
    TailZeros (syncLayW lay pre g0) := by
  intro b hb1 hb2
  simp only [syncLayW, syncLay] at hb1 hb2 ⊢
  by_cases hbw : b < lay.wr
  · rw [syncOld_getD_lt _ _ _ _ hbw]
    by_cases hbo : b < lay.old.length
    · exact hZ b hb1 hbo
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  · exact syncOld_getD_ge _ _ _ _ (by omega)

/-- **F-Z after the window's fdatasync**, from F-Z or nothing written past the start's frames
(`TailZ0`: a pending tail's, `wal-tc17`). -/
theorem tailZeros_syncW0 {lay : WalLay} {pre : List SegG} {g0 : SegG} (hZ : TailZ0 lay) :
    TailZeros (syncLayW lay pre g0) := by
  rcases hZ with hZ | hZ
  · exact tailZeros_syncW hZ
  · intro b hb1 hb2
    simp only [syncLayW, syncLay] at hb1 hb2 ⊢
    exact syncOld_getD_ge _ _ _ _ (by omega)

/-- **The record boundary after the window's fdatasync** (`tailBound_sync`: it does not read `old`). -/
theorem tailBound_syncW {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) :
    TailBound C Mr { d with m := d.H.length } (syncLayW lay pre g0) :=
  by have := tailBound_sync (pre := pre) habs hs htail; exact this

/-- A candidate list's value as of stamp 0 is one of its candidates' values, or zero (no candidate
stamped 0). -/
theorem valAt0_cases (c : Cands) : valAt c 0 = 0 ∨ ∃ s, (valAt c 0, s) ∈ c := by
  cases h : (c.filter (fun q => decide (q.2 ≤ 0))).getLast? with
  | none => left; unfold valAt; rw [h]; rfl
  | some z =>
    right
    refine ⟨z.2, ?_⟩
    have hzm : z ∈ c := (List.mem_filter.1 (List.mem_of_getLast? h)).1
    unfold valAt
    rw [h]
    exact hzm

/-- **The crash condition after the fdatasync of a tail in a window** (`crashOk_sync`'s window
form): the old condition at the tail imaged as of the last sync (`syncImg`, of the synced size
`|bs| ∈ [lo, hi]`; below `wr` a stamp-0 candidate, `ByteOk`'s head; from `wr` on, past `lo`
a stamp-0 candidate, else a zero candidate or the zero arm past `lo` (`WinHead`)), then `crashTo_tailM` at the raised mark over the
static relation of `syncLayW` (`walAbsD_syncW`). -/
theorem crashOk_syncW {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} {cl : List Claim} {n : Nat} {pre : List SegG} {g0 : SegG}
    (habs0 : WalAbsD C Mr d lay ents) (hs0 : lay.segs = pre ++ [g0]) (hx : ¬ SegExact g0)
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length)
    (hZ : TailZ0 lay) (hwz : WinZero lay g0) (hnd0 : (lay.segs.map (·.ino)).Nodup)
    (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z)
    (hok : CrashOk C Mr d lay cl n) :
    CrashOk C Mr { d with m := d.H.length } (syncLayW lay pre g0) cl n := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs0]; simp
  have hwin := habs0.lastWin g0 hg0
  have habs := walAbsD_syncW habs0 hs0 hx htail hwz
  have hZ' : TailZeros (syncLayW lay pre g0) := tailZeros_syncW0 hZ
  have hB := tailBound_syncW (pre := pre) habs0 hs0 htail
  intro m' fo hr hf hnmd hw
  have hs : (syncLayW lay pre g0).segs = pre ++ [syncTail g0] := rfl
  have hgm : syncTail g0 ∈ (syncLayW lay pre g0).segs := by rw [hs]; simp
  have hg : (syncLayW lay pre g0).segs.getLast? = some (syncTail g0) := by rw [hs]; simp
  have hxs : SegExact (syncTail g0) := by
    simp [SegExact, syncTail, OsMeta.synced, (habs0.metas g0 (List.mem_of_getLast? hg0)).1]
  have hino : (syncTail g0).ino = g0.ino := rfl
  have hinos : (syncLayW lay pre g0).segs.map (·.ino) = lay.segs.map (·.ino) := by
    rw [hs, hs0]; simp [hino]
  have hnd : ((syncLayW lay pre g0).segs.map (·.ino)).Nodup := by rw [hinos]; exact hnd0
  have hpre : ∀ g' ∈ pre, g'.ino ≠ g0.ino := by
    intro g' hg' he
    rw [hs0, List.map_append, List.nodup_append] at hnd0
    exact hnd0.2.2 _ (List.mem_map_of_mem hg') _ (by simp) he
  have hpreX : ∀ g' ∈ pre, SegExact g' := by
    intro g' hg'
    obtain ⟨-, -, -, -, h5⟩ := habs0.metas g' (by rw [hs0]; simp [hg'])
    rcases h5 with h5 | h5
    · rw [hg0] at h5; cases h5; exact absurd rfl (hpre _ hg')
    · exact h5
  let fo0 : Ino → Option Fs.OsFile := fun i =>
    if i = g0.ino then (fo i).map (fun f => syncImg g0.bs f.size) else fo i
  have hfo : ∀ i, i ≠ g0.ino → fo0 i = fo i := fun i hi => by simp [fo0, hi]
  have hfo0g : fo0 g0.ino = (fo g0.ino).map (fun f => syncImg g0.bs f.size) := by simp [fo0]
  have hlen0 : (syncTail g0).bs.length = g0.bs.length := by simp [syncTail]
  have hsyncSz : ∀ f, fo g0.ino = some f → f.size = g0.bs.length := by
    intro f hf1
    obtain ⟨-, hlo, hhi, -, -⟩ := hf (syncTail g0) hgm f hf1
    have hmlo := hxs.1
    have hmhi := hxs.2
    rw [hlen0] at hmlo hmhi
    omega
  -- the old tail's crash, imaged as of the last sync
  have hfc0 : FileCrashedR g0.om [(0, DFrac.own (1 : Qp).half, g0.bs)] (fo0 g0.ino) := by
    rw [hfo0g]
    intro f' hf'
    obtain ⟨f, hf1, rfl⟩ := Option.map_eq_some_iff.1 hf'
    have hsz : f.size = g0.bs.length := hsyncSz f hf1
    have hsz' : (syncImg g0.bs f.size).size = g0.bs.length := hsz
    obtain ⟨hm1, -, hm3, hm4, -⟩ := habs0.metas g0 (List.mem_of_getLast? hg0)
    have hhd := habs0.winHead g0 hg0 hx
    refine ⟨⟨_, rfl⟩, by omega, by omega, ?_, ?_, fun b c hb _ hb2 => absurd hb2 (by omega)⟩
    · intro r hr k hk hks
      rw [List.mem_singleton] at hr; subst hr
      simp only [Nat.zero_add] at hks ⊢
      rw [syncImg_cache g0.bs f.size k (show k < f.size from hks)]
      have e : g0.bs.getD k (0, []) = g0.bs[k]'hk := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      rw [e]
      by_cases hkw : k < lay.wr
      · rcases habs0.low g0 hg0 k (g0.bs[k]'hk) (List.getElem?_eq_getElem hk) hkw with
          ⟨-, hB⟩ | ⟨hl, -, -⟩
        · exact .inl (valAt_mem0 hB.head0)
        · rcases valAt0_cases (g0.bs[k]'hk).2 with h0 | h0
          · exact .inr ⟨hl, h0⟩
          · exact .inl h0
      · rcases valAt0_cases (g0.bs[k]'hk).2 with h0 | h0
        · have hkX : k < (segBytesX g0).length := Nat.lt_of_lt_of_le hk segBytesX_length_le
          rcases hhd k (by omega) hkX with hl | ⟨s0, hs0⟩
          · exact .inr ⟨by omega, h0⟩
          · rw [segBytesX_getD_lt hk, e] at hs0
            exact .inl ⟨s0, by rw [h0]; exact hs0⟩
        · exact .inl h0
    · intro z hz b hzb hb
      have := hzf z hz; omega
  have hf0 : ∀ g' ∈ lay.segs, FileCrashedR g'.om [(0, DFrac.own (1 : Qp).half, g'.bs)]
      (fo0 g'.ino) := by
    intro g' hg'
    rw [hs0, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rw [hfo _ (hpre g' hg')]; exact hf g' (by rw [hs]; simp [hg'])
    · exact hfc0
  have hn0 : ∀ g' ∈ lay.segs, g'.ino ∈ walInos (entsOf m' lay.j) → (fo0 g'.ino).isSome := by
    intro g' hg' hnd'
    rw [hs0, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rw [hfo _ (hpre g' hg')]; exact hnmd g' (by rw [hs]; simp [hg']) hnd'
    · rw [hfo0g, Option.isSome_map]; exact hnmd (syncTail g') (by rw [hs]; simp) hnd'
  have hw0 : W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo0 i)) (segBytesOf lay)
      (segRzOf lay) := by
    apply w1G_sync
    intro i bs hbs b hb
    obtain ⟨g', hg', rfl, rfl⟩ := segBytesOf_some hbs
    have hg'' := hg'
    rw [hs0, List.mem_append, List.mem_singleton] at hg''
    rcases hg'' with hgp | rfl
    · have hX := hpreX g' hgp
      rw [segBytesX_of_hi (Nat.le_of_eq hX.2)]
      rw [hfo _ (hpre g' hgp)] at hb ⊢
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hgp
      have hk' : lay.segs[k]? = some g' := by
        rw [hs0, List.getElem?_append_left ((List.getElem?_eq_some_iff.1 hk).1)]; exact hk
      have hkl : k + 1 < lay.segs.length := by
        have := (List.getElem?_eq_some_iff.1 hk).1; rw [hs0]; simp; omega
      have hint := habs0.intact k g' hkl hk'
      have hdur : ∀ y ∈ g'.bs, y = durB y.1 := by
        rw [hint]; intro y hy; obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
      cases hfg : fo g'.ino with
      | none => simp [imgOf, hfg] at hb
      | some f' =>
        have hfc := hf g' (by rw [hs]; simp [hgp])
        rw [hfg] at hfc
        have hc := img_durable hfc hdur hX.1 hX.2
        simp only [imgOf, hfg, Option.map_some, Option.getD_some, hc] at hb ⊢
        simp only [List.length_map] at hb
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hb,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
        simp only [Option.map_some, Option.getD_some]
        rw [hdur _ (List.getElem_mem hb)]
        exact (valAt_durB _).symm
    · rw [hfo0g] at hb ⊢
      cases hfg : fo g'.ino with
      | none => simp [imgOf, hfg] at hb
      | some f' =>
        have hsz := hsyncSz f' hfg
        simp only [imgOf, hfg, Option.map_some, Option.getD_some, syncImg_length] at hb ⊢
        rw [syncImg_getD _ _ _ hb, segBytesX_getD_lt (by omega)]
  have h0 := hok m' fo0 hr hf0 hn0 hw0
  have h' : CrashTo C Mr d (syncLayW lay pre g0) m' fo0 :=
    crashTo_congr_lay (lay := lay) (lay' := syncLayW lay pre g0) rfl rfl rfl rfl rfl hinos h0
  exact crashTo_tailM hC habs hZ' hB hnd hg hxs d.m habs0.lastSynced h' hfo (hf _ hgm)
    (hnmd _ hgm) hw

/-- `syncLayW` keeps the inodes. -/
theorem syncLayW_inos (lay : WalLay) (pre : List SegG) (g0 : SegG) (hs : lay.segs = pre ++ [g0]) :
    (syncLayW lay pre g0).segs.map (·.ino) = lay.segs.map (·.ino) :=
  syncLay_inos lay pre g0 hs

/-- **`WalsOk` after the fdatasync of a tail in a window** (`walsOk_sync`'s window form). -/
theorem walsOk_syncW {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (hZ : TailZ0 lay)
    (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z) (hx : ¬ SegExact g0) (hwz : WinZero lay g0)
    (hok : CrashOk C Mr d lay cl n) :
    WalsOk C Mr R jr (walSyncS s dir d) (<[dir := syncLayW lay pre g0]> Ls) cl n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hW
  have hsub : ∀ dir' lay', (<[dir := syncLayW lay pre g0]> Ls) !! dir' = some lay' →
      ∃ lay1, Ls !! dir' = some lay1 ∧ (lay'.segs.map (·.ino)).Sublist (lay1.segs.map (·.ino)) := by
    intro dir' lay' h
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at h; cases h
      exact ⟨lay, hl, by rw [syncLayW_inos lay pre g0 hs]; exact List.Sublist.refl _⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h
      exact ⟨lay', h, List.Sublist.refl _⟩
  refine ⟨fun dir' d' hd' => ?_, fun dir' hn => ?_, segsAll_nodup_sub h3 hsub, fun g' hg' => ?_,
    fun dir' nm hin hn => ?_, h6⟩
  · by_cases e : dir' = dir
    · subst e
      rw [walSyncS_lookup] at hd'; cases hd'
      obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, -⟩ := h1 dir' d hd
      have e : lay1 = lay := by rw [hl] at hl1; exact (Option.some.inj hl1).symm
      rw [e] at hjr hnm hc habs
      have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 h3).1 dir' lay hl
      exact ⟨syncLayW lay pre g0, nm, hj, GMap.lookup_insert _ _ _, hA, hjr, hnm, hc,
        walAbsD_syncW habs hs hx htail hwz,
        ⟨none, (fun _ h => nomatch h), (crashOkA_none_iff _ _ _ _ _ _).2
          (crashOk_syncW hC habs hs hx htail hZ hwz hnd hzf hok)⟩⟩
    · rw [walSyncS_lookup_ne s dir d e] at hd'
      obtain ⟨lay1, nm, hj, hl1, rest⟩ := h1 dir' d' hd'
      exact ⟨lay1, nm, hj, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl1, rest⟩
  · have e : dir' ≠ dir := by rintro rfl; rw [walSyncS_lookup] at hn; cases hn
    rw [walSyncS_lookup_ne s dir d e] at hn
    rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact h2 dir' hn
  · obtain ⟨dir', lay', hl', hg''⟩ := segsAll_mem hg'
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      simp only [syncLayW, syncLay, List.mem_append, List.mem_singleton] at hg''
      rcases hg'' with hg'' | rfl
      · exact h4 g' (mem_segsAll hl (by rw [hs]; exact List.mem_append_left _ hg''))
      · exact h4 g0 (mem_segsAll hl (by rw [hs]; simp))
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact h4 g' (mem_segsAll hl' hg'')
  · have e : dir' ≠ dir := by rintro rfl; rw [walSyncS_lookup] at hn; cases hn
    rw [walSyncS_lookup_ne s dir d e] at hn
    exact h5 dir' nm hin hn

/-- **The directory keys after the fdatasync of a tail in a window**, no cut pending
(`dirKeysOk_sync`'s window form). -/
theorem dirKeysOk_syncW {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (hZ : TailZ0 lay)
    (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z) (hx : ¬ SegExact g0) (hwz : WinZero lay g0)
    (h : DirKeysOk C Mr jr s Ls cl n K none) :
    DirKeysOk C Mr jr (walSyncS s dir d) (<[dir := syncLayW lay pre g0]> Ls) cl n K none := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun dir' j X hk => ?_, fun dir' d' lay' hd' hl' hc => ?_, h3.insert hl rfl⟩
  · obtain ⟨lay1, hj, hl1, rest⟩ := h1 dir' j X hk
    by_cases e : dir' = dir
    · subst e; rw [hl] at hl1; cases hl1
      exact ⟨syncLayW lay pre g0, hj, GMap.lookup_insert _ _ _, rest⟩
    · exact ⟨lay1, hj, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl1, rest⟩
  · by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      rw [walSyncS_lookup] at hd'; cases hd'
      obtain ⟨lay1, nm1, hj1, hl1, -, -, -, -, habs, -⟩ := hW.1 dir' d hd
      rw [hl] at hl1; cases hl1
      have hnd : (lay.segs.map (·.ino)).Nodup :=
        ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir' lay hl
      have hok := (crashOkA_none_iff _ _ _ _ _ _).1 (h2 dir' d lay hd hl (by simp))
      exact (crashOkA_none_iff _ _ _ _ _ _).2 (crashOk_syncW hC habs hs hx htail hZ hwz hnd hzf hok)
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      rw [walSyncS_lookup_ne s dir d e] at hd'
      exact h2 dir' d' lay' hd' hl' hc

/-- **The layout after the tail's fdatasync, exact or in a window** (`syncLay`, or `syncLayW` when a
resize window is open): its segments `pre` then the synced tail, the directory, cuts and write
position kept, F-Z, the record boundary, and the invariant's `WalsOk` and directory keys, no cut
pending, at the synced state. -/
theorem syncLay_any {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {dir : GoString}
    {d : WalDur} {lay : WalLay} {ents : Ents} {pre : List SegG} {g0 : SegG}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0])
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (hZ : TailZeros lay)
    (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z) (hK : DirKeysOk C Mr jr s Ls cl n K none)
    (habs : WalAbsD C Mr d lay ents) :
    ∃ L : WalLay, L.segs = pre ++ [syncTail g0] ∧ L.j = lay.j ∧ L.nm = lay.nm ∧
      L.cuts = lay.cuts ∧ L.wr = lay.wr ∧ TailZeros L ∧
      TailBound C Mr { d with m := d.H.length } L ∧
      WalsOk C Mr R jr (walSyncS s dir d) (<[dir := L]> Ls) cl n ∧
      DirKeysOk C Mr jr (walSyncS s dir d) (<[dir := L]> Ls) cl n K none := by
  have hok : CrashOk C Mr d lay cl n :=
    (crashOkA_none_iff _ _ _ _ _ _).1 (hK.2.1 dir d lay hd hl (by simp))
  by_cases hex : SegExact g0
  · exact ⟨syncLay lay pre g0, rfl, rfl, rfl, rfl, rfl, hZ, tailBound_sync habs hs htail,
      walsOk_sync hC hW hd hl hs htail hZ hzf hex hok,
      dirKeysOk_sync hC hW hd hl hs htail hZ hzf hex hK⟩
  · have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
    have hwz := habs.winZero g0 hg0 hex hZ
    exact ⟨syncLayW lay pre g0, rfl, rfl, rfl, rfl, rfl, tailZeros_syncW hZ,
      tailBound_syncW habs hs htail,
      walsOk_syncW hC hW hd hl hs htail (Or.inl hZ) hzf hex hwz hok,
      dirKeysOk_syncW hC hW hd hl hs htail (Or.inl hZ) hzf hex hwz hK⟩

end syncw

end WalFs
end EtcdGrove
end Perennial

end
