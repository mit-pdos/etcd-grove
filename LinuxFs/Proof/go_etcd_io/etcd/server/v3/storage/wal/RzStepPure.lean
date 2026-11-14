/- Lean-first (no Rocq counterpart).

# A resize's first step on the tail keeps the static relation (I3b, pure)

`notes/wal-fsext-plan.md`, I3b. A resize of the last segment (`cut`'s truncate at the write position,
`ReadAll`'s `ZeroToEnd`) opens a window on it (`SegExact`, `Abs.lean`): here the static relation of a
layout in the window.

* `rzSeg g0 tr tg n`: the tail as the first step of a resize to `tg` announces it (`SegFl.OkR`,
  `rzSeg_ok`);
* `walAbsD_win`: the static relation of a layout whose tail `g` may be in a window (its `OsMeta` around
  its bytes, `TailLast` if exact, `TailWin` and `lo ≤ wr` if not), from the old one;
* `walAbsD_rzStart`: a resize's first step from an exact tail or a window, to a target at or past the
  write position.

The crash condition across the window (`CrashOk`) is not here: see the I3b log (2026-11-14, `wal-tc2`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailStepPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

@[simp] theorem rzMeta_size (tr : Bool) (m : OsMeta) (tg n : Nat) : (rzMeta tr m tg n).size = m.size := by
  show (m.announce _ _ tg).size = _; simp
@[simp] theorem rzMeta_cut (tr : Bool) (m : OsMeta) (tg n : Nat) : (rzMeta tr m tg n).cut = m.cut := by
  show (m.announce _ _ tg).cut = _; simp
@[simp] theorem rzMeta_lo (tr : Bool) (m : OsMeta) (tg n : Nat) : (rzMeta tr m tg n).lo = min m.lo tg := rfl
@[simp] theorem rzMeta_hi (tr : Bool) (m : OsMeta) (tg n : Nat) : (rzMeta tr m tg n).hi = max m.hi tg := rfl

/-- **The tail `g0` as the first step of a resize to `tg` announces it** (`SegFl.OkR`). -/
def rzSeg (g0 : SegG) (tr : Bool) (tg n : Nat) : SegG :=
  { g0 with om := rzMeta tr g0.om tg n,
            bs := g0.bs.take (min g0.om.size tg) ++ rsAnn n (g0.bs.drop (min g0.om.size tg)) }

theorem rzSeg_ok {g0 : SegG} {tr : Bool} {tg n t : Nat} (hlen : g0.bs.length = g0.om.size)
    (hcut : g0.om.cut = none) (hpos : 0 < min g0.om.size tg) :
    SegFl.OkR ⟨t, 0, [], n, g0.om, g0.bs, some (tr, tg)⟩ tr tg (rzSeg g0 tr tg n) :=
  ⟨hlen, hcut, rfl, rfl, hpos⟩

theorem rzSeg_length (g0 : SegG) (tr : Bool) (tg n : Nat) :
    (rzSeg g0 tr tg n).bs.length = g0.bs.length := by
  simp only [rzSeg, List.length_append, List.length_take, rsAnn_length, List.length_drop]; omega

theorem rzSeg_getElem?_lt {g0 : SegG} {tr : Bool} {tg n b : Nat} (hlen : g0.bs.length = g0.om.size)
    (hb : b < min g0.om.size tg) : (rzSeg g0 tr tg n).bs[b]? = g0.bs[b]? := by
  simp only [rzSeg]
  rw [List.getElem?_append_left (by simp only [List.length_take]; omega), List.getElem?_take,
    if_pos hb]

/-- A resize to a target at or past the size leaves the bytes as they were. -/
theorem rzSeg_bs_of_le {g0 : SegG} {tr : Bool} {tg n : Nat} (hlen : g0.bs.length = g0.om.size)
    (h : g0.om.size ≤ tg) : (rzSeg g0 tr tg n).bs = g0.bs := by
  simp only [rzSeg, Nat.min_eq_left h]
  rw [List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega)]
  simp [rsAnn]

/-- **The static relation of a layout whose tail may be in a resize window**: the old relation with
an exact tail `g0`, the new tail `g` of the same name and inode, its `OsMeta` around its bytes, and
the last segment's facts (`TailLast` if exact, `TailWin` and `winLo` if not). -/
theorem walAbsD_win {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 g : SegG} {wr' : Nat}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (hino : g.ino = g0.ino) (hname : g.name = g0.name)
    (hmeta : g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo ≤ g.bs.length ∧
      g.bs.length ≤ g.om.hi)
    (hlast : (SegExact g → TailLast C Mr d (tailLay lay pre g wr') g) ∧
      (¬ SegExact g → TailWin C Mr d (tailLay lay pre g wr') g ∧ g.om.lo ≤ wr')) :
    WalAbsD C Mr d (tailLay lay pre g wr') ents := by
  refine ⟨?_, ?_, ?_, habs.cut, ?_, ?_, ?_, habs.synced, habs.lastSynced, habs.fit, habs.tailStop,
    by simp [tailLay]⟩
  · have h1 := habs.names.1; have h2 := habs.names.2
    rw [hs] at h1 h2
    simp only [tailLay, List.map_append, List.map_cons, List.map_nil] at h1 h2 ⊢
    rw [hino, hname]; exact ⟨h1, h2⟩
  · have h := habs.cuts; rw [hs] at h; simpa [tailLay] using h
  · intro k g' hk
    rcases getElem?_tail_cases hk with ⟨hk1, hk2⟩ | ⟨rfl, rfl⟩
    · exact habs.nameBound k g' (by rw [hs, List.getElem?_append_left hk1]; exact hk2)
    · obtain ⟨sq, ix, h1, h2⟩ := habs.nameBound pre.length g0 (by rw [hs]; simp)
      exact ⟨sq, ix, by rw [hname]; exact h1, h2⟩
  · intro g' hg'
    simp only [tailLay, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · obtain ⟨h1, h2, h3, h4, h5⟩ := habs.metas g' (by rw [hs]; exact List.mem_append_left _ hg')
      refine ⟨h1, h2, h3, h4, h5.elim (fun h => Or.inr ?_) Or.inr⟩
      rw [hs, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at h
      subst h
      exfalso
      have hn := habs.names.2
      rw [hs, List.map_append, List.pairwise_append] at hn
      exact go.goStringLt_irrefl _ (hn.2.2 _ (List.mem_map_of_mem hg') _ (by simp))
    · exact ⟨hmeta.1, hmeta.2.1, hmeta.2.2.1, hmeta.2.2.2, Or.inl (by simp [tailLay])⟩
  · intro k g' hk hg'
    simp only [tailLay, List.length_append, List.length_singleton] at hk
    rcases getElem?_tail_cases hg' with ⟨hk1, hk2⟩ | ⟨hk1, -⟩
    · exact habs.intact k g' (by rw [hs]; simpa using hk) (by rw [hs, List.getElem?_append_left hk1]; exact hk2)
    · omega
  · intro g' hg'
    simp only [tailLay, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq] at hg'
    subst hg'
    exact hlast

/-- **A resize's first step keeps the static relation** (the window opens, or stays open), the target
at or past the write position (`cut` truncates to it, `ZeroToEnd` to `z0 = wr`), the least crash size
the step announces at most `wr` (`min lo tg ≤ wr`: so for `cut`'s and `ZeroToEnd`'s truncate, `tg =
wr`): the bytes below the write position are untouched. From an exact tail or a window (`wal-tc7`). -/
theorem walAbsD_rzStart {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} {tr : Bool} {tg n : Nat}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (hwr : lay.wr ≤ tg) (hlo : min g0.om.lo tg ≤ lay.wr) :
    WalAbsD C Mr d (tailLay lay pre (rzSeg g0 tr tg n) lay.wr) ents := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  obtain ⟨hsz, hcut, hlo0, hhi0, -⟩ := habs.metas g0 (List.mem_of_getLast? hg0)
  have hlen := rzSeg_length g0 tr tg n
  have hl : g0.bs.length = g0.om.size := hsz.symm
  have hW := habs.lastWin g0 hg0
  obtain ⟨hso, hwS, hbo, hwo, hB, hz0, hzS, hzZ⟩ := hW
  refine walAbsD_win habs hs rfl rfl ?_ ⟨fun hx => ?_, fun _ => ?_⟩
  · simp only [rzSeg, rzMeta_size, rzMeta_cut, rzMeta_lo, rzMeta_hi] at hlen ⊢
    rw [hlen]; exact ⟨hsz, hcut, by omega, by omega⟩
  · -- exact: the old tail exact, the target at or past the size, nothing cut off
    have h1 : (rzSeg g0 tr tg n).om.lo = (rzSeg g0 tr tg n).bs.length := hx.1
    have h2 : (rzSeg g0 tr tg n).om.lo = min g0.om.lo tg := rfl
    have h3 : (rzSeg g0 tr tg n).om.hi = (rzSeg g0 tr tg n).bs.length := hx.2
    have h4 : (rzSeg g0 tr tg n).om.hi = max g0.om.hi tg := rfl
    have hex0 : SegExact g0 := ⟨by omega, by omega⟩
    have hle : g0.om.size ≤ tg := by omega
    obtain ⟨hso, hwS, hbo, hwo, hB, hz0, hzS, hzZ⟩ := (habs.last g0 hg0).1 hex0
    have e : rzSeg g0 tr tg n = { g0 with om := rzMeta tr g0.om tg n } := by
      have := rzSeg_bs_of_le (tr := tr) (n := n) hl hle
      simp only [rzSeg] at this ⊢; rw [this]
    rw [e]
    exact ⟨hso, hwS, hbo, hwo, hB, hz0, hzS, hzZ⟩
  · refine ⟨⟨hso, hwS, by simp only [tailLay]; omega, by simp only [tailLay]; omega,
      fun b x hb hbw => ?_, hz0, hzS, hzZ⟩, by simp only [rzSeg, rzMeta_lo]; omega⟩
    simp only [tailLay] at hbw
    rw [rzSeg_getElem?_lt hl (by omega)] at hb
    exact hB b x hb (by omega)

end pure

end WalFs
end EtcdGrove
end Perennial

end
