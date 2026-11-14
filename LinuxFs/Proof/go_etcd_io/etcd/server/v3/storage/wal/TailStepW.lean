/- Lean-first (no Rocq counterpart).

# A `pwrite` step on the tail in a resize window or past the size (W6, pure; W6 log, twenty-third session)

The writer past the preallocated size (a `Save` crossing `SegmentSizeBytes`) and the writes in a resize
window (`cut`'s flush after its truncate, the writes after a write past the size) change the last
segment's ghost as `TailStepPure.lean`'s steps do, but the tail is not exact before or after: the
layout's `OsMeta` of a write in flight is `wrMeta` (the candidates announced past the size, `pwTail`),
its finish `pwPostK true`. Their crash condition is `crashOkW_tailW` (`TailCrashW.lean`) from the two
layouts' static relations; here the pieces of those.

* `wrMeta_pc_ge`: what `wrMeta` knows past the size.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashW
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RzStepPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- **What a write's layout `OsMeta` knows past the size** (`wrMeta`; W6 log, twenty-third session, for the
writer past the size): in the written range, what `m` knew with the data's byte stamped `n` appended
(`pwTail`); past it, what `m` knew (the zeros known moved to the write's end only over the range). -/
theorem wrMeta_pc_ge {m : OsMeta} {off : Nat} {data : List w8} {n b : Nat} (hoff : off ≤ m.size)
    (hb : m.size ≤ b) :
    (wrMeta m off data n).pc b = if off ≤ b ∧ b < off + data.length then
      (m.pc b).map (· ++ [(data.getD (b - off) 0, n)]) else m.pc b := by
  have htc : (wrMeta m off data n).tc !! b = if inRange off (off + data.length) b then
      (m.pc b).map (· ++ [(data.getD (b - off) 0, n)]) else m.tc !! b := by
    show pwTail m off data n !! b = _
    rw [pwTail_lookup]
    by_cases hr : inRange off (off + data.length) b = true
    · rw [if_pos hr, if_pos hr, if_pos hb]
    · rw [if_neg hr, if_neg hr]
  have hzf : (wrMeta m off data n).zf = m.zf.map
      (fun z => if min off m.size < off + data.length then max z (off + data.length) else z) := by
    rw [wrMeta_zf]; unfold cfMeta; rw [announce_zf]
  have hmin : min off m.size = off := Nat.min_eq_left hoff
  rw [hmin] at hzf
  by_cases hin : off ≤ b ∧ b < off + data.length
  · rw [if_pos hin]
    have hr : inRange off (off + data.length) b = true := by simp [inRange, hin.1, hin.2]
    rw [hr, if_pos rfl] at htc
    cases hp : m.pc b with
    | some c =>
      rw [hp] at htc
      unfold OsMeta.pc; rw [htc]; rfl
    | none =>
      rw [hp] at htc
      unfold OsMeta.pc; rw [htc, hzf]
      simp only [Option.map_none]
      cases hz : m.zf with
      | none => rfl
      | some z =>
        simp only [Option.map_some]
        rw [if_pos (show off < off + data.length by omega),
          if_neg (show ¬ max z (off + data.length) ≤ b by omega)]
  · rw [if_neg hin]
    have hr : inRange off (off + data.length) b = false := by
      simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [hr] at htc
    simp only [Bool.false_eq_true, ite_false] at htc
    unfold OsMeta.pc; rw [htc, hzf]
    cases m.tc !! b with
    | some c => rfl
    | none =>
      cases hz : m.zf with
      | none => rfl
      | some z =>
        simp only [Option.map_some]
        have hb' : off + data.length ≤ b := by omega
        split
        · by_cases hzb : z ≤ b
          · rw [if_pos (by omega), if_pos hzb]
          · rw [if_neg (by omega), if_neg hzb]
        · rfl

/-! ## The candidates known past the size -/

/-- `pcRunN` reaches its length when every byte of the run is known. -/
theorem pcRunN_length_eq {m : OsMeta} : ∀ {b k : Nat}, (∀ j, j < k → (m.pc (b + j)).isSome) →
    (pcRunN m b k).length = k
  | _, 0, _ => by simp [pcRunN]
  | b, k + 1, h => by
    unfold pcRunN
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (h 0 (by omega))
    rw [Nat.add_zero] at hc
    rw [hc]
    simp only [List.length_cons]
    rw [pcRunN_length_eq (fun j hj => by rw [show b + 1 + j = b + (j + 1) by omega]; exact h _ (by omega))]

/-- **`TailZ` knows every byte past the size** (`tc` up to the zeros known, then the zeros). -/
theorem TailZ.pc_isSome {m : OsMeta} (h : TailZ m) {b : Nat} (hb : m.size ≤ b) : (m.pc b).isSome := by
  obtain ⟨z, hz, -, -, htc⟩ := h
  unfold OsMeta.pc
  by_cases hbz : b < z
  · obtain ⟨c, hc⟩ := htc b hb hbz
    rw [hc]; rfl
  · cases m.tc !! b with
    | some c => rfl
    | none => rw [hz]; simp only; rw [if_pos (by omega)]; rfl

/-- A byte of `segBytesX g` past `g.bs`, from `g.om.pc`. -/
theorem segBytesX_getD_ge {g : SegG} {b : Nat} (hb : g.bs.length ≤ b) (hbX : b < (segBytesX g).length) :
    ∃ c, g.om.pc b = some c ∧ ((segBytesX g).getD b (0, [])).2 = c := by
  have h := segBytesX_getElem?_ge (g := g) hb (List.getElem?_eq_getElem hbX)
  refine ⟨_, h.2, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbX, Option.getD_some]

/-! ## The announced tail, any write from inside the file -/

/-- **The tail `g0` as the first step of a write of `data` at `off` (inside the file, possibly past its
size) announces it** (`SegFl.Ok`): `segAnn`'s bytes, the `OsMeta` with the candidates announced past the
size (`wrMeta`). For a write inside the size it is `segAnn` (`segAnnW_in`). -/
def segAnnW (g0 : SegG) (off : Nat) (data : List w8) (n : Nat) : SegG :=
  { segAnn g0 off data n with om := wrMeta g0.om off data n }

theorem segAnnW_in {g0 : SegG} {off : Nat} {data : List w8} {n : Nat}
    (hin : off + data.length ≤ g0.om.size) : segAnnW g0 off data n = segAnn g0 off data n := by
  simp only [segAnnW, segAnn, wrMeta_in hin]

theorem segAnnW_ok {g0 : SegG} {off : Nat} {data : List w8} {n t : Nat}
    (hoff : off ≤ g0.om.size) (hd : data ≠ []) (hlen : g0.bs.length = g0.om.size)
    (hcut : g0.om.cut = none) (hoff0 : 0 < off) :
    SegFl.Ok ⟨t, off, data, n, g0.om, g0.bs, none⟩ (segAnnW g0 off data n) :=
  ⟨hoff, hd, hlen, hcut, rfl, rfl, hoff0⟩

/-- The announced tail's bytes (any write from inside the file: its range past the size has no bytes). -/
theorem segAnnW_getElem? {g0 : SegG} {off : Nat} {data : List w8} {n b : Nat}
    (hoff : off ≤ g0.om.size) (hl : g0.bs.length = g0.om.size) :
    (segAnnW g0 off data n).bs[b]? =
      if off ≤ b ∧ b < off + data.length then
        g0.bs[b]?.map (fun x => (x.1, x.2 ++ [(data.getD (b - off) 0, n)]))
      else g0.bs[b]? := by
  have hlo : cfLo g0.om off = off := by unfold cfLo; omega
  have hR : (cfRange g0.om g0.bs off data.length).length = cfHi g0.om off data.length - off := by
    unfold cfRange; rw [hlo]; simp only [List.length_take, List.length_drop, cfHi]; omega
  have hP : (pwAnn data n (cfRange g0.om g0.bs off data.length)).length =
      cfHi g0.om off data.length - off := by rw [pwAnn_length, hR]
  have hhi : cfHi g0.om off data.length = min (off + data.length) g0.om.size := rfl
  show (g0.bs.take (cfLo g0.om off) ++ pwAnn data n (cfRange g0.om g0.bs off data.length) ++
    g0.bs.drop (cfHi g0.om off data.length))[b]? = _
  rw [hlo, getElem?_tpd _ _ off _ b (by omega), hP]
  by_cases h1 : b < off
  · rw [if_pos h1, if_neg (by omega)]
  · rw [if_neg h1]
    by_cases h2 : b < off + (cfHi g0.om off data.length - off)
    · rw [if_pos h2, if_pos ⟨by omega, by omega⟩]
      simp only [pwAnn, List.getElem?_mapIdx]
      unfold cfRange
      rw [hlo, List.getElem?_take, if_pos (by omega), List.getElem?_drop,
        show off + (b - off) = b by omega]
    · rw [if_neg h2]
      have e : cfHi g0.om off data.length + (b - off - (cfHi g0.om off data.length - off)) = b := by omega
      rw [e]
      split
      · rename_i hb
        rw [List.getElem?_eq_none (by omega)]; rfl
      · rfl

theorem segAnnW_length {g0 : SegG} {off : Nat} {data : List w8} {n : Nat}
    (hoff : off ≤ g0.om.size) (hl : g0.bs.length = g0.om.size) :
    (segAnnW g0 off data n).bs.length = g0.bs.length := by
  show (g0.bs.take (cfLo g0.om off) ++ pwAnn data n (cfRange g0.om g0.bs off data.length) ++
    g0.bs.drop (cfHi g0.om off data.length)).length = _
  simp only [List.length_append, List.length_take, List.length_drop, pwAnn_length, cfRange, cfLo, cfHi]
  omega

theorem segAnnW_om (g0 : SegG) (off : Nat) (data : List w8) (n : Nat) :
    (segAnnW g0 off data n).om = wrMeta g0.om off data n := rfl

@[simp] theorem segAnnW_ino (g0 : SegG) (off : Nat) (data : List w8) (n : Nat) :
    (segAnnW g0 off data n).ino = g0.ino := rfl

@[simp] theorem segAnnW_name (g0 : SegG) (off : Nat) (data : List w8) (n : Nat) :
    (segAnnW g0 off data n).name = g0.name := rfl

theorem wrMeta_lo_eq {m : OsMeta} {off : Nat} {data : List w8} {n : Nat} (hlo : m.lo ≤ m.size) :
    (wrMeta m off data n).lo = m.lo := by
  simp only [wrMeta_lo, cfMeta, announce_lo]; omega

theorem wrMeta_hi_eq (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) :
    (wrMeta m off data n).hi = max m.hi (max m.size (off + data.length)) := by
  simp only [wrMeta_hi, cfMeta, announce_hi]

theorem wrMeta_rz_eq (m : OsMeta) (off : Nat) (data : List w8) (n : Nat) :
    (wrMeta m off data n).rz = m.rz := by
  simp [wrMeta_rz, cfMeta]

/-- **A byte of a write's range past the size: what `wrMeta` knows**, from what the tail knew. -/
theorem wrMeta_pc_some {m : OsMeta} {off : Nat} {data : List w8} {n b : Nat} {c : Cands}
    (hoff : off ≤ m.size) (hb : m.size ≤ b) (h : (wrMeta m off data n).pc b = some c) :
    ∃ c0, m.pc b = some c0 ∧ ∀ q ∈ c, q ∈ c0 ∨ (off ≤ b ∧ b < off + data.length ∧
      q = (data.getD (b - off) 0, n)) := by
  rw [wrMeta_pc_ge hoff hb] at h
  split at h
  · rename_i hr
    obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨c0, hc0, fun q hq => ?_⟩
    rcases List.mem_append.1 hq with hq | hq
    · exact .inl hq
    · simp only [List.mem_singleton] at hq; exact .inr ⟨hr.1, hr.2, hq⟩
  · exact ⟨c, h, fun q hq => .inl hq⟩

/-- **The first step of a write from inside the file keeps the static relation**, the tail exact or in a
window (W6 log, twenty-third and twenty-fourth sessions): the write past the synced bytes, of the
intended bytes from there, change number positive; the tail's zeros known past its size (`TailZ`) and
nothing but zeros known past its `hi` (`PastZ`), the handle's; F-Z. Exact and inside the size:
`walAbsD_announce`. Otherwise the window is open after it (`WinLast`): the write raises `hi` past the
size, or the window was open. -/
theorem walAbsD_announceW {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} {off : Nat} {data : List w8} {n : Nat}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0])
    (hso : lay.so ≤ off) (hoff : off ≤ g0.om.size)
    (hpre : data <+: (segStream C Mr d lay.cuts lay.cuts.length).drop off) (hn : 0 < n)
    (hZ : TailZeros lay) (hTZ : TailZ g0.om) (hPZ : PastZ g0.om) :
    WalAbsD C Mr d (tailLay lay pre (segAnnW g0 off data n) lay.wr) ents := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  obtain ⟨hsz, hcut, hlo0, hhi0, -⟩ := habs.metas g0 (List.mem_of_getLast? hg0)
  have hl : g0.bs.length = g0.om.size := hsz.symm
  by_cases hcase : SegExact g0 ∧ off + data.length ≤ g0.om.size
  · rw [segAnnW_in hcase.2]
    exact walAbsD_announce habs hs hcase.1 hso hcase.2 hpre hn
  -- the window after the step
  obtain ⟨g, hgdef⟩ : ∃ g, g = segAnnW g0 off data n := ⟨_, rfl⟩
  rw [← hgdef]
  have hgom : g.om = wrMeta g0.om off data n := by rw [hgdef]; rfl
  have hlen : g.bs.length = g0.bs.length := by rw [hgdef]; exact segAnnW_length hoff hl
  have hglo : g.om.lo = g0.om.lo := by rw [hgom]; exact wrMeta_lo_eq (by omega)
  have hghi : g.om.hi = max g0.om.hi (max g0.om.size (off + data.length)) := by
    rw [hgom]; exact wrMeta_hi_eq _ _ _ _
  have hgrz : g.om.rz = g0.om.rz := by rw [hgom]; exact wrMeta_rz_eq _ _ _ _
  have hgsz : g.om.size = g0.om.size := by rw [hgom]; exact wrMeta_size _ _ _ _
  have hgb : ∀ b, g.bs[b]? = if off ≤ b ∧ b < off + data.length then
      g0.bs[b]?.map (fun x => (x.1, x.2 ++ [(data.getD (b - off) 0, n)])) else g0.bs[b]? :=
    fun b => by rw [hgdef]; exact segAnnW_getElem? hoff hl
  -- a byte of the range is the stream's
  have hdS : ∀ b, off ≤ b → b < off + data.length → data.getD (b - off) 0 = (segStream C Mr d lay.cuts lay.cuts.length).getD b 0 ∧
      b < (segStream C Mr d lay.cuts lay.cuts.length).length := by
    intro b h1 h2
    obtain ⟨e1, e2⟩ := prefix_getD hpre (j := b - off) (by omega)
    rw [show off + (b - off) = b by omega] at e1 e2
    exact ⟨e1, e2⟩
  have hnx : ¬ SegExact g := by
    intro hx
    apply hcase
    have h1 := hx.1; have h2 := hx.2
    rw [hglo, hlen] at h1
    rw [hghi, hlen] at h2
    exact ⟨⟨h1, by omega⟩, by omega⟩
  have hW := habs.lastWin g0 hg0
  obtain ⟨hso', hwS, hz0o, hwb, hB, hz0, hzS, hzZ, hWC⟩ := hW
  have hold := habs.oldHi_any g0 hg0
  have hwlo := habs.winLo_any g0 hg0
  have hzero := habs.zeroPast g0 hg0 hZ
  -- `segBytesX g` reaches `hi`: every byte past the size known
  have hXlen : (segBytesX g).length = g.om.hi := by
    have hk : ∀ j, j < g.om.hi - g.bs.length → (g.om.pc (g.bs.length + j)).isSome := by
      intro j _
      have hb : g0.om.size ≤ g.bs.length + j := by omega
      have := hTZ.pc_isSome hb
      rw [hgom, wrMeta_pc_ge hoff hb]
      split
      · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 this
        rw [hc]; rfl
      · exact this
    simp only [segBytesX, pcRun, List.length_append]
    rw [pcRunN_length_eq hk]; omega
  have hX0 : g0.om.hi ≤ (segBytesX g0).length := hWC.1
  refine walAbsD_win habs hs (by rw [hgdef]; rfl) (by rw [hgdef]; rfl) ⟨by rw [hgsz, hlen]; exact hsz, by rw [hgom]; simp [hcut],
    by rw [hglo, hlen]; exact hlo0, by rw [hghi, hlen]; omega⟩ ⟨fun hx => absurd hx hnx, fun _ => ?_⟩
  refine ⟨⟨hso', hwS, hz0o, by simp only [tailLay]; omega, fun b x hb hbl => ?_, hz0, hzS, hzZ,
      ⟨by omega, fun b hb1 hb2 q hq => ?_⟩⟩, fun b hb1 hb2 => ?_, fun _ b x hb hx => ?_,
    by simp only [tailLay]; omega, by unfold WinLo at hwlo ⊢; simp only [tailLay]; omega,
    fun b x hb hlb hbw => ?_⟩
  · -- `ByteOk` below `lo`: the range's bytes gain the write's candidate
    rw [hglo] at hbl
    simp only [tailLay] at hb ⊢
    rw [hgb b] at hb
    split at hb
    · rename_i hr
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hb
      have hy0 := hB b y hy hbl
      obtain ⟨hdv, hbS⟩ := hdS b hr.1 hr.2
      show ByteOk ((segStream C Mr d lay.cuts lay.cuts.length).getD b 0) (lay.old.getD b 0) (decide (b < (segStream C Mr d lay.cuts lay.cuts.length).length))
        (decide (b < lay.wr)) (decide (b < lay.so)) (y.1, y.2 ++ [(data.getD (b - off) 0, n)])
      rw [show decide (b < lay.so) = false from decide_eq_false (by omega),
        show decide (b < (segStream C Mr d lay.cuts lay.cuts.length).length) = true from decide_eq_true hbS] at hy0 ⊢
      rw [hdv]
      exact ByteOk.ann hy0 rfl hn
    · exact hB b x hb hbl
  · -- `WinCands`: from `wr` on, the old candidates (and past `hi`, `PastZ`) and the write's
    rw [hgrz]
    simp only [tailLay] at hb1
    by_cases hbl : b < g.bs.length
    · rw [segBytesX_getD_lt hbl, List.getD_eq_getElem?_getD, hgb b] at hq
      have hbl0 : b < g0.bs.length := by omega
      have hq0 : ∀ q ∈ (g0.bs.getD b (0, [])).2, WinShape (segStream C Mr d lay.cuts lay.cuts.length) lay.old g0.om.rz b q := by
        intro q hq
        refine hWC.2 b hb1 (Nat.lt_of_lt_of_le hbl0 segBytesX_length_le) q ?_
        rw [segBytesX_getD_lt hbl0]; exact hq
      rw [List.getElem?_eq_getElem hbl0] at hq
      split at hq
      · rename_i hr
        simp only [Option.map_some, Option.getD_some] at hq
        rcases List.mem_append.1 hq with hq | hq
        · apply hq0; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl0]; exact hq
        · simp only [List.mem_singleton] at hq; subst hq
          obtain ⟨hdv, hbS⟩ := hdS b hr.1 hr.2
          exact .inr (.inr ⟨hbS, hdv, hn⟩)
      · simp only [Option.getD_some] at hq
        apply hq0; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl0]; exact hq
    · obtain ⟨c, hc, hce⟩ := segBytesX_getD_ge (by omega) hb2
      rw [hce] at hq
      rw [hgom] at hc
      obtain ⟨c0, hc0, hmem⟩ := wrMeta_pc_some hoff (by omega) hc
      rcases hmem q hq with hq | ⟨h1, h2, rfl⟩
      · by_cases hbh : b < g0.om.hi
        · have hbX0 : b < (segBytesX g0).length := by omega
          obtain ⟨c1, hc1, hce1⟩ := segBytesX_getD_ge (g := g0) (by omega) hbX0
          rw [hc0, Option.some.injEq] at hc1; subst hc1
          exact hWC.2 b hb1 hbX0 q (by rw [hce1]; exact hq)
        · exact hPZ.winShape hold (by omega) hc0 q hq
      · obtain ⟨hdv, hbS⟩ := hdS b h1 h2
        exact .inr (.inr ⟨hbS, hdv, hn⟩)
  · -- `WinHead`: `lo` unchanged; below the size the old candidates are kept
    simp only [tailLay] at hb1 ⊢
    rw [hglo]
    by_cases hbl : b < g0.bs.length
    · have hkeep : ∀ s, ((0 : w8), s) ∈ (g0.bs.getD b (0, [])).2 →
          ((0 : w8), s) ∈ ((segBytesX g).getD b (0, [])).2 := by
        intro s hs'
        rw [segBytesX_getD_lt (by omega), List.getD_eq_getElem?_getD, hgb b,
          List.getElem?_eq_getElem hbl]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl, Option.getD_some] at hs'
        split
        · simp only [Option.map_some, Option.getD_some]; exact List.mem_append_left _ hs'
        · simp only [Option.getD_some]; exact hs'
      by_cases hx0 : SegExact g0
      · obtain ⟨s, hs'⟩ := tail_zero_cand ((habs.last g0 hg0).1 hx0) hZ hb1 hbl
        exact .inr ⟨s, hkeep s hs'⟩
      · rcases habs.winHead g0 hg0 hx0 b hb1 (Nat.lt_of_lt_of_le hbl segBytesX_length_le) with h | ⟨s, hs'⟩
        · exact .inl h
        · rw [segBytesX_getD_lt hbl] at hs'
          exact .inr ⟨s, hkeep s hs'⟩
    · exact .inl (by omega)
  · -- `WinZero`: the values unchanged
    simp only [tailLay] at hb
    rw [hgb b] at hx
    split at hx
    · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
      exact hzero b y hb hy
    · exact hzero b x hb hx
  · -- `WinLow`: the bytes written from `lo` to `wr`, the write's candidate added
    rw [hglo] at hlb
    simp only [tailLay] at hbw ⊢
    rw [hgrz]
    rw [hgb b] at hb
    split at hb
    · rename_i hr
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hb
      have hyW := habs.lowW g0 hg0 b y hy hbw (by unfold WinLo at hwlo; omega) (rz' := g0.om.rz)
        (fun _ h => h)
      obtain ⟨hdv, hbS⟩ := hdS b hr.1 hr.2
      refine ⟨hyW.1, fun q hq => ?_⟩
      rcases List.mem_append.1 hq with hq | hq
      · exact hyW.2 q hq
      · simp only [List.mem_singleton] at hq; subst hq
        exact .inr (.inr ⟨hbS, hdv, hn⟩)
    · exact habs.lowW g0 hg0 b x hb hbw (by unfold WinLo at hwlo; omega) (fun _ h => h)

end pure

end WalFs
end EtcdGrove
end Perennial

end
