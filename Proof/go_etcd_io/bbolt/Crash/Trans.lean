/- Lean-first (no Rocq counterpart).

# How a file state's crash candidates move with the operations (generic, for `Crash/Phases.lean`)

The states the crash-aware `os` specs ask about (`Spec/os/CrashSt.lean`): a write's attempts
(`WReach`: the attempt in flight, then its landing, `pwPostK`/`finBytes`), a growing truncate
(`TReach`), a sync (`csSynced`), a mapping. What a crash picks from (`crashCands`, `Crash/View.lean`)
only grows when an attempt lands (`cands_landed`: every candidate list the attempt in flight shows
is the landed state's), and a sync leaves each byte below the size its page-cache value
(`csSynced_bs`).
-/
module

public import Proof.go_etcd_io.bbolt.Crash.Dur
public import Spec.os.CrashSt

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

section trans
variable [GooseExts]

/-! ## A write's attempt -/

theorem pwPostK_size (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) :
    (pwPostK true m off data k n).size = pwSize m.size off k := rfl
theorem pwPostK_lo (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) :
    (pwPostK true m off data k n).lo = min m.lo (max m.size (off + data.length)) := rfl
theorem pwPostK_hi (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) :
    (pwPostK true m off data k n).hi = max m.hi (max m.size (off + data.length)) := rfl
theorem pwPostK_tc (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) :
    (pwPostK true m off data k n).tc = pwTail m off data n := rfl
theorem pwPostK_zf (m : OsMeta) (off : Nat) (data : List w8) (k n : Nat) :
    (pwPostK true m off data k n).zf =
      m.zf.map (fun z => if min off m.size < off + data.length then max z (off + data.length) else z) :=
  rfl

theorem cfMeta_lo (m : OsMeta) (off n : Nat) : (cfMeta m off n).lo = min m.lo (max m.size (off + n)) :=
  rfl
theorem cfMeta_hi (m : OsMeta) (off n : Nat) : (cfMeta m off n).hi = max m.hi (max m.size (off + n)) :=
  rfl

/-- The candidates of a byte in a write's range, as the write in flight shows them. -/
theorem crashCands_write (m : OsMeta) (bs : List ByteG) (fa fb t off : Nat) (data : List w8)
    (n b : Nat) :
    crashCands ⟨m, bs, fa, fb, .write t off data n⟩ b =
      if inRange (min off m.size) (off + data.length) b then
        (crashCands ⟨m, bs, fa, fb, .idle⟩ b).map
          (· ++ [(if off ≤ b then data.getD (b - off) 0 else 0, n)])
      else crashCands ⟨m, bs, fa, fb, .idle⟩ b := rfl

/-- The finished attempt's byte `b` (from `getElem?_tpd`). -/
theorem finBytes_getElem? {m : OsMeta} {bs : List ByteG} {off : Nat} {data : List w8} {k n : Nat}
    {zs : List Cands} (hl : bs.length = m.size) (hoff : off ≤ m.size) (b : Nat) :
    (finBytes m bs off data k n zs)[b]? =
      if b < off then bs[b]?
      else if b < off + (min (off + data.length) (pwSize m.size off k) - off) then
        (pwBytes m.size off data k n (cfRange m bs off data.length) zs)[b - off]?
      else bs[min (off + data.length) m.size +
        (b - off - (min (off + data.length) (pwSize m.size off k) - off))]? := by
  unfold finBytes
  rw [getElem?_tpd _ _ _ _ _ (by simp only [cfLo]; omega), pwBytes_length]
  simp only [cfLo, cfHi, Nat.min_eq_left hoff]

/-- A byte of the attempt's written part: its value, its candidates (the old ones, or for a byte
past the old size `zs`'s), with the data's byte stamped `n`. -/
theorem pwBytes_getElem?' (sz off : Nat) (data : List w8) (k n : Nat) (xs : List ByteG)
    (zs : List Cands) (j : Nat) (hj : j < min (off + data.length) (pwSize sz off k) - off) :
    (pwBytes sz off data k n xs zs)[j]? = some (pwByte off data k xs (off + j),
      (if j < xs.length then (xs.getD j (0, [])).2 else zs.getD (j - xs.length) []) ++
        [(data.getD j 0, n)]) := by
  unfold pwBytes
  rw [List.getElem?_map, List.getElem?_range hj]; rfl

theorem cfRange_length {m : OsMeta} {bs : List ByteG} {off n : Nat} (hl : bs.length = m.size)
    (hoff : off ≤ m.size) : (cfRange m bs off n).length = min (off + n) m.size - off := by
  simp only [cfRange, cfLo, cfHi, List.length_take, List.length_drop, Nat.min_eq_left hoff]; omega

theorem cfRange_getD {m : OsMeta} {bs : List ByteG} {off n j : Nat} (hl : bs.length = m.size)
    (hoff : off ≤ m.size) (hj : j < min (off + n) m.size - off) :
    (cfRange m bs off n).getD j (0, []) = bs[off + j]'(by omega) := by
  simp only [cfRange, cfLo, cfHi, Nat.min_eq_left hoff]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

/-- **A landed attempt shows every candidate list the attempt in flight showed.** -/
theorem cands_landed {m : OsMeta} {bs : List ByteG} {fa fb t off : Nat} {data : List w8} {k n : Nat}
    {zs : List Cands} (hl : bs.length = m.size) (hoff : off ≤ m.size) (hk : k ≤ data.length)
    (hzl : zs.length = pwSize m.size off k - m.size) (hz : ZsOk m zs) (b : Nat) (c : Cands)
    (hc : crashCands ⟨m, bs, fa, fb, .write t off data n⟩ b = some c) :
    crashCands ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩ b =
      some c := by
  have hS' : m.size ≤ pwSize m.size off k := by unfold pwSize; split <;> omega
  have hS2 : pwSize m.size off k ≤ max m.size (off + data.length) := by
    unfold pwSize; split <;> omega
  rw [crashCands_write] at hc
  show baseCands ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩ b = _
  unfold baseCands
  simp only [pwPostK_size]
  simp only [crashCands, baseCands] at hc
  have hmin : min off m.size = off := Nat.min_eq_left hoff
  rw [hmin] at hc
  by_cases hr : off ≤ b ∧ b < off + data.length
  · rw [if_pos (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hr.1, hr.2⟩),
      if_pos hr.1] at hc
    obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.1 hc
    by_cases hb' : b < pwSize m.size off k
    · rw [if_pos hb', finBytes_getElem? hl hoff, if_neg (by omega), if_pos (by omega),
        pwBytes_getElem?' _ _ _ _ _ _ _ _ (by omega)]
      simp only [Option.map_some]
      congr 1
      rw [cfRange_length hl hoff]
      by_cases hb : b < m.size
      · rw [if_pos hb] at hc0
        rw [if_pos (by omega), cfRange_getD hl hoff (by omega)]
        simp only [show off + (b - off) = b by omega]
        rw [List.getElem?_eq_getElem (by omega)] at hc0
        simp only [Option.map_some, Option.some.injEq] at hc0
        rw [hc0]
      · rw [if_neg hb] at hc0
        rw [if_neg (by omega)]
        have := hz (b - m.size) c0 (by rw [show m.size + (b - m.size) = b by omega]; exact hc0)
          (by omega)
        rw [List.getD_eq_getElem?_getD, show b - off - (min (off + data.length) m.size - off) =
          b - m.size by omega, this]
        rfl
    · rw [if_neg hb']
      have hb : ¬ b < m.size := by omega
      rw [if_neg hb] at hc0
      unfold OsMeta.pc
      rw [pwPostK_tc, pwTail_lookup, if_pos (by simp only [inRange, Bool.and_eq_true,
        decide_eq_true_eq]; exact ⟨hr.1, hr.2⟩), if_pos (by omega), hc0]
      rfl
  · rw [if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)] at hc
    by_cases hb : b < m.size
    · rw [if_pos hb] at hc
      rw [if_pos (by omega), finBytes_getElem? hl hoff]
      by_cases hbo : b < off
      · rw [if_pos hbo]; exact hc
      · rw [if_neg hbo, if_neg (by omega)]
        rw [show min (off + data.length) m.size + (b - off - (min (off + data.length)
          (pwSize m.size off k) - off)) = b by omega]
        exact hc
    · rw [if_neg hb] at hc
      rw [if_neg (by omega)]
      unfold OsMeta.pc at hc ⊢
      rw [pwPostK_tc, pwTail_lookup, if_neg (by simp only [inRange, Bool.and_eq_true,
        decide_eq_true_eq]; omega), pwPostK_zf]
      revert hc
      cases m.tc !! b with
      | some c' => exact id
      | none =>
        dsimp only
        cases m.zf with
        | none => intro h; cases h
        | some z =>
          dsimp only; simp only [Option.map_some]
          intro h
          split at h
          · rw [if_pos (by split <;> omega)]; exact h
          · cases h

/-- **The bytes a landed attempt left outside its range.** -/
theorem finBytes_out {m : OsMeta} {bs : List ByteG} {off : Nat} {data : List w8} {k n : Nat}
    {zs : List Cands} (hl : bs.length = m.size) (hoff : off ≤ m.size) (hk : k ≤ data.length)
    (b : Nat) (hb : b < off ∨ off + data.length ≤ b) (hbs : b < m.size) :
    (finBytes m bs off data k n zs)[b]? = bs[b]? := by
  have hS' : m.size ≤ pwSize m.size off k := by unfold pwSize; split <;> omega
  rw [finBytes_getElem? hl hoff]
  rcases hb with hb | hb
  · rw [if_pos hb]
  · rw [if_neg (by omega), if_neg (by omega)]
    congr 1; omega

/-- **The page-cache values of a landed attempt**: the data's, or the old ones. -/
theorem finBytes_val {m : OsMeta} {bs : List ByteG} {off : Nat} {data : List w8} {k n : Nat}
    {zs : List Cands} (hl : bs.length = m.size) (hoff : off ≤ m.size) (hk : k ≤ data.length)
    (b : Nat) (x : ByteG) (hx : (finBytes m bs off data k n zs)[b]? = some x) :
    (∃ y, bs[b]? = some y ∧ x.1 = y.1) ∨ (off ≤ b ∧ x.1 = data.getD (b - off) 0) ∨ x.1 = 0 := by
  rw [finBytes_getElem? hl hoff] at hx
  split at hx
  · exact .inl ⟨x, hx, rfl⟩
  · split at hx
    · rw [pwBytes_getElem?' _ _ _ _ _ _ _ _ (by omega)] at hx
      simp only [Option.some.injEq] at hx
      subst hx
      unfold pwByte
      split
      · exact .inr (.inl ⟨by omega, by simp only [show off + (b - off) - off = b - off by omega]⟩)
      · by_cases hj : b - off < (cfRange m bs off data.length).length
        · left
          rw [cfRange_length hl hoff] at hj
          rw [show off + (b - off) - off = b - off by omega, cfRange_getD hl hoff hj]
          exact ⟨_, List.getElem?_eq_getElem (by omega), by simp only [show off + (b - off) = b by omega]⟩
        · right; right
          have hnone : (cfRange m bs off data.length).getD (b - off) (0, []) = (0, []) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
          rw [show off + (b - off) - off = b - off by omega, hnone]
    · exact .inl ⟨x, hx, rfl⟩

/-! ## A sync -/

theorem csSynced_bs (m : OsMeta) (H F T : List ByteG) (fa fb : Nat)
    (hF : ∀ y ∈ F, y = durB y.1) (b : Nat) :
    (csSynced m H F T fa fb).bs[b]? = ((H ++ (F ++ T))[b]?).map (fun x => durB x.1) := by
  simp only [csSynced]
  have hFm : F.map (fun x => durB x.1) = F := by
    have : F.map (fun x => durB x.1) = F.map id :=
      List.map_congr_left (fun y hy => (hF y hy).symm)
    rw [this, List.map_id]
  have e : H.map (fun x => durB x.1) ++ (F ++ T.map (fun x => durB x.1)) =
      (H ++ (F ++ T)).map (fun x => durB x.1) := by
    simp only [List.map_append, hFm]
  rw [e, List.getElem?_map]

end trans

end bbolt
end EtcdGrove
end Perennial
